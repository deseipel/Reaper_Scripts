--[[
  Real-time RS5K -> MP4 Video Sampler (v7.2 - Fixed Rate Drum Trigger)
  Plays MP4/MKV/MOV video items in sync with RS5K sample playback.
--]]

--------------------------------------------------------------------------------
-- CONFIG
--------------------------------------------------------------------------------
local VIDEO_TRACK_NAME       = "RS5K_Video_Output"
local PITCH_BEND_RANGE_ST    = 6  -- semitones

-- RS5K parameter indexes
local IDX_NOTE_START         = 3
local IDX_NOTE_END           = 4
local IDX_START_OFFSET       = 13
local IDX_LENGTH             = 14
local IDX_OBEY_NOTE_OFFS     = 11
local IDX_PITCH_OFFSET       = 5  -- NEW: Param 5 is Pitch@start

--------------------------------------------------------------------------------
-- STATE
--------------------------------------------------------------------------------
local active_voices          = {}     
local g_voice_count          = 0
local g_last_seq             = 0
local g_is_first_run         = true
local g_bend_semitones       = 0.0
local g_last_pitch_bucket    = -1
local g_last_played = { chan = nil, note = nil }
local g_mod_wheel_val        = 0.0    
local g_base_offsets         = {}     -- NEW: Remembers your manual RS5K start tweaks
local g_last_forced_offset   = {}     -- NEW: The "fingerprint" of the last script override

-- Transport
local g_transport_owned      = false  
local g_initial_cursor_pos   = 0
local g_pending_play         = false  

-- Debug log
local g_log                  = {}
local LOG_MAX                = 30
local g_log_frozen           = false

-- UI display values
local UI_FILE  = "None"
local UI_NOTE  = "None"
local UI_RATE  = "1.00x"

--------------------------------------------------------------------------------
-- DEBUG LOG & UI
--------------------------------------------------------------------------------
local function log(msg)
  if g_log_frozen then return end
  table.insert(g_log, 1, string.format("[%.3f] %s", reaper.time_precise(), msg))
  if #g_log > LOG_MAX then table.remove(g_log) end
end

local function init_ui()
  gfx.init("RS5K Video Linker v7.2", 700, 370, 0, 100, 100)
  gfx.setfont(1, "Arial", 14)
end

local function draw_ui()
  gfx.set(0.1, 0.1, 0.1, 1)
  gfx.rect(0, 0, gfx.w, gfx.h, 1)

  gfx.x, gfx.y = 10, 10
  gfx.set(0.8, 0.8, 0.8, 1)
  gfx.drawstr("RS5K Video Linker v7.2 (Fixed Rate)")

  gfx.x, gfx.y = 10, 35
  -- PlayState 4 is the bitmask for "Recording"
  local is_recording = (reaper.GetPlayState() & 4) == 4 

  if is_recording then
    gfx.set(1.0, 0.2, 0.2, 1) -- Bright Red
    gfx.drawstr("STATUS: RECORDING (Video items will be kept)")
  else
    gfx.set(0.2, 0.8, 1.0, 1) -- Cyan
    gfx.drawstr("STATUS: JAM MODE (Video items auto-deleted)")
  end

  gfx.set(1, 1, 1, 1)
  gfx.x, gfx.y = 10, 60
  gfx.drawstr("Note: " .. UI_NOTE .. "   Rate: " .. UI_RATE)
  gfx.x, gfx.y = 10, 80
  gfx.set(0.5, 0.5, 1, 1)
  gfx.drawstr("File: " .. UI_FILE)

  if g_log_frozen then
    gfx.set(1, 0, 0, 1)
    gfx.x, gfx.y = 10, 100
    gfx.drawstr("LOG FROZEN (press R to unfreeze)")
  end
  gfx.set(1, 1, 0, 1)
  local y = g_log_frozen and 120 or 105
  for i = 1, math.min(#g_log, 16) do
    gfx.x, gfx.y = 10, y
    gfx.drawstr(g_log[i])
    y = y + 16
  end
  gfx.update()
end

--------------------------------------------------------------------------------
-- HELPERS 
--------------------------------------------------------------------------------
local function is_rs5k(track, fx)
  local ok, param_name = reaper.TrackFX_GetParamName(track, fx, IDX_START_OFFSET, "")
  if ok and param_name:lower():find("start offset") then
    return true
  end
  return false
end

local function get_rs5k_midi_channel(tr, fx)
  local num_params = reaper.TrackFX_GetNumParams(tr, fx)
  for i = 0, num_params - 1 do
    local ok, name = reaper.TrackFX_GetParamName(tr, fx, i, "")
    if ok and name:lower():find("midi chan") then
      local _, str_val = reaper.TrackFX_GetFormattedParamValue(tr, fx, i, "")
      local parsed = str_val:match("%d+")
      return parsed and tonumber(parsed) or 0
    end
  end
  return 0
end

local function get_or_create_video_track()
  for i = 0, reaper.CountTracks(0) - 1 do
    local tr = reaper.GetTrack(0, i)
    local _, name = reaper.GetTrackName(tr, "")
    if name == VIDEO_TRACK_NAME then return tr end
  end
  reaper.InsertTrackAtIndex(reaper.CountTracks(0), true)
  local tr = reaper.GetTrack(0, reaper.CountTracks(0) - 1)
  reaper.GetSetMediaTrackInfo_String(tr, "P_NAME", VIDEO_TRACK_NAME, true)
  return tr
end

local function get_sample_path(track, fx)
  for _, key in ipairs({"FILE", "FILE0", "FILE1"}) do
    local ok, val = reaper.TrackFX_GetNamedConfigParm(track, fx, key)
    if ok and val and val ~= "" and (val:lower():find("%.mp4") or val:lower():find("%.mkv") or val:lower():find("%.mov")) then
      local clean = val:gsub('\0', ''):gsub('%s+$', '')
      UI_FILE = clean:match("[/\\]([^/\\]+)$") or clean
      return clean
    end
  end
  return nil
end

local function get_rs5k_params(track, fx)
  local start_norm = reaper.TrackFX_GetParamNormalized(track, fx, IDX_START_OFFSET)
  local len_norm   = reaper.TrackFX_GetParamNormalized(track, fx, IDX_LENGTH)
  local obey_raw   = reaper.TrackFX_GetParam(track, fx, IDX_OBEY_NOTE_OFFS, 0, 0)
  return start_norm, len_norm, obey_raw >= 0.5
end

--------------------------------------------------------------------------------
-- SPAWN VIDEO ITEM
--------------------------------------------------------------------------------
local function spawn_video(path, start_norm, len_norm, note, channel, place_pos,root_note)
  if not path or path == "" then return nil end

  local src = reaper.PCM_Source_CreateFromFile(path)
  if not src then return nil end

  local full_len   = reaper.GetMediaSourceLength(src)
  local start_time = start_norm * full_len
  local end_time   = len_norm   * full_len
  local dur        = math.max(end_time - start_time, 0.05)
  
  -- NEW: Bring back the melodic pitch math!
  local semitone_diff = (note - root_note) + g_bend_semitones
  local rate = 2 ^ (semitone_diff / 12)

  -- The Fix: Lock base rate to 1.0, only modify via pitch bend wheel
  local rate = 2 ^ (g_bend_semitones / 12)

  UI_NOTE = string.format("CH %d | Note %d", channel, note)
  UI_RATE = string.format("%.2fx", rate)

  local tr   = get_or_create_video_track()
  local item = reaper.AddMediaItemToTrack(tr)
  local take = reaper.AddTakeToMediaItem(item)
  reaper.SetMediaItemTake_Source(take, src)
  reaper.SetMediaItemTakeInfo_Value(take, "D_VOL", 0)

  reaper.SetMediaItemInfo_Value(item,     "D_POSITION",  place_pos)
  reaper.SetMediaItemTakeInfo_Value(take, "D_STARTOFFS", start_time)
  reaper.SetMediaItemTakeInfo_Value(take, "D_PLAYRATE",  rate)
  reaper.SetMediaItemInfo_Value(item,     "D_LENGTH",    dur / rate)

  reaper.UpdateArrange()
  return item, take, start_time, dur
end

--------------------------------------------------------------------------------
-- VOICE MANAGEMENT
--------------------------------------------------------------------------------
local function trim_and_remove_voice(voice_key)
  local info = active_voices[voice_key]
  if not info then return end

  local is_recording = (reaper.GetPlayState() & 4) == 4

  if info.item and reaper.ValidatePtr2(0, info.item, "MediaItem*") then
    
    if not is_recording then
      -- JAM MODE: Vaporize the item completely to keep the timeline clean
      local tr = reaper.GetMediaItemTrack(info.item)
      if tr then
        reaper.DeleteTrackMediaItem(tr, info.item)
        log("JAM MODE: Auto-deleted video item.")
      end
      
    else
      -- RECORDING MODE: Trim it to match the exact length of the held note
      local now = reaper.GetPlayState() > 0 and reaper.GetPlayPosition() or reaper.GetCursorPosition()
      local new_dur = now - info.start_time
      local max_dur = reaper.GetMediaItemInfo_Value(info.item, "D_LENGTH")
      if new_dur > 0 and new_dur < max_dur then
        reaper.SetMediaItemInfo_Value(info.item, "D_LENGTH", new_dur)
      end
    end
    
  end

  active_voices[voice_key] = nil
  g_voice_count = g_voice_count - 1
end

local function stop_transport_if_owned()
  if g_transport_owned then
    reaper.Main_OnCommand(1016, 0)
    reaper.SetEditCurPos(g_initial_cursor_pos, true, false)
    g_transport_owned = false
  end
end

--------------------------------------------------------------------------------
-- MIDI HANDLERS
--------------------------------------------------------------------------------
local function handle_note_on(channel, note)
  g_last_played.chan = channel
  g_last_played.note = note
  local voice_key = channel .. "_" .. note

  if active_voices[voice_key] then
    trim_and_remove_voice(voice_key)
  end

  for t = 0, reaper.CountTracks(0) - 1 do
    local tr = reaper.GetTrack(0, t)
    for fx = 0, reaper.TrackFX_GetCount(tr) - 1 do
      
      if is_rs5k(tr, fx) then
        local rs5k_chan = get_rs5k_midi_channel(tr, fx)
        
        if rs5k_chan == 0 or rs5k_chan == channel then
          local n_start = math.floor(reaper.TrackFX_GetParam(tr, fx, IDX_NOTE_START, 0, 0) * 127 + 0.5)
          local n_end   = math.floor(reaper.TrackFX_GetParam(tr, fx, IDX_NOTE_END,   0, 0) * 127 + 0.5)

   if note >= n_start and note <= n_end then
            local path = get_sample_path(tr, fx)
            if path then
            -- 1. Read the current live knobs from the RS5K UI
              local fx_guid = reaper.TrackFX_GetFXGUID(tr, fx)
              local current_ui_offset = reaper.TrackFX_GetParamNormalized(tr, fx, IDX_START_OFFSET)
              local len_norm = reaper.TrackFX_GetParamNormalized(tr, fx, IDX_LENGTH)

              -- NEW: Calculate the effective root note for melodic pitching
              local note_start_norm = reaper.TrackFX_GetParam(tr, fx, IDX_NOTE_START, 0, 0)
              local note_start = math.floor(note_start_norm * 127 + 0.5)
              local _, pitch_offset_str = reaper.TrackFX_GetFormattedParamValue(tr, fx, IDX_PITCH_OFFSET, "")
              local pitch_start_offset = tonumber((pitch_offset_str or "0"):match("(-?[0-9]+)")) or 0
              local root_note = note_start - pitch_start_offset

              -- 2. Detect if YOU manually tweaked the knob since the last pad hit
              if g_last_forced_offset[fx_guid] and math.abs(current_ui_offset - g_last_forced_offset[fx_guid]) < 0.001 then
                current_ui_offset = g_base_offsets[fx_guid] or current_ui_offset
              else
                g_base_offsets[fx_guid] = current_ui_offset
              end

              -- 3. Calculate the Stutter Target
              local target_offset = current_ui_offset
              if g_mod_wheel_val > 0.01 then
                target_offset = current_ui_offset + (g_mod_wheel_val * (len_norm * 0.95))
                if target_offset > 1.0 then target_offset = 1.0 end
              end

              -- 4. Instantly push the correct start time to the audio plugin
              reaper.TrackFX_SetParamNormalized(tr, fx, IDX_START_OFFSET, target_offset)
              g_last_forced_offset[fx_guid] = target_offset

              local obey_raw = reaper.TrackFX_GetParam(tr, fx, IDX_OBEY_NOTE_OFFS, 0, 0)
              local obey_note_offs = (obey_raw >= 0.5)

              local place_pos
              if reaper.GetPlayState() == 0 then
                place_pos = reaper.GetCursorPosition()
              else
                place_pos = reaper.GetPlayPosition()
              end

              -- 5. Spawn the video passing the 'root_note'
              local item, take, start_time, dur = spawn_video(path, target_offset, len_norm, note, channel, place_pos, root_note)

              if item then
                active_voices[voice_key] = {
                  item           = item,
                  take           = take,
                  start_time     = place_pos,
                  obey_note_offs = obey_note_offs,
                  base_start_offs= target_offset,  -- For DJ Stutter
                  slice_dur      = dur,            -- For DJ Stutter
                  root_note      = root_note,      -- NEW: For live Pitch Bend
                  incoming_note  = note            -- NEW: For live Pitch Bend
                }
                g_voice_count = g_voice_count + 1
              end


              end
            end
          end
        end
      end
    end
  end


local function handle_note_off(channel, note)
  local voice_key = channel .. "_" .. note
  local info      = active_voices[voice_key]

  if not info then return end

  if not info.obey_note_offs then
    return
  end

  trim_and_remove_voice(voice_key)

  if g_voice_count <= 0 then
    g_voice_count = 0
    stop_transport_if_owned()
  end
  reaper.UpdateArrange()
end

local function handle_bend(val)
  local bucket = math.floor(val / 64)
  if bucket == g_last_pitch_bucket then return end
  g_last_pitch_bucket = bucket
  g_bend_semitones = ((val - 8192) / 8191) * PITCH_BEND_RANGE_ST
end


local function handle_mod_wheel(val)
  local norm = val / 127.0
  for key, info in pairs(active_voices) do
    if reaper.ValidatePtr2(0, info.item, "MediaItem*") and reaper.ValidatePtr2(0, info.take, "MediaItem_Take*") then
      
      -- 1. How long has this note been playing?
      local now = reaper.GetPlayState() > 0 and reaper.GetPlayPosition() or reaper.GetCursorPosition()
      local elapsed = now - info.start_time
      
      -- 2. Where should the playhead be based on the Mod Wheel? (0.0 to 1.0)
      local target_media_pos = info.base_start_offs + (norm * info.slice_dur)
      
      -- 3. Shift the underlying video so the target position perfectly aligns with 'now'
      local new_take_offs = target_media_pos - elapsed
      
      reaper.SetMediaItemTakeInfo_Value(info.take, "D_STARTOFFS", new_take_offs)
      reaper.UpdateItemInProject(info.item)
      
      log(string.format("Scrub: %.1f%%", norm * 100))
    end
  end
end

--------------------------------------------------------------------------------
-- MAIN LOOP
--------------------------------------------------------------------------------
local function main()
  local char = gfx.getchar()
  if char < 0 then return end 

  if char == string.byte('r') or char == string.byte('R') then
    g_log_frozen = false
  end

  draw_ui()

  if g_is_first_run then
    g_last_seq   = reaper.MIDI_GetRecentInputEvent(0)
    g_is_first_run = false
    reaper.defer(main)
    return
  end

  local idx     = 0
  local new_seq = 0
  local did_act = false

  while true do
    local seq, m = reaper.MIDI_GetRecentInputEvent(idx)
    if seq <= 0 or seq <= g_last_seq then break end

    if new_seq == 0 then new_seq = seq end

    if m and #m >= 1 then
      local b1      = string.byte(m, 1) or 0
      local b2      = string.byte(m, 2) or 0
      local b3      = string.byte(m, 3) or 0
      local status  = b1 & 0xF0
      local channel = (b1 & 0x0F) + 1

      if     status == 0x90 and b3 > 0 then
        handle_note_on(channel, b2)
      elseif status == 0x80 or (status == 0x90 and b3 == 0) then
        handle_note_off(channel, b2)
      elseif status == 0xE0 then
        handle_bend((b3 * 128) + b2)
	  elseif status == 0xB0 and b2 == 1 then  -- NEW: Listen for Mod Wheel (CC 1)
        g_mod_wheel_val = b3 / 127.0          -- Convert 0-127 MIDI to a 0.0-1.0 percentage
      end
      did_act = true
    end
    idx = idx + 1
  end

  if new_seq > 0 then g_last_seq = new_seq end

  if g_pending_play then
    g_pending_play = false
    reaper.Main_OnCommand(1007, 0)
  end

 for key, info in pairs(active_voices) do
    if reaper.ValidatePtr2(0, info.take, "MediaItem_Take*") then
      -- Re-calculate with melodic math so the pitch wheel bends the already-pitched video
      local semitone_diff = (info.incoming_note - info.root_note) + g_bend_semitones
      local rate = 2 ^ (semitone_diff / 12)
      reaper.SetMediaItemTakeInfo_Value(info.take, "D_PLAYRATE", rate)
    end
  end

  if did_act then reaper.UpdateArrange() end
  reaper.defer(main)
end

init_ui()
main()
