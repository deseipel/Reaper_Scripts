--[[
Real-time RS5K → MP4 Video Sampler (v2.0 - Queue-Based)
Author: Reaper DAW Ultimate Assistant
Version: 2.0 (Uses MIDI Queue)

Purpose:
  - Listens for MIDI events via the REAPER event queue (lossless).
  - Triggers different RS5K instances based on MIDI note ranges.
  - Handles Note-On, Note-Off, Pitch Bend, and Mod Wheel.
--]]

--------------------------------------------------
-- 🔧 CONFIG
--------------------------------------------------
local VIDEO_TRACK_NAME = "RS5K_Video_Output"
local MIDI_DEVICE_ID = 0 -- 0 = all MIDI inputs
local DEBUG = true

-- RS5K Parameter Indexes
local NOTE_START_PARAM_IDX = 3 -- RS5K "Note start"
local NOTE_END_PARAM_IDX   = 4 -- RS5K "Note end"
local PITCH_ROOT_NOTE_IDX = 5 -- RS5K "Pitch@start (note)"
local START_OFFSET_PARAM_IDX = 13 -- RS5K "Sample start offset"
local LENGTH_PARAM_IDX = 14 -- RS5K "Sample length"

-- Pitch Bend Config
local PITCH_BEND_RANGE_SEMITONES = 6 -- +/- 6 semitones

--------------------------------------------------
-- 🧩 Internal Caches
--------------------------------------------------
local source_cache = {}     -- [filepath] = PCM_Source
local spawned_items = {}    -- [item] = end time for cleanup
local note_to_item = {} -- [note] = { item, take, root_note, incoming_note }

-- Reset all variables on startup.
local last_processed_event_seq = 0
local last_pitch_bucket = -1
local g_current_bend_semitones = 0.0
--------------------------------------------------
-- 🧠 Utility Functions
--------------------------------------------------
local function msg(text)
  if DEBUG then reaper.ShowConsoleMsg(tostring(text).."\n") end
end

-- Base64 utility table
local B64 = {
    _ = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/",
    d = {}
}
for i = 1, #B64._ do
    B64.d[B64._:sub(i, i)] = i - 1
end

-- Function to decode a Base64 string
local function base64_decode(str)
    str = str:gsub("[^"..B64._.."=]", "")
    local mod = #str % 4
    if mod == 2 then str = str .. "==" end
    if mod == 3 then str = str .. "=" end
    
    local bytes = {}
    for i = 1, #str, 4 do
        local b1 = B64.d[str:sub(i, i)]
        local b2 = B64.d[str:sub(i+1, i+1)]
        local b3 = B64.d[str:sub(i+2, i+2)]
        local b4 = B64.d[str:sub(i+3, i+3)]
        
        if b1 then bytes[#bytes+1] = string.char(b1*4 + math.floor(b2/16)) end
        if b2 and str:sub(i+2, i+2) ~= "=" then bytes[#bytes+1] = string.char((b2%16)*16 + math.floor(b3/4)) end
        if b3 and str:sub(i+3, i+3) ~= "=" then bytes[#bytes+1] = string.char((b3%4)*64 + b4) end
    end
    return table.concat(bytes)
end

-- Parses REAPER note strings (e.g., "A4", "C#3", "Gb-1") into MIDI note numbers
local function ParseNoteString(note_str)
  local note_map = { c = 0, d = 2, e = 4, f = 5, g = 7, a = 9, b = 11 }
  
  -- Try to match the note string
  local note_char, accidental, octave = note_str:match("([A-Ga-g])([#b]?)(-?[0-9]+)")
  
  if not note_char then
    msg("Error parsing note string: " .. note_str .. ". Defaulting to A4 (69).")
    return 69 -- Default to A4 if parsing fails
  end
  
  local note_val = note_map[note_char:lower()]
  
  if accidental == "#" then
    note_val = note_val + 1
  elseif accidental == "b" then
    note_val = note_val - 1
  end
  
  local octave_val = tonumber(octave)
  
  -- Calculate MIDI note number (MIDI standard C-1=0, A4=69)
  local midi_note = note_val + (octave_val + 1) * 12
  
  return midi_note
end


local function get_or_create_video_track()
  for i = 0, reaper.CountTracks(0)-1 do
    local tr = reaper.GetTrack(0, i)
    local _, name = reaper.GetTrackName(tr, "")
    if name == VIDEO_TRACK_NAME then return tr end
  end
  reaper.InsertTrackAtIndex(reaper.CountTracks(0), true)
  local tr = reaper.GetTrack(0, reaper.CountTracks(0)-1)
  reaper.GetSetMediaTrackInfo_String(tr, "P_NAME", VIDEO_TRACK_NAME, true)
  reaper.SetMediaTrackInfo_Value(tr, "I_RECMON", 0)
  return tr
end
 --[[
local function find_rs5k_fx(track)
  local fx_count = reaper.TrackFX_GetCount(track)
  local rs5k_prefix = "(rs5k)" -- Custom prefix check
  local internal_name = "reasamplomatic5000" -- Fallback check

  for fx = 0, fx_count - 1 do
    local retval, name = reaper.TrackFX_GetFXName(track, fx, "")
    
    if retval and name then
      local lower_name = name:lower()
      
      -- Check 1: Match the custom prefix (e.g., (RS5K)Sample.mp4)
      if lower_name:find(rs5k_prefix) then 
        return fx 
      end
      
      -- Check 2: Fallback to the internal plugin name 
      if lower_name:find(internal_name) then
        return fx
      end
    end
  end
  
  return nil
end
--]]

local function get_sample_path(track, fx)
  
  -- 1. Try standard named parameters first (for general compatibility)
  for _, key in ipairs({"FILE", "FILE0", "FILE1"}) do
    local ok, val = reaper.TrackFX_GetNamedConfigParm(track, fx, key)
    if ok and val and val ~= "" and val:lower():find(".mp4") then 
      -- Clean up the string just in case the API call didn't fully clean it
      val = val:gsub('\0', ''):gsub('%s+$', '')
      return val 
    end
  end

  -- 2. Fallback: Manually read the state chunk for the Base64 file string (for VST state)
  local ok, chunk = reaper.GetTrackStateChunk(track, "", false)
  if ok and chunk then
    
    -- Pattern to target the VST block and specifically capture the Base64 line that starts with 'QzpcV' (C:\...)
    local rs5k_block, b64_path_line = chunk:match(
      '<VST "VSTi: ReaSamplOmatic5000 (Cockos)".-\n' .. 
      '.-[\r\n]' .. -- Skip first Base64 line
      '(QzpcV.-)[\r\n]' -- Capture second Base64 line
    ) 

    if b64_path_line then
      -- Remove potential trailing garbage before decoding
      b64_path_line = b64_path_line:match("^%S+") 

      local decoded_data = base64_decode(b64_path_line)

      -- Extract the path: C:\... ending in .mp4
      local path = decoded_data:match("(C:\\.-%.mp4)") 

      if path then
        -- Clean up null bytes and trailing whitespace from the decoded string
        path = path:gsub('\0', ''):gsub('%s+$', '')
        msg("Path found via Base64 decode: " .. path)
        return path
      end
    end
  end

  return nil
end


local function get_pcm_source(path)
  if source_cache[path] then 
    msg("Cache hit for: " .. path)
    return source_cache[path] 
  end
  
  -- Step 1: Print the path being used
  msg("Attempting to load PCM_Source from path: [" .. path .. "]")
  
  -- Ensure only standard Windows directory separators are used (optional safety)
  local clean_path = path:gsub("/", "\\")
  
  -- Step 2: Attempt to create the source
  local src = reaper.PCM_Source_CreateFromFile(clean_path)
  
  -- Step 3: Check the result and report
  if src then
    msg("SUCCESS: PCM_Source created.")
    source_cache[path] = src
    return src
  else
    msg("FAILURE: reaper.PCM_Source_CreateFromFile failed for path: [" .. clean_path .. "]")
    -- Return nil so the calling function can exit gracefully
    return nil 
  end
end

local function get_rs5k_params(track, fx)

  -- 1. Get Start/Length (Params 13, 14)
  local _, start_str = reaper.TrackFX_GetFormattedParamValue(track, fx, START_OFFSET_PARAM_IDX, "")
  local _, length_str = reaper.TrackFX_GetFormattedParamValue(track, fx, LENGTH_PARAM_IDX, "")
  local start_offset_norm = tonumber(start_str)
  local length_norm = tonumber(length_str)

  -- 2. Get Note Start (Param 3)
  -- This is our "trigger anchor"
  local note_start_norm = reaper.TrackFX_GetParam(track, fx, NOTE_START_PARAM_IDX, 0, 0)
  local note_start = math.floor(note_start_norm * 127 + 0.5)

  -- 3. Get Pitch@start Offset (Param 5)
  local _, pitch_offset_str = reaper.TrackFX_GetFormattedParamValue(track, fx, PITCH_ROOT_NOTE_IDX, "")
  
  -- *** NEW SAFETY CHECK ***
  -- If the string is nil, default it to "0" to prevent a crash.
  if not pitch_offset_str then pitch_offset_str = "0" end

  -- 4. Extract the number from the string (e.g., "-6")
  local pitch_start_offset = tonumber(pitch_offset_str:match("(-?[0-9]+)")) or 0

  -- 5. Calculate the TRUE Root Note (Your Logic)
  -- 60 - (-6) = 66
  local root_note = note_start - pitch_start_offset
  
  -- Apply safety clamps
  start_offset_norm = math.max(0, math.min(1, start_offset_norm or 0))
  length_norm = math.max(0, math.min(1, length_norm or 1))

  -- Calculate the *actual* End Offset
  local end_offset_norm = start_offset_norm + (1 - start_offset_norm) * length_norm

  -- Debug Print
  msg("DEBUG PARAMS (NEW LOGIC):")
  msg("  Start Offset (Param 13): " .. string.format("%.3f", start_offset_norm))
  msg("  Length (Param 14): " .. string.format("%.3f", length_norm))
  msg("  Note Start (Param 3): " .. note_start)
  msg("  Pitch Offset (Param 5): " .. pitch_start_offset .. " semitones (from string '" .. pitch_offset_str .. "')")
  msg("  EFFECTIVE Root Note: " .. root_note .. " (NoteStart - Offset)")
  msg("  CALCULATED End Offset: " .. string.format("%.3f", end_offset_norm))

  -- Sanity Check
  if end_offset_norm <= start_offset_norm then
      msg("WARNING: RS5K sample range is zero/negative. Forcing Start=0.0, End=1.0.")
      start_offset_norm = 0.0
      end_offset_norm = 1.0
  end

  -- Return the start/end offsets and the calculated root note
  return start_offset_norm, end_offset_norm, root_note
end

--------------------------------------------------
-- 🎞️ Video Spawning / Removal
--------------------------------------------------
-- NEW SIGNATURE: a_pitch_norm is replaced with incoming_note and root_note
local function spawn_video(path, start_norm, end_offset_norm, incoming_note, root_note)
  if not path or path == "" then return end

  -- Create the media source
  local src = reaper.PCM_Source_CreateFromFile(path)
  if not src then
    reaper.ShowConsoleMsg("❌ Could not load media source: " .. path .. "\n")
    return
  end

  -- Get the full source length (audio or video)
  local full_src_length = reaper.GetMediaSourceLength(src)
  if not full_src_length or full_src_length <= 0 then
    reaper.ShowConsoleMsg("⚠️ Invalid media length for " .. path .. "\n")
    return
  end

  -- Convert RS5K's normalized offsets (0–1) to seconds
  local start_time = start_norm * full_src_length
  local end_time   = end_offset_norm * full_src_length
  local duration   = end_time - start_time
  if duration <= 0 then duration = 0.05 end

  -- *** NEW PLAYRATE CALCULATION ***
-- Calculate semitone difference, NOW including the current pitch bend
  local semitone_diff = (incoming_note - root_note) + g_current_bend_semitones
  -- Calculate rate: 2^(semitones / 12)
  local playrate = 2 ^ (semitone_diff / 12)

  -- Make or find the "Video" track
  local video_tr = get_or_create_video_track()
  local item = reaper.AddMediaItemToTrack(video_tr)
  local take = reaper.AddTakeToMediaItem(item)
  reaper.SetMediaItemTake_Source(take, src)

  -- Set the take's audio volume to 0 (-inf dB)
  reaper.SetMediaItemTakeInfo_Value(take, "D_VOL", 0)

  -- Place at current play position
  local play_pos = reaper.GetPlayPosition()
  reaper.SetMediaItemInfo_Value(item, "D_POSITION", play_pos)

  -- Apply RS5K slice and the NEWLY CALCULATED rate
  reaper.SetMediaItemTakeInfo_Value(take, "D_STARTOFFS", start_time)
  reaper.SetMediaItemTakeInfo_Value(take, "D_PLAYRATE", playrate)
  reaper.SetMediaItemInfo_Value(item, "D_LENGTH", duration / playrate)

  reaper.UpdateArrange()

  reaper.ShowConsoleMsg(string.format(
    "🎞 Spawned video: %s\n  Start: %.3fs  Dur: %.3fs  Rate: %.3fx\n",
    path, start_time, duration, playrate))
    
  return item, take
end




local function remove_video_item(item)
  if not reaper.ValidatePtr2(0, item, "MediaItem*") then return end
  local tr = get_or_create_video_track()
  reaper.DeleteTrackMediaItem(tr, item)
  reaper.UpdateArrange()
end

--------------------------------------------------
-- 🎹 MIDI Input Handling
--------------------------------------------------
local function handle_note_on(note)
  msg("--- handle_note_on triggered. Note: " .. note)

  if note_to_item[note] then 
    msg("Note " .. note .. " is already on. Aborting.")
    return 
  end

  -- Loop ALL tracks
  for t = 0, reaper.CountTracks(0) - 1 do
    local track = reaper.GetTrack(0, t)
    
    -- Loop ALL FX on this track
    for fx = 0, reaper.TrackFX_GetCount(track) - 1 do
    
      -- Check if this specific FX is an RS5k
      local retval, name = reaper.TrackFX_GetFXName(track, fx, "")
      
      -- A simple check for the plugin name
      if retval and name and (name:find("ReaSamplOmatic5000") or name:lower():find("(rs5k)")) then
        msg("Found RS5k on track " .. t .. ", FX slot " .. fx)
        
        -- Get this RS5k's note range
        local note_start = math.floor(reaper.TrackFX_GetParam(track, fx, NOTE_START_PARAM_IDX, 0, 0) * 127 + 0.5)
        local note_end = math.floor(reaper.TrackFX_GetParam(track, fx, NOTE_END_PARAM_IDX, 0, 0) * 127 + 0.5)
        
        msg("Checking note range... Script read: " .. note_start .. " to " .. note_end)

        -- Check if the note we played is within this plugin's range
        if note >= note_start and note <= note_end then
          msg("Note " .. note .. " is IN RANGE.")
          
          local path = get_sample_path(track, fx) -- Pass the correct 'fx' index
          msg("Checking path... Path found: " .. (path or "nil"))
          
          if path and path:lower():find(".mp4") then
            msg("Path is a valid .mp4. Calling spawn_video...")
            
            local start_norm, end_norm, root_note = get_rs5k_params(track, fx)
            
            local item, take = spawn_video(path, start_norm, end_norm, note, root_note) 
            
            if item and take then
              note_to_item[note] = {
                item = item,
                take = take,
                start_time = reaper.GetPlayPosition(),
                root_note = root_note,
                incoming_note = note
              }
              msg("Video spawned and locked to note " .. note)
              
              -- We found a match, but we DON'T break.
              -- We continue checking other FX slots.
            else
              msg("ERROR: spawn_video was called but returned nil.")
            end
          else
            msg("Path was nil or not an .mp4. Aborting this FX.")
          end
        else
          msg("Note " .. note .. " is OUTSIDE range. Checking next FX.")
        end -- end if note in range
      end -- end if is rs5k
    end -- end FX loop
  end -- end track loop
end

local function handle_note_off(note)
  local info = note_to_item[note]
  if not info then return end
  
  if info and info.item then
    local item = info.item
    
    -- *** NEW VALIDATION LINE ***
    -- Check if the item pointer is still valid before using it
    if not reaper.ValidatePtr2(0, item, "MediaItem*") then
      msg("Note Off: Item pointer was invalid, skipping trim.")
      note_to_item[note] = nil -- Clear the invalid lock
      return 
    end
    
    -- Get the time the note was released
    local note_off_time = reaper.GetPlayPosition()
    
    -- Calculate the new duration (how long the key was held)
    local new_duration = note_off_time - info.start_time
    
    -- Get the item's current (maximum) length
    local max_duration = reaper.GetMediaItemInfo_Value(item, "D_LENGTH")
    
    -- Check if the new duration is shorter than the max
    if new_duration > 0 and new_duration < max_duration then
      -- Trim the item by setting its new, shorter length
      reaper.SetMediaItemInfo_Value(item, "D_LENGTH", new_duration)
      reaper.UpdateArrange()
      msg("Note Off: Trimmed item to " .. new_duration .. "s")
    end
  end -- <<< ADD THIS 'END' to close 'if info and info.item then'
  -- Clear the note from the active table
  note_to_item[note] = nil
end

local function handle_modwheel(val) -- val is 0-127
  -- This function is now separate from the loop and clean
  local norm = val / 127
  for t = 0, reaper.CountTracks(0) - 1 do
    local track = reaper.GetTrack(0, t)
    local fx = find_rs5k_fx(track)
    if fx then
      reaper.TrackFX_SetParam(track, fx, START_OFFSET_PARAM_IDX, norm)
    end
  end
end

local function handle_pitch_bend(val) -- val is 0-16383
  -- OPTIMIZATION...
  local pitch_bucket = math.floor(val / 64)
  if pitch_bucket == last_pitch_bucket then
    return
  end
  last_pitch_bucket = pitch_bucket

  -- 1. CALCULATE AND STORE THE NEW GLOBAL BEND
  g_current_bend_semitones = ((val - 8192) / 8191) * PITCH_BEND_RANGE_SEMITONES
  
  -- We no longer save to the project.
end

--------------------------------------------------
-- 🎞️ Decoupled UI Updater (15fps)
--------------------------------------------------
local function updater()
  -- Loop through all currently playing notes
  for note, info in pairs(note_to_item) do
    if info and info.take and reaper.ValidatePtr2(0, info.take, "MediaItem_Take*") then
      
      -- Read the base note and the *current global bend*
      local base_semitones = info.incoming_note - info.root_note
      local total_semitones = base_semitones + g_current_bend_semitones
      
      -- Calculate and set the new rate
      local new_rate = 2 ^ (total_semitones / 12)
      reaper.SetMediaItemTakeInfo_Value(info.take, "D_PLAYRATE", new_rate)
    end
  end
  
  -- Run this function again in 0.066 seconds (~15fps)
  reaper.defer(updater)
end

--------------------------------------------------
-- ♻️ Main Deferred Loop (Extra-Verbose Debug)
--------------------------------------------------

local function main()
  local events_to_process = {}
  local new_last_seq = 0
  local idx = 0
  local did_process_note = false -- Flag to update arrange only if needed

  -- 1. Latch the queue and find all new events
  while true do
    local retval, msg_str, ts, devIdx, projPos, projLoopCnt = reaper.MIDI_GetRecentInputEvent(idx)
    
    if retval > 0 and retval > last_processed_event_seq then
      table.insert(events_to_process, {
        seq = retval,
        msg = msg_str
      })
      
      if new_last_seq == 0 then
        new_last_seq = retval
      end
      
      idx = idx + 1
    else
      break
    end
  end

  -- 2. If we found new events, update our "last processed" marker
if new_last_seq > 0 then
    last_processed_event_seq = new_last_seq
  end

  -- *** NEW DEBUGGING ***
  if #events_to_process > 0 then
   -- msg("MainLoop: Found " .. #events_to_process .. " new event(s).")
  end

  -- 3. Process the events we collected, in reverse order (oldest to newest)
  for i = #events_to_process, 1, -1 do
    local event = events_to_process[i]
    local msg_str = event.msg
    
    if msg_str and #msg_str >= 3 then
      local b1, b2, b3 = string.byte(msg_str, 1, 3)
      local status = b1 & 0xF0

      -- *** NEW DEBUGGING ***
      --msg("MainLoop: Processing event. Status: " .. string.format("0x%X", status))

      -- Route to our handlers
      if status == 0x90 then -- Note On
        --msg("MainLoop: Event is Note On. Calling handle_note_on...")
        if b3 > 0 then handle_note_on(b2)
        else handle_note_off(b2) end
        did_process_note = true
        
      elseif status == 0x80 then -- Note Off
        --msg("MainLoop: Event is Note Off. Calling handle_note_off...")
        handle_note_off(b2)
        did_process_note = true
        
      elseif status == 0xB0 and b2 == 1 then -- CC1 (Mod Wheel)
        --handle_modwheel(b3) -- Still DISABLED
        
      elseif status == 0xE0 then -- Pitch Bend
        --msg("MainLoop: Event is Pitch Bend. Calling handle_pitch_bend...")
        local bend_val = (b3 * 128) + b2 -- 14-bit value
        handle_pitch_bend(bend_val)
        -- We DON'T set the flag here, to prevent console spam
      else
        --msg("MainLoop: Event is other status, ignoring.")
      end
    end
  end

  -- 4. Update the screen once, only if we processed notes
  if did_process_note then
    reaper.UpdateArrange()
  end

  reaper.defer(main)
end
--------------------------------------------------
-- 🚀 Start
--------------------------------------------------
reaper.ShowConsoleMsg("RS5K Video Sampler (v2.0 Queue-Based) running...\n")
get_or_create_video_track()
main()
updater() -- <<< ADD THIS to start the 15fps UI loop
  

