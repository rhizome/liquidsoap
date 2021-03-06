# Turn a source into an infaillible source by adding blank when the source is
# not available.
# @param s the source to turn infaillible
# @category Source / Track Processing
def mksafe(~id="mksafe",s)
  fallback(id=id,track_sensitive=false,[s,blank(id="safe_blank")])
end

# list.mem_assoc(key,l) returns true if l contains a pair
# (key,value)
# @category List
# @param a Key to look for
# @param l List of pairs (key,value)
def list.mem_assoc(a,l)
  def f(cur, el) =
    if not cur then
      fst(el) == a
    else
      cur
    end
  end
  list.fold(f, false, l)
end

# list.filter_assoc(key,l) returns all the elements of the form
# (key, value) from l.
# @category List
# @param k Key to look for
# @param l List of pairs (key,value)
def list.filter_assoc(k,l)
  list.filter(fun (el) -> fst(el) == k, l)
end

# Add a skip function to a source when it does not have one by default.
# @category Interaction
# @param s The source to attach the command to.
def add_skip_command(s) =
  # A command to skip
  def skip(_) =
    source.skip(s)
    "Done!"
  end
  # Register the command:
  server.register(namespace="#{source.id(s)}",
                  usage="skip",
                  description="Skip the current song.",
                  "skip",skip)
end

# Removes all metadata coming from a source.
# @category Source / Track Processing
def drop_metadata(s)
  map_metadata(fun(_)->[],update=false,strip=true,insert_missing=false,s)
end

# Default inputs and outpus.
#
# They are called "prefered" but it's not a user preference, just a view of
# what's generally preferable among the available modules.
#
# It is important that input and output preferences are in the same order: the
# chosen I/O should work in the same clock, we don't want an ALSA input and OSS
# output. The only exception is AO: it is the default output after dummy, so the
# input will be a dummy when AO is used for output.

output.prefered=output.dummy
%ifdef output.ao
  output.prefered=output.ao
%endif
%ifdef output.alsa
  output.prefered=output.alsa
%endif
%ifdef output.oss
  output.prefered=output.oss
%endif
%ifdef output.portaudio
  output.prefered = output.portaudio
%endif
%ifdef output.pulseaudio
  output.prefered=output.pulseaudio
%endif
# Output to local audio card using the first available driver in pulseaudio,
# portaudio, oss, alsa, ao, dummy.
# @category Source / Output
def output.prefered(~id="",~fallible=false,
                    ~on_start={()},~on_stop={()},~start=true,s)
  output.prefered(id=id,fallible=fallible,
                  start=start,on_start=on_start,on_stop=on_stop,
                  s)
end

def in(~id="",~start=true,~on_start={()},~on_stop={()},~fallible=false)
  blank(id=id)
end
%ifdef input.alsa
  in = input.alsa
%endif
%ifdef input.oss
  in = input.oss
%endif
%ifdef input.portaudio
  in = input.portaudio
%endif
%ifdef input.pulseaudio
  in = input.pulseaudio
%endif
# Create a source from the first available input driver in pulseaudio,
# portaudio, oss, alsa, blank.
# @category Source / Input
def in(~id="",~start=true,~on_start={()},~on_stop={()},~fallible=false)
  in(id=id,start=start,on_start=on_start,on_stop=on_stop,fallible=fallible)
end

# Output a stream using the 'output.prefered' operator. The input source does
# not need to be infallible, blank will just be played during failures.
# @param s the source to output
# @category Source / Output
def out(s)
  output.prefered(mksafe(s))
end

# Special track insensitive fallback that always skips current song before
# switching.
# @category Source / Track Processing
# @param ~input The input source
# @param f The fallback source
def fallback.skip(~input,f)
  def transition(a,b) =
    source.skip(a)
    # This eats the last remaining frame from a
    sequence([a,b])
  end
  fallback(track_sensitive=false,transitions=[transition,transition],[input,f])
end

# Compress and normalize, producing a more uniform and "full" sound.
# @category Source / Sound Processing
# @param s The input source.
def nrj(s)
  compress(threshold=-15.,ratio=3.,gain=3.,normalize(s))
end

# Multiband-compression.
# @category Source / Sound Processing
# @param s The input source.
def sky(s)
  # 3-band crossover
  low = filter.iir.eq.low(frequency = 168.)
  mh = filter.iir.eq.high(frequency = 100.)
  mid = filter.iir.eq.low(frequency = 1800.)
  high = filter.iir.eq.high(frequency = 1366.)

  # Add back
  add(normalize = false,
      [ compress(attack = 100., release = 200., threshold = -20.,
                 ratio = 6., gain = 6.7, knee = 0.3,
                 low(s)),
        compress(attack = 100., release = 200., threshold = -20.,
                 ratio = 6., gain = 6.7, knee = 0.3,
                 mid(mh(s))),
        compress(attack = 100., release = 200., threshold = -20.,
                 ratio = 6., gain = 6.7, knee = 0.3,
                 high(s))
      ])
end

# Simple crossfade.
# @category Source / Track Processing
# @param ~start_next Duration in seconds of the crossed end of track.
# @param ~fade_in Duration of the fade in for next track.
# @param ~fade_out Duration of the fade out for previous track.
# @param ~conservative Always prepare for a premature end-of-track.
# @param s The source to use.
def crossfade(~id="",~conservative=true,
              ~start_next=5.,~fade_in=3.,~fade_out=3.,
              s)
  s = fade.in(duration=fade_in,s)
  s = fade.out(duration=fade_out,s)
  fader = fun (a,b) -> add(normalize=false,[b,a])
  cross(id=id,conservative=conservative,duration=start_next,fader,s)
end

# Append speech-synthesized tracks reading the metadata.
# @category Source / Track Processing
# @param ~pattern Pattern to use
# @param s The source to use
def say_metadata
  p = 'say:$(if $(artist),"It was $(artist)$(if $(title),\", $(title)\").")'
  fun (s,~pattern=p) ->
    append(s,fun (m) -> request.queue(queue=[request.create(pattern % m)],
                                      interactive=false))
end

%ifdef soundtouch
# Increases the pitch, making voices sound like on helium.
# @category Source / Sound Processing
# @param s The input source.
def helium(s)
  soundtouch(pitch=1.5,s)
end
%endif

# Get the value associated to a variable in the process environment. Return ""
# if variable is not set.
# @category System
def getenv(s) =
  list.assoc(default="",s,environment())
end

# Perform a shell call and return its output.
# @category System
# @param ~timeout Cancel process after @timeout@ has elapsed. Ignored if negative.
# @param ~env Process environment
# @param ~inherit_env Inherit calling process's environment when @env@ parameter is empty.
# @param command Command to run
def get_process_output(~timeout=(-1.),~env=[],~inherit_env=true,command) =
  fst(fst(run_process(timeout=timeout,env=env,inherit_env=inherit_env,command)))
end

# Perform a shell call and return the list of its output lines.
# @category System
# @param ~timeout Cancel process after @timeout@ has elapsed. Ignored if negative.
# @param ~env Process environment
# @param ~inherit_env Inherit calling process's environment when @env@ parameter is empty.
# @param command Command to run
def get_process_lines(~timeout=(-1.),~env=[],~inherit_env=true,command) =
  string.split(separator="\\n",get_process_output(timeout=timeout,env=env,inherit_env=inherit_env,command))
end

# Return true if process exited with 0 code.
# @category System
# @param ~timeout Cancel process after @timeout@ has elapsed. Ignored if negative.
# @param ~env Process environment
# @param ~inherit_env Inherit calling process's environment when @env@ parameter is empty.
# @param command Command to test
def test_process(~timeout=(-1.),~env=[],~inherit_env=true,command) =
  res = run_process(timeout=timeout,env=env,command)
  snd(res) == ("exit","0")
end

# Split the arguments of an url of the form arg=bar&arg2=bar2 into
# [("arg","bar"),("arg2","bar2")].
# @category String
# @param args Agument string to split
def url.split_args(args) =
  def f(x) =
    ret = string.split(separator="=",x)
    arg = url.decode(list.nth(default="",ret,0))
    val = if list.length(ret) == 1 then "" else url.decode(list.nth(default="",ret,1)) end
    (arg,val)
  end
  l = string.split(separator="&",args)
  list.map(f,l)
end

# Split an url of the form foo?arg=bar&arg2=bar2 into
# ("foo",[("arg","bar"),("arg2","bar2")]).
# @category String
# @param uri Url to split
def url.split(uri) =
  ret = string.extract(pattern="([^\?]*)\?(.*)",uri)
  args = ret["2"]
  if args != "" then
    (ret["1"],url.split_args(ret["2"]))
  else
    (uri,[])
  end
end

# Register a server/telnet command to update a source's metadata. Returns a new
# source, which will receive the updated metadata. The command has the following
# format: insert key1="val1",key2="val2",...
# @category Source / Track Processing
# @param ~id Force the value of the source ID.
def server.insert_metadata(~id="",s) =
  x = insert_metadata(id=id,s)
  insert = fst(x)
  s = snd(x)
  def insert(s) =
    l = string.split(separator='([^=]+\s*=\s*"(\\"|[^"])*")\s*,\s*',s)
    def f(l,x) =
      sub = fun (s) -> string.replace(pattern='\\"',fun (_) -> '"',s)
      if x != "" then
        ret = string.extract(pattern='([^=]+)\s*=\s*"((?:\\"|[^"])*)"',x)
        if ret["1"] != "" then
          list.append(l,[(ret["1"],
                          sub(ret["2"]))])
        else
          l
        end
      else
        l
      end
    end
    meta = list.fold(f,[],l)
    if meta != [] then
      insert(meta)
      "Done"
    else
      "Syntax error or no metadata given. \
       Use key1=\"val1\",key2=\"val2\",.."
    end
  end
  id = source.id(s)
  server.register(namespace="#{id}",
                  description="Insert a metadata chunk.",
                  usage="insert key1=\"val1\",key2=\"val2\",..",
                  "insert",insert)
  s
end

# Register a command that outputs the RMS of the returned source.
# @category Source / Visualization
# @param ~id Force the value of the source ID.
def server.rms(~id="",s) =
  x = rms(id=id,s)
  rms = fst(x)
  s = snd(x)
  id = source.id(s)
  def rms(_) =
    rms = rms()
    "#{rms}"
  end
  server.register(namespace="#{id}",
                  description="Return the current RMS of the source.",
                  usage="rms",
                  "rms",rms)
  s
end

# Read some value from standard input (console).
# @category System
# @param ~hide Hide typed characters (for passwords).
def read(~hide=false)
  if hide then
    system("stty -echo")
  end
  s = list.hd(default="",get_process_lines("read BLA && echo $BLA"))
  if hide then
    system("stty echo")
  end
  print("")
  s
end

# Dummy implementation of file.mime
# @category System
def file.mime_default(_)
  ""
end
%ifdef file.mime
# Alias of file.mime (because it is available)
# @category System
def file.mime_default(file)
  file.mime(file)
end
%endif

# Generic mime test. First try to use file.mime if it exist.  Otherwise try to
# get the value using the file binary. Returns "" (empty string) if no value
# can be found.
# @category System
# @param file The file to test
def get_mime(file) =
  def file_method(file) =
    if test_process("which file") then
      list.hd(default="",get_process_lines("file -b --mime-type \
                                  #{quote(file)}"))
    else
      ""
    end
  end
  # First try mime method
  ret = file.mime_default(file)
  if ret != "" then
    ret
  else
    # Now try file method
    file_method(file)
  end
end


# Remove low frequencies often produced by microphones.
# @category Source / Sound Processing
# @param s The input source.
def mic_filter(s)
  filter(freq=200.,q=1.,mode="high",s)
end

# Creates a source that fails to produce anything.
# @category Source / Input
def fail(~id="")
  fallback(id=id,[])
end

# Creates a source that plays only one track of the input source.
# @category Source / Track Processing
# @param s The input source.
def once(s)
  sequence([s,fail()])
end

# Crossfade between tracks, taking the respective volume levels into account in
# the choice of the transition.
# @category Source / Track Processing
# @param ~start_next   Crossing duration, if any.
# @param ~fade_in      Fade-in duration, if any.
# @param ~fade_out     Fade-out duration, if any.
# @param ~width        Width of the volume analysis window.
# @param ~conservative Always prepare for a premature end-of-track.
# @param ~default      Transition used when no rule applies \
#                      (default: sequence).
# @param ~high         Value, in dB, for loud sound level.
# @param ~medium       Value, in dB, for medium sound level.
# @param ~margin       Margin to detect sources that have too different \
#                      sound level for crossing.
# @param s             The input source.
def smart_crossfade (~start_next=5.,~fade_in=3.,~fade_out=3.,
                     ~default=(fun (a,b) -> sequence([a, b])),
                     ~high=-15., ~medium=-32., ~margin=4.,
                     ~width=2.,~conservative=true,s)
  fade.out = fade.out(type="sin",duration=fade_out)
  fade.in  = fade.in(type="sin",duration=fade_in)
  add = fun (a,b) -> add(normalize=false,[b, a])
  log = log(label="smart_crossfade")

  def transition(a,b,ma,mb,sa,sb)

    list.iter(fun(x)-> log(level=4,"Before: #{x}"),ma)
    list.iter(fun(x)-> log(level=4,"After : #{x}"),mb)

    if
      # If A and B are not too loud and close, fully cross-fade them.
      a <= medium and b <= medium and abs(a - b) <= margin
    then
      log("Old <= medium, new <= medium and |old-new| <= margin.")
      log("Old and new source are not too loud and close.")
      log("Transition: crossed, fade-in, fade-out.")
      add(fade.out(sa),fade.in(sb))

    elsif
      # If B is significantly louder than A, only fade-out A.
      # We don't want to fade almost silent things, ask for >medium.
      b >= a + margin and a >= medium and b <= high
    then
      log("new >= old + margin, old >= medium and new <= high.")
      log("New source is significantly louder than old one.")
      log("Transition: crossed, fade-out.")
      add(fade.out(sa),sb)

    elsif
      # Opposite as the previous one.
      a >= b + margin and b >= medium and a <= high
    then
      log("old >= new + margin, new >= medium and old <= high")
      log("Old source is significantly louder than new one.")
      log("Transition: crossed, fade-in.")
      add(sa,fade.in(sb))

    elsif
      # Do not fade if it's already very low.
      b >= a + margin and a <= medium and b <= high
    then
      log("new >= old + margin, old <= medium and new <= high.")
      log("Do not fade if it's already very low.")
      log("Transition: crossed, no fade.")
      add(sa,sb)

    # What to do with a loud end and a quiet beginning ?
    # A good idea is to use a jingle to separate the two tracks,
    # but that's another story.

    else
      # Otherwise, A and B are just too loud to overlap nicely, or the
      # difference between them is too large and overlapping would completely
      # mask one of them.
      log("No transition: using default.")
      default(sa, sb)
    end
  end

  smart_cross(width=width, duration=start_next, conservative=conservative,
              transition,s)
end

# Custom playlist source written using the script language.  Will read directory
# or playlist, play all files and stop.  Returns a pair @(reload,source)@ where
# @reload@ is a function of type @(?uri:string)->unit@ used to reload the source
# and @source@ is the actual source. The reload function can optionally be
# called with a new playlist URI. Otherwise, it reloads the previous URI.
# @category Source / Input
# @param ~id Force the value of the source ID.
# @param ~random Randomize playlist content
# @param ~on_done Function to execute when the playlist is finished
# @param ~filter Filter out some files depending on metadata
# @param uri Playlist URI
def playlist.reloadable(~id="",~random=false,~on_done={()},~filter=fun(_)->true,uri)
  # A reference to the playlist
  playlist = ref []
  # A reference to the uri
  playlist_uri = ref uri
  # A reference to know if the source has been stopped
  has_stopped = ref false
  # The next function
  def rec next () =
    file =
      if list.length(!playlist) > 0 then
        ret = list.hd(default="",!playlist)
        playlist := list.tl(!playlist)
        ret
      else
        # Playlist finished
        if not !has_stopped then
          has_stopped := true
          on_done ()
        end
        ""
      end
    r = request.create(file)
    if filter(request.metadata(r)) then
      r
    else
      next ()
    end
  end
  # Instanciate the source
  source = request.dynamic(id=id,next)
  # Get its id.
  id = source.id(source)
  # The load function
  def load_playlist () =
    files =
      if file.is_directory(!playlist_uri) then
        log(label=id,"playlist is a directory.")
        get_process_lines("find #{quote(!playlist_uri)} -type f | sort")
      else
        playlist = request.create.raw(!playlist_uri)
        result =
          if request.resolve(playlist) then
            playlist = request.filename(playlist)
            files = playlist.parse(playlist)
            def file_request(el) =
              meta = fst(el)
              file = snd(el)
              s = list.fold(fun (cur, el) ->
                "#{cur},#{fst(el)}=#{string.escape(snd(el))}", "", meta)
              if s == "" then
                file
              else
                "annotate:#{s}:#{file}"
              end
            end
            list.map(file_request,files)
          else
            log(label=id,"Couldn't read playlist: request resolution failed.")
            []
          end
        request.destroy(playlist)
        result
      end
    if random then
      playlist := list.sort(fun (x,y) -> int_of_float(random.float()), files)
    else
      playlist := files
    end
  end
  # The reload function
  def reload(~uri="") =
    if uri != "" then
      playlist_uri := uri
    end
    log(label=id,"Reloading playlist with URI #{!playlist_uri}")
    has_stopped := false
    load_playlist()
  end
  # Load the playlist
  load_playlist()
  # Return
  (reload,source)
end

# Custom playlist source written using the script language. It will read directory
# or playlist, play all files and stop.
# @category Source / Input
# @param ~id Force the value of the source ID.
# @param ~random Randomize playlist content
# @param ~on_done Function to execute when the playlist is finished
# @param ~reload_mode If set to "watch", will be reloaded when the playlist is changed
# @param uri Playlist URI
def playlist.once(~id="",~random=false,~on_done={()},~reload_mode="",uri)
  rs = playlist.reloadable(id=id,random=random,on_done=on_done,uri)
  reload = fst(rs)
  s = snd(rs)
  if reload_mode == "watch" then
    unwatch = file.watch(uri,fun () -> reload())
    source.on_shutdown(s,unwatch)
  end
  s
end

# Play the whole playlist as one track.
# @category Source / Track Processing
# @param ~id Force the value of the source ID.
# @param ~random Randomize playlist content
# @param uri Playlist URI.
def playlist.merge(~id="",~random=false,uri) =
  pl = playlist.reloadable(id=id,random=random,uri)
  reload = fst(pl)
  s = snd(pl)
  s = merge_tracks(s)
  on_end(delay=0.,fun(_,_)->reload(),s)
end

# Mixes two streams, with faded transitions between the state when only the
# normal stream is available and when the special stream gets added on top of
# it.
# @category Source / Track Processing
# @param ~delay   Delay before starting the special source.
# @param ~p       Portion of amplitude of the normal source in the mix.
# @param ~normal  The normal source, which could be called the carrier too.
# @param ~special The special source.
def smooth_add(~delay=0.5,~p=0.2,~normal,~special)
  d = delay
  fade.final = fade.final(duration=d*2.)
  fade.initial = fade.initial(duration=d*2.)
  q = 1. - p
  c = amplify
  fallback(track_sensitive=false,
           [special,normal],
           transitions=[
             fun(normal,special)->
               add(normalize=false,
                   [c(p,normal),
                    c(q,fade.final(type="sin",normal)),
                    sequence([blank(duration=d),c(q,special)])]),
             fun(special,normal)->
               add(normalize=false,
                   [c(p,normal),
                    c(q,fade.initial(type="sin",normal))])
           ])
end

# Restrict a source to play only when a predicate is true.
# @category Source / Track Processing
# @param pred The predicate, typically a time interval such as \
#             <code>{10h-10h30}</code>.
def at(pred,s)
  switch([(pred,s)])
end

# Execute a given action when a predicate is true. This will be run in
# background.
# @category System
# @param ~freq Frequency for checking the predicate, in seconds.
# @param ~pred Predicate indicating when to execute the function, \
#              typically a time interval such as <code>{10h-10h30}</code>.
# @param f Function to execute when the predicate is true.
def exec_at(~freq=1.,~pred,f)
  def check()
    if pred() then
      f()
    end
    freq
  end
  add_timeout(freq,check)
end

# Enable replay gain metadata resolver. This resolver will process any file
# decoded by liquidsoap and add a replay_gain metadata when this value could be
# computed. For a finer-grained replay gain processing, use the replay_gain
# protocol.
# @category Liquidsoap
# @param ~extract_replaygain The extraction program
def enable_replaygain_metadata(
       ~extract_replaygain="#{configure.libdir}/extract-replaygain")
  def replaygain_metadata(file)
    x = get_process_lines("#{extract_replaygain} \
                              #{quote(file)}")
    if list.hd(default="",x) != "" then
      [("replay_gain",list.hd(default="",x))]
    else
      []
    end
  end
  add_metadata_resolver("replay_gain", replaygain_metadata)
end

# Assign a new clock to the given source (and to other time-dependent sources)
# and return the source. It is a conveniency wrapper around clock.assign_new(),
# allowing more concise scripts in some cases.
# @category Liquidsoap
# @param ~sync Do not synchronize the clock on regular wallclock time, \
#              but try to run as fast as possible (CPU burning mode).
def clock(~sync=true,~id="",s)
  clock.assign_new(sync=sync,id=id,[s])
  s
end

# Create a log of clock times for all the clocks initially present. The log is
# in a simple format which you can directly use with gnuplot.
# @category Liquidsoap
# @param ~interval Polling interval.
# @param ~delay    Delay before setting up the clock logger. This should \
#                  be used to ensure that the logger starts only after \
#                  the clocks are created.
# @param unlabeled Path of the log file.
def log_clocks(~delay=0.,~interval=1.,logfile)
  # Get the current clocks
  clocks = list.map(fst,get_clock_status())
  # Column headers
  system("echo \# #{string.concat(separator=' ',clocks)} > #{(logfile:string)}")
  def report()
    status = get_clock_status()
    status = list.map(fun (x) -> (fst(x),string_of(snd(x))), status)
    status = list.map(fun (c) -> status[c], clocks)
    system("echo #{string.concat(separator=' ',status)} >> #{logfile}")
    interval
  end
  if delay<=0. then
    add_timeout(interval,report)
  else
    add_timeout(delay,{add_timeout(interval,report) (-1.)})
  end
end

# Skip track when detecting a blank.
# @category Source / Track Processing
# @param ~id Force the value of the source ID.
# @param ~threshold Power in decibels under which the stream is considered silent.
# @param ~max_blank Maximum silence length allowed, in seconds.
# @param ~min_noise Minimum duration of noise required to end silence, in seconds.
# @param ~track_sensitive Reset blank counter at each track.
def skip_blank(~id="",~threshold=-40.,~max_blank=20.,~min_noise=0.,~track_sensitive=true,s)
  on_blank({source.skip(s)},threshold=threshold,max_blank=max_blank,min_noise=min_noise,track_sensitive=track_sensitive,s)
end

# Same operator as rotate but merges tracks from each sources.
# For instance, <code>rotate.merge([intro,main,outro])</code> creates a source
# that plays a sequence <code>[intro,main,outro]</code> as single track and loops back.
# @category Source / Track Processing
# @param ~id Force the value of the source ID.
# @param ~track_sensitive Re-select only on end of tracks.
# @param ~transitions Transition functions, padded with <code>fun (x,y) -> y</code> functions.
# @param ~weights Weights of the children (padded with 1), defining for each child how many tracks are played from it per round, if that many are actually available.
# @param sources Sequence of sources to be merged
def rotate.merge(~id="",~track_sensitive=true,~transitions=[],~weights=[],sources)
  ready = ref true
  duration = get(default=0.04,"frame.duration")

  def to_first(old,new) =
    ready := (not !ready)
    sequence(merge=true,[blank(duration=duration),new])
  end

  transitions = if list.length(transitions) == 0 then
    [to_first]
  else
    list.mapi((fun (i,t) ->
      if i == 0 then
        (fun (old,new) ->
          to_first(old,t(old,new)))
      else t end), transitions)
  end

  source = rotate(track_sensitive=track_sensitive,transitions=transitions,weights=weights,sources)
  source = merge_tracks(source)

  switch(id=id,replay_metadata=false,track_sensitive=false,[({!ready}, source), ({(not !ready)}, source)])
end

# Extract the left channel of a stereo source
# @category Source / Conversions
# @param s Source to extract from
def stereo.left(s)
  mean(stereo.pan(pan=-1., s))
end

# Extract the right channel of a stereo source
# @category Source / Conversions
# @param s Source to extract from
def stereo.right(s)
  mean(stereo.pan(pan=1., s))
end

# Rotate between overlapping sources. Next track starts according
# to 'liq_start_next' offset metadata.
# @category Source / Track Processing
# @param ~id Force the value of the source ID.
# @param ~start_next Metadata field indicating when the next track should start, relative to current track's time.
# @param ~weights Relative weight of the sources in the sum. The empty list stands for the homogeneous distribution.
# @param sources Sources to toggle from
def overlap_sources(~id="",~normalize=false,
                    ~start_next="liq_start_next",
                    ~weights=[],sources) =
  position = ref 0
  length   = list.length(sources)

  def current_position() =
    pos = !position
    position := (pos + 1) mod length
    pos
  end

  ready_list = list.map(fun (_) -> ref false,sources)
  grab_ready = list.nth(default=ref false,ready_list)

  def set_ready(pos,b) =
    is_ready = grab_ready(pos)
    is_ready := b
  end

  # Start next track on_offset
  def on_start_next(_,_) =
    set_ready(current_position(),true)
  end
  on_offset = on_offset(force=true,override=start_next,on_start_next)
  sources = list.map(on_offset,sources)

  # Disable after each track
  def disable(pos,source) =
    def disable(_) =
      set_ready(pos,false)
    end
    on_track(disable,source)
  end

  sources = list.mapi(disable,sources)

  # Relay metadata from all sources
  send_to_main_source = ref fun (_) -> ()

  def relay_metadata(m) =
    fn = !send_to_main_source
    fn(m)
  end
  sources = list.map(on_metadata(relay_metadata),sources)

  # Now drop all metadata
  sources = list.map(drop_metadata,sources)

  # Wrap sources into switches.
  def make_switch(pos,source) =
    is_ready = grab_ready(pos)
    switch(track_sensitive=true,[({!is_ready},source)])
  end
  sources = list.mapi(make_switch,sources)

  # Initiate the whole thing.
  set_ready(current_position(),true)

  # Create main source
  source = add(id=id,normalize=normalize,weights=weights,sources)

  # Set send_to_main_source
  x = insert_metadata(source)
  send_to_main_source := fst(x)
  snd(x)
end

# Restart one server client waiting on the given condition
# @param c condition
# @category Interaction
def server.signal(c) =
  signal = fst(snd(c))
  signal()
end

# Restart all server clients waiting on the given condition
# @param c condition
# @category Interaction
def server.broadcast(x) =
  broadcast = snd(snd(x))
  broadcast()
end
