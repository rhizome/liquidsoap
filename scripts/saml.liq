math.pi = 3.14159265358979323846

# Time

saml.time = [=]

def saml.time.integrator(~periodic=false,~reset=event.channel(),freq) =
    y = ref 0.
#    event.handle(reset,fun (_) -> y:=0.)
    ans = !y
    y := !y + freq * period
    if periodic and !y >= 1. then
       event.emit(reset,())
       # This is a much better approximation than 0...
       y := !y - 1.
    end
    ans
end

def saml.time.now(freq=1.) = saml.time.integrator(freq) end

def saml.time.frequencize (x,freq) =
    period = freq * period
    x
end

# Generators

saml.gen = [=]

def saml.gen.saw(freq=1.) =
    saml.time.integrator(periodic=true,freq) * 2. - 1.
end

def saml.gen.sine(freq=1.) =
    math.sin(math.pi * saml.gen.saw(freq))
end

def saml.gen.square(freq=1.) =
    x = saml.gen.saw(freq)
    if x < 0. then -1. else 1. end
end

def saml.gen.noise() =
    math.random.float(2.) - 1.
end

#def saml.gen.width(width) =
#    freq = freq
#    x = saml.gen.saw(freq)
#end

def saml.gen.seq (a,b) =
    first = ref true
    def on_eot (t) =
        first := false
    end
    if !first then
        a(on_eot = on_eot)
    else
        b
    end
end

def saml.gen.voice (f) =
    freq = ref(1.)
    def set_freq (f) = freq := f end
    velocity = ref (1.)
    def set_velocity (v) = velocity := v end
    active = ref (false)
    note_off = event.channel()
    #event.handle(note_off, fun (_) -> begin velocity := 0.; active := false end)
    desactivate = event.channel()
    def activate () = active := true end
    def is_active () = !active end
    def note () =
        [
            freq = !freq,
            note_off = note_off,
            desactivate = desactivate,
        ]
    end
    def main =
        x = f(note())
        event.handle(desactivate, fun (_) -> active := false)
        !velocity * x
    end
    [
        #TODO: implement set_note along with set_freq
        set_freq = set_freq,
        set_velocity = set_velocity,
        note_off = fun () -> event.emit(note_off,()),
        activate = activate,
        is_active = is_active,
        main = main,
    ]
end

# Envelopes

saml.env = [=]

def saml.env.adsr (~a=0.05,~d=0.02,~s=0.8,~r=0.01,~note_off=event.channel(),~desactivate=event.channel()) =
    t = saml.time.now()
    rt = ref (-1.)
    event.handle(note_off, fun(_)-> rt := t)

    if !rt >= 0. then
        x = math.max (0., (r - (t - !rt)) / r)
        x = x * s
        if x == 0. then event.emit(desactivate, ()) end
        x
    else if t < a then
        t / a
    else if t < d then
        (1. - (t - a) / d * (1. - s))
    else
        s
    end end end
end

# Filters

saml.filter = [=]

def saml.filter.prev (x) =
    p = ref 0.
    y = !p
    p := x
    y
end

def saml.filter.clip (~min=-1.,~max=1.,x) =
    math.min(max, math.max(min, x))
end

# First-order filters
saml.filter.fo = [=]

def saml.filter.fo.low_pass (freq, x) =
    omega = 2. * math.pi * freq * period
    a = omega / (1. + omega)
    #TODO: there would be a nice definition with prev if we had recursion...
    y' = ref (0.)
    y = a * x + (1. - a) * !y'
    y' := y
    y
end


# Events

def event.every(e,freq) =
    reset = event.channel()
    # TODO: ignore
    t = saml.time.integrator(periodic=true, reset=reset, freq)
    event.handle(reset, fun (_) -> event.emit(e,()))
end