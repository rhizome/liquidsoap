math.pi = 3.14159265358979323846

#saml = [=]

# Time

saml.time = [=]

def saml.time.integrator (~periodic=false,x) =
    y = ref 0.
    ans = !y
    y := !y + x * period
    # TODO: optimize this
    #if periodic then y := !y mod 1. end
    ans
end

def saml.time.now () = saml.time.integrator(1.) end

# Generators

saml.gen = [=]

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
    event.handle(note_off, fun (_) -> begin velocity := 0.; active := false end)
    deactivate = event.channel()
    event.handle(deactivate, fun (_) -> active := false)
    def activate () = active := true end
    def is_active () = !active end
    def note () =
        [
            freq = !freq,
            note_off = note_off,
            deactivate = deactivate,
        ]
    end
    [
        set_freq = set_freq,
        set_velocity = set_velocity,
        note_off = fun () -> event.emit(note_off,()),
        activate = activate,
        is_active = is_active,
        main = !velocity * f(note())
    ]
end

# Envelopes

saml.env = [=]

#c = event.channel()

def adsr (~a=0.05,~d=0.02,~s=0.8,~r=0.5,~note_off=event.channel(),~desactivate=event.channel()) =
    t = saml.time.now()
    rt = ref (-1.)
    event.handle(note_off, fun(_)-> rt := t)

    if !rt >= 0. then
        x = math.max (0., (r - (t - !rt)) / r)
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

saml.env.adsr = adsr