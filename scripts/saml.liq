math.pi = 3.14159265358979323846

# Time

saml.time = [=]

def saml.time.integrator (x) =
    y = ref 0.
    ans = !y
    y := !y + x * period
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
    def note_off () = velocity := 0.; active := false end
    def activate () = active := true end
    def is_active () = !active end
    [
        set_freq = set_freq,
        set_velocity = set_velocity,
        note_off = note_off,
        activate = activate,
        is_active = is_active,
        main = !velocity * f (!freq)
    ]
end

# Enveloppes

saml.env = [=]

def saml.env.adsr (~a=0.1,~d=0.08,~s=0.8,~r=0.5,x) =
    t = saml.time.now()
    if t < a then
        x * t / a
    else if t < d then
        x * (1. - (t - a) / d * (1. - s))
    else
        x * s
    end end
end