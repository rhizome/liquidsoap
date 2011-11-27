math.pi = 3.1416

period = 0.

saml.time = [=]

def saml.time.integrator (x) =
    y = ref 0.
    y := !y + x * period
    !y
end

def saml.time.now () = saml.time.integrator(1.) end

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