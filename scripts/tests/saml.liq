#!../../src/liquidsoap --saml --errors-as-warnings

%include "../saml.liq"

open (saml)
open (math)

def now () = time.now () end

def f () =
    r = ref (1.1)
    3.
end

#saml.emit.generator.c(f ())

#saml.emit.generator.c(3. * now())

def ff (y) =
    x = ref (5.)
    x := !x + 1.
    !x
end
#saml.emit.c.generator(f(3.))

def voice (f) =
    freq = ref(1.01)
    def set_freq (f) = freq := f end
#    velocity = ref (1.02)
#    def set_velocity (v) = velocity := v end
    [
        set_freq = set_freq,
#        set_velocity = set_velocity,
#        main = !velocity * f (!freq)
        main = f (!freq)
    ]
end

#saml.emit.generator.c(sin(440. * time.now()))

def osc () =
    def f (freq) = sin(freq * now()) end
    voice(f)
end

saml.emit.generator.dssi.c(osc())

#saml.emit.generator.c(osc().main)
