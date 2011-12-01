#!../../src/liquidsoap --saml --errors-as-warnings

%include "../saml.liq"

open (saml)
open (math)

def now () = time.now () end

#saml.emit.generator.c(3. * now())

#saml.emit.c.generator(now*2.)
#saml.emit.c.generator(sin(now*2.))
def f (y) =
    x = ref (5.)
    x := !x + 1.
    !x
end
#saml.emit.c.generator(f(3.))

def handle_freq (f) =
    freq = ref(1.)
    def set_freq (f) = freq := f end
    [
        set_freq = set_freq,
        main = f (!freq)
    ]
end

saml.emit.generator.c(sin(440. * time.now()))

def osc () =
    def f (freq) = sin(freq * now()) end
    handle_freq(f)
end

#saml.emit.generator.dssi.c(osc())

#saml.emit.generator.c(osc().main)
