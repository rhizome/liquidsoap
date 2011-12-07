#!../../src/liquidsoap --saml --errors-as-warnings

%include "../saml.liq"

open (saml)
open (math)

def ignore (x) = () end

def now () = time.now () end

def f () =
    r = ref (1.1)
    3.
end

#saml.emit.generator.c(f ())

#saml.emit.generator.c(now() + 1.)

#saml.emit.generator.c(3. * now())

def ff (y) =
    x = ref (5.)
    x := !x + 1.
    !x
end
#saml.emit.generator.c(ff(3.))

#saml.emit.generator.c(sin(440. * time.now()))

def f () =
    r = [ a = 3., b = .2 ]
    r.b
end

#saml.emit.generator.c(f())

def f () =
    r = ref(6.)
    [
        set_freq = fun (x) -> r := x,
        set_velocity = fun (x) -> r := x,
        main = 5.
    ]
end

#saml.emit.generator.dssi.c(f())

def osc () =
    def f (freq) = sin(2. * pi * freq * now()) end
    def f (freq) = env.adsr(f(freq)) end
    gen.voice(f)
end

#saml.emit.generator.dssi.c(osc())

#saml.emit.generator.c(osc().main)

def fff () =
    saml.print.int(4)
    c = event.channel()
    event.handle(c, saml.print.int)
    event.emit(c, 5)
    3.
end

saml.emit.generator.c(fff())
