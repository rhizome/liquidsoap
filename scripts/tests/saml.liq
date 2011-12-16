#!../../src/liquidsoap --saml --errors-as-warnings

%include "../saml.liq"

open (saml)
open (math)

def ignore (x) = () end

def now () = time.now () end

def f () =
    r = ref (1.1)
    r = ref (1.2)
    r := !r + 1.
    r = ref (1.3)
    3. + !r
end

#saml.emit.generator.c(f ())

#saml.emit.generator.c(now() + 1.)

#saml.emit.generator.c(3. * now())

def f (y) =
    x = ref (5.)
    x := !x + 1.
    !x
end
#saml.emit.generator.c(f(3.))

#saml.emit.generator.c(sin(440. * time.now()))

def f () =
    r = [ a = 3., b = .2 ]
    r.b
end

#saml.emit.generator.c(f())

def f () =
    freq = ref(440.)
    amp = ref(1.)
    active = ref(false)
    [
        set_freq = fun (x) -> freq := x,
        set_velocity = fun (x) -> amp := x,
        main = !amp * sin(2. * pi * !freq * now ()),
        activate = fun () -> active := true,
        is_active = fun () -> !active,
        note_off = fun () -> active := false,
    ]
end

#saml.emit.generator.dssi.c(f())

def osc () =
    def f (freq) = sin(2. * pi * freq * now()) end
#    def f (freq) = (if true then 1. else 0. end) * f(freq) end
    def f (freq) = env.adsr() * f(freq) end
    gen.voice(f)
end

saml.emit.generator.dssi.c(osc())

#saml.emit.generator.c(osc().main)

def f () =
    print_int(4)
    c = event.channel()
    event.handle(c, print_int)
    event.emit(c, 5)
    3.
end

#saml.emit.generator.c(f())
