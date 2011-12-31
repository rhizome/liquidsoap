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

#saml.emit.generator.c(3. + 4.)

#saml.emit.generator.c(f ())

#saml.emit.generator.c(now() + 1.)

#saml.emit.generator.c(3. * now())

#saml.emit.generator.c(now() * now())

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
    r = ref (1.)
    c = event.channel()
    event.handle(c,fun (x) -> r := !r + x)
    event.emit(c,5.)
    !r
end

#saml.emit.generator.c(f())

def f () =
    freq = ref(440.)
    amp = ref(1.)
    active = ref(false)
    [
        set_freq = fun (x) -> freq := x,
        set_velocity = fun (x) -> amp := x,
        main = !amp * sin(2. * pi * !freq * now ()) / 2.,
        activate = fun () -> active := true,
        is_active = fun () -> !active,
        note_off = fun () -> active := false,
    ]
end

#saml.emit.generator.dssi.c(f())

def f () =
    def adsr (~note_off=event.channel()) =
        event.handle(note_off, fun(_)-> ())
        1.
    end
    adsr()
end
#saml.emit.generator.c(f())

def f () =
    x = ref (3.)
    def r () = [ a = !x ] end
    def f (r) = r.a end
    f(r())
end
#saml.emit.generator.c(f())

def f () =
    c = event.channel()
    d = event.channel()
    event.handle(c, fun(_) -> event.emit(d,()))
    event.emit(c,())
    3.3
end
#saml.emit.generator.c(f())

def f () =
    #t = 3.
    t = now()
    r = ref (5.)
    c = event.channel()
    event.handle(c, fun (_) -> r := t)
    event.emit(c,())
    1.
end
#saml.emit.generator.c(f())

def f () =
    period = 3. * period
    sin(2. * pi * now())
end
#saml.emit.generator.c(f())

def f () =
    def f (x) =
        period = 440. * period
        period
    end
    #f = time.frequencize(gen.sine())
    x = f(440.)
    print_float(period)
    x
end
#saml.emit.generator.c(f())

def f () =
    x = sin(2. * pi * now())
    #x = 5.
    x = filter.fo.low_pass(440., x)
    x
end
#saml.emit.generator.c(f())

def f () =
    r = ref (5.)
    #t = 3.
    t = now()
    c = event.channel()
    event.handle(c, fun (_) -> r := t)
    event.handle(c, fun (_) -> r := t)
    event.emit(c,())
    1.
end
saml.emit.generator.c(f())

def osc () =
#    def f (freq) = sin(2. * pi * freq * now()) end
#    def f (freq) = (now() * freq) mod 1. end
#    def f (freq) =
#        period = freq * period
#        sin(2. * pi * now())
#    end
    def f (freq) = gen.saw(freq) end
    def f (note) =
        #event.handle(note.note_off, fun(_) -> event.emit(note.desactivate, ()))
        freq = note.freq
        #freq = freq*(1.+gen.sine(5.)/200. * pow(10.,now()*10.)/10.)
        #freq = freq*(1.+gen.sine(5.)/200.)
        #r = 200./freq
        #freq = freq+(random.float(r)-r/2.)*4.
        x = env.adsr(a=0.005, d=0.001, r=0.05, note_off=note.note_off, desactivate=note.desactivate) * f(freq) / 5.
        x = x + gen.sine(note.freq) / 15.
        x = filter.fo.low_pass(env.adsr(a=0.005, d=0.01, s=0.5) * 10000., x)
        x
    end
    gen.voice(f)
end
#saml.emit.generator.dssi.c(osc())

#saml.emit.generator.c(osc().main)

def f () =
    print_int(4)
    c = event.channel()
    event.handle(c, print_int)
    event.emit(c, 5)
    3.
end

#saml.emit.generator.c(f())
