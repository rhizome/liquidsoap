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
    def g(x) = x + x end
    def a =
        r = ref (0)
        r := !r + 1
        2.
    end
    g(a)
end
#saml.emit.generator.c(f())

def f () =
    r = ref (5.)
    #t = 6.
    t = now()
    c = event.channel()
    event.handle(c, fun (_) -> r := t)
    event.emit(c,())
    #event.handle(c, fun (_) -> r := t)
    1.
end
#saml.emit.generator.c(f())

def h (e=event.channel()) = event.emit(e,()) 0. end
def f () =
    h()
end
#saml.emit.generator.c(f())

def osc () =
    def f (freq) =
        y = ref 0.
        ans = !y
        y := !y + freq * period
        if !y >= 1. then y := 0. end
        ans / 5.
    end
    def f (freq) = gen.saw(freq) / 5. end
    def f (note) =
        x = f(note.freq)
        event.handle(note.note_off, fun(_) -> event.emit(note.desactivate, ()))
        x
    end
    gen.voice(f)
end
#saml.emit.generator.dssi.c(osc())

def osc () =
    def f (freq) = gen.saw(freq) end
    def f (note) =
        event.handle(note.note_off, fun(_) -> event.emit(note.desactivate, ()))
        freq = note.freq
        x = f(freq) / 5.
        #x = env.adsr(a=0.005, d=0.001, r=0.05, note_off=note.note_off, desactivate=note.desactivate) * f(freq) / 5.
        #x = filter.fo.low_pass(env.adsr(a=0.005, d=0.01, s=0.5) * 10000., x)
        x
    end
    gen.voice(f)
end
saml.emit.generator.dssi.c(osc())

def osc () =
    note_off = event.channel()
    def f () =
        r = 10./5.
        event.handle(note_off, fun(_) -> print_float (r+r))
        5.
    end
    [
        set_freq = fun(_) -> (),
        set_velocity = fun(_) -> (),
        note_off = fun() -> event.emit(note_off,()),
        activate = fun() -> (),
        is_active = fun() -> true,
        main = f(),
    ]
end
#saml.emit.generator.dssi.c(osc())

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
        #freq = freq + gen.noise()
        #freq = freq*(1.+gen.sine(5.)/200. * pow(10.,now()*10.)/10.)
        freq = freq*(1.+gen.sine(5.)/200.)
        #r = 200./freq
        #freq = freq+(random.float(r)-r/2.)*4.
        x = env.adsr(a=0.005, d=0.001, r=0.05, note_off=note.note_off, desactivate=note.desactivate) * f(freq) / 5.
        x = x + gen.sine(note.freq) / 15.
        #x = x + env.adsr(a=0.01,d=0.01,s=0.005) * gen.noise() / 10.
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
