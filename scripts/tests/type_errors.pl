#!/usr/bin/perl -w

use strict ;

my $liquidsoap = "../../src/liquidsoap";
die unless -f $liquidsoap ;

$liquidsoap = "LIQ_LADSPA=0 $liquidsoap -c";

sub section {
  print "\n*** $_[0] ***\n\n" ;
}

sub incorrect {
  my $expr = pop ;
  print "Incorrect expression $expr...\n" ;
  system "$liquidsoap '$expr'" ;
  die unless (($?>>8)==1) ;
  print "\n" ;
}

sub correct {
  my $expr = pop ;
  print "Correct expression $expr...\n" ;
  system "$liquidsoap -i '$expr'" ;
  die unless (($?>>8)==0) ;
  print "\n";
}

# TODO: move this at the end
section("RECORDS");
correct('ignore([a=4,b=5].a)');
incorrect('ignore([a=4,b=5].c)');
correct('def f(x) = x.a end ignore(f([a=4,b=5]))');
incorrect('def f(x) = x.c end ignore(f([a=4,b=5]))');
correct('r = [a=[b=0]] r = [r with a = [r.a with t = 5.]] ignore (r)');
correct('r = [a=[b=0]] def r.a.t = 5. end ignore (r)');
correct('def f(r) = ignore (r.a); ignore (r.b) end ignore (f)');
correct('def f(r) = [r with a = 5] end ignore(f([b=2]))');
correct('r = [a=0] def r.b = 5 end ignore (r.a)');
correct('r = [f = fun (r) -> ignore (r.a)] ignore (r.f([a=5,b=2])) ignore(r.f([a=3]))');

section("BASIC");
incorrect('[1]==["1"]');
incorrect('1==["1"]');
incorrect('1==(1,"1")');
# In some of those examples the type error could be reported for a
# sub-expression since we have location information.
# With the concise error, it's still pretty good currently.
incorrect('(1,1)==(1,"1")');
incorrect('(1,1)==("1",1)');
incorrect('1==request.create("")');
incorrect('fun(x)->x(snd(x))');

section("SUBTYPING");
incorrect('(1:unit)');
correct('ignore(((blank():source(1,1,1)):source(*,*,*)))');
incorrect('((blank():source(*,*,*)):source(1,1,1))');
# Next one requires the inference of a subtype (fixed vs. variable arity)
correct('ignore(audio_to_stereo(add([])))');

section("CONSTRAINTS");
incorrect('"bl"+"a"');
incorrect('(fun(a,b)->a+b)==(fun(a,b)->a+b)');
incorrect('fun(x)->x(x)'); # TODO is it an accident that we get same varname
incorrect('def f(x) y=snd(x) y(x) end');

section("LET GENERALIZATION");
correct('def f(x) = y=x ; y end ignore(f(3)+snd(f((1,2))))');
incorrect('def f(x) = y=x ; y end ignore(f(3)+"3")');

section("ARGUMENTS");
# The errors should be about the type of the param, not of the function.
incorrect('1+"1"');
# Also, a special simple error is expected for obvious labelling mistakes.
incorrect('fallback(transitions=[],xxxxxxxxxxx=[])');
incorrect('fallback(transitions=[],transitions=[])');

section("FUNCTIONS");
incorrect('fallback(transitions=[fun(~l)->1])');
incorrect('fallback(transitions=[fun(~l=1)->1])');
incorrect('fallback(transitions=[fun(x,y=blank())->y])');
incorrect('fallback(transitions=[fun(x,y)->0])');
correct('f=fallback(transitions=[fun(x,y,a=2)->x])');
incorrect('fallback(transitions=[fun(x,y)->y+1])');
correct('x=fun(f)->f(3) y=x(fun(f,u="1")->u) ignore(y)');

section("CONTENT KIND");
incorrect('output.file(%vorbis(stereo),"foo",mean(blank()))');
incorrect('output.file(%vorbis(stereo),"foo",video.add_image(blank()))');
incorrect('def f(x) = output.file(%vorbis(stereo),"",x) output.file(%vorbis(mono),"",x) end');
incorrect('add([output.file(%vorbis(stereo),"",blank()),output.file(%vorbis(mono),"",blank())])');
incorrect('add([mean(blank()),audio_to_stereo(add([]))])');

print "Everything's good!\n" ;
