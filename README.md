# Probabilistic Horn Abduction
### Originally by David Poole.
### Reimplemented by Samer Abdallah

This is an implementation of probabilistic Horn abduction (pHa), a form
of probabilistic programming consisting of an object language that includes
random variables and random world semantics, and an inference strategy based
on a simulated prioritised multithreaded search for solutions of probabilistic
goals.

To run from the UNIX shell,

	$ swipl -s <pha>/scripts/run.pl

Alternatively, you can run the script from the SWI command line with:

	?- [pack(pha/scripts/run)].

This will load the alarm.pha model and drop you immediately into the interactive stateful
top level. The state consists of observations that have been made, and is initially empty.
To get the probability of a goal, try, eg

	>> prob(fire(yes),P).

This will tell you the probability that the building is on fire.
To test the old adage that 'where there's smoke there's fire', you can check the probabilities:

	>> prob(fire(yes)|smoke(yes), P).
	>> prob(fire(no)|smoke(yes), P).

So there you are: where there's smoke there may or may not be fire.
To push an observation on to the stack, do, eg

	>> observe(alarm(yes)).

This means that you have observed that the fire alarm is on. What is the probability that
the building is on fire now?

	>> prob(fire(yes),P).

What is the probability that the building is on fire if, in addition to the alarm being on,
there is also smoke?

	>> prob(fire(yes)|smoke(yes),P).

What are the explanations for the alarm being on?

	>> explanations(0). % 0 means account for ALL probability mass

Or to get them one by one,

	>> explanation(E).

There are more models in pack(pha/models). The run.pl script adds this path
as the file search path 'pha'.

### Implmentation notes

This implementation is a complete re-write of Poole's which I did in 2015, 
completely removing the use of mutable state and failure driven processing. 
The original used mutable state to manage a collection of prioritised 'threads' 
(see below), whereas this one uses state threading and DCG notation to that instead. 
It also uses lazy lists to manage the generation of explanations on demand, and uses 
another layer of DCG state threading to keep track of a stack of observations, as 
illustrated above.

Given more recent work on probabilistic programming, such as Oleg Kiselyov's Hansei,
Church, Bher, WebPPL, Anglican and so on, it is interesting to see PHA and Poole's original
implementation in terms of a multithreaded exploration of probabilistic choices, with
a meta-interpreter that allows the current continuation to be captured whenever a random 
variable is to be sampled (cf. delimited continuations in Hansei or CPS-transform in 
WebPPL), a per-thread state consisting of a record of random variable choices made so 
far (cf Hansei's lazy and Church's mem), and sort of thread scheduler that runs the
threads with highest probability first.

In this light, it might be interesting to re-implement this not as an object language 
with an interpreter, but in 'direct style' using delimited continuations (shift/reset) 
to handle the simulated multi-threading.
