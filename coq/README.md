# twitchcoq

Reimplementing a subset of Coq in Python


## Notes

First order logic:

<pre>
Theorem test : exists x : nat, x + 2 = 4.
Theorem test : exists y : nat, (exists x : nat, x - 2 = y).
</pre>

Second order logic (quantifying over first order logic statements):

<pre>
forall y : (fun x : nat -> nat)
</pre>

Higher order logic... so on and so forth

