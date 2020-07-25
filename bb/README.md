# Attack Steps

0. Naive
  5+1 states, 2 values, 2 moves ^ 10 labels
  24^10 = 63 trillion, possible for sigma(5, 2)

1. Determine a canonical numbering of all the machines that's easy to enumerate and refer to the machines by.
   Should be simple, yet remove many isomorfphic machines.
   bbprover claims 150M machines.
   zany zoo claims 102,550,546
(put number here)

2. Exclude all machines that halt with <= 4098 (current ones record)
   Run for 47,176,870 steps.
(put number here)

3. Exclude all machines with a repeated state
(put number here)

4. Now it's proving time
  a. If they halt, no proof is required,
  b.    step it repeats.
  c.    But how to prove it.

