#PASS: (0) Mutual exclusion.
AG ~nmutex

#PASS: (1-3) No starvation.
AG AF inCS<0>
AG AF inCS<1>
AG AF inCS<2>

#PASS: (4)
AG invar

#PASS: (5)
AG ~bad
