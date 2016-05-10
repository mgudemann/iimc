#PASS: (0) Mutual exclusion.
AG ~nmutex

#PASS: (1-4) No starvation.
AG AF inCS<0>
AG AF inCS<1>
AG AF inCS<2>
AG AF inCS<3>

#PASS: (5)
AG invar
