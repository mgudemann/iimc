#PASS: (0) Mutual exclusion.
AG ~nmutex

#PASS: (1-3) No starvation.
AG AF inCS<0>
AG AF inCS<1>
AG AF inCS<2>

#PASS: (4)
AG ~bad

#PASS: (5)
AG(~nmutex & ~bad)

#PASS: (6)
AG((~inCS<2> & ~inCS<1> & ~inCS<0> |
    ~Slot<*0*> & ~Slot<*1*> & ~Slot<*2*> & ~Slot<*3*>) & ~nmutex & ~bad)

#PASS: (7)
AG((~state<*0*><1> & ~state<*0*><0> | 
    ~state<*1*><1> & ~state<*1*><0> |
    (my_place<*0*><1> ^ my_place<*1*><1>) | 
    (my_place<*0*><0> ^ my_place<*1*><0>)) &
   (~state<*0*><1> & ~state<*0*><0> | 
    ~state<*2*><1> & ~state<*2*><0> |
    (my_place<*0*><1> ^ my_place<*2*><1>) | 
    (my_place<*0*><0> ^ my_place<*2*><0>)) &
   (~state<*1*><1> & ~state<*1*><0> | 
    ~state<*2*><1> & ~state<*2*><0> |
    (my_place<*1*><1> ^ my_place<*2*><1>) | 
    (my_place<*1*><0> ^ my_place<*2*><0>)) &
   (~inCS<2> & ~inCS<1> & ~inCS<0> |
    ~Slot<*0*> & ~Slot<*1*> & ~Slot<*2*> & ~Slot<*3*>) & ~nmutex & ~bad)
