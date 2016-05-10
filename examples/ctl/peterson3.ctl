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

#PASS: (6)
AG((~state<*0*><2> & ~state<*0*><1> & ~state<*0*><0>) -> 
   AX AX AX AX AX AX AX AX AX AX AX ~state<*0*><2>)

#FAIL: (7)
AG((~state<*0*><2> & ~state<*0*><1> & ~state<*0*><0>) -> 
   AX AX AX AX AX AX AX AX AX AX AX AX ~state<*0*><2>)

#PASS: (8-10)
AG(state<*0*><2> -> (pos<*0*><1> & ~pos<*0*><0>))
AG(state<*1*><2> -> (pos<*1*><1> & ~pos<*1*><0>))
AG(state<*2*><2> -> (pos<*2*><1> & ~pos<*2*><0>))

#PASS: (11-13)
AG((~state<*0*><2> & ~state<*0*><1> & ~state<*0*><0>) -> (~pos<*0*><1> & ~pos<*0*><0>))
AG((~state<*1*><2> & ~state<*1*><1> & ~state<*1*><0>) -> (~pos<*1*><1> & ~pos<*1*><0>))
AG((~state<*2*><2> & ~state<*2*><1> & ~state<*2*><0>) -> (~pos<*2*><1> & ~pos<*2*><0>))

#PASS: (14)
AG ~(j<*0*><1> & ~j<*0*><0> & j<*1*><1> & ~j<*1*><0> & j<*2*><1> & ~j<*2*><0>)

#PASS: (15-17)
AG(~state<*0*><1> | state<*0*><2> | (pos<*0*><1> == j<*0*><1>) & (pos<*0*><0> == j<*0*><0>))
AG(~state<*1*><1> | state<*1*><2> | (pos<*1*><1> == j<*1*><1>) & (pos<*1*><0> == j<*1*><0>))
AG(~state<*2*><1> | state<*2*><2> | (pos<*2*><1> == j<*2*><1>) & (pos<*2*><0> == j<*2*><0>))
