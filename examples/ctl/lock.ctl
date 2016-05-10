#PASS: (0)
#Transition to State 3 only occurs under the required circumstances.
AG((state<1> & state<0>) |
   ~E ~((state<1> & ~state<0>) & (~position<4> & position<3> & position<2> & position<1> & position<0>) & upReg) U (state<1> & state<0>))

#PASS: (1)
#Transition to State 2 only occurs under the required circumstances.
AG((state<1> & ~state<0>) |
   ~E ~((~state<1> & state<0>) & (position<4> & ~position<3> & position<2> & ~position<1> & position<0>) & downReg) U (state<1> & ~state<0>))

#PASS: (2)
#Transition to State 1 only occurs under the required circumstances.
AG((~state<1> & state<0>) |
   ~E ~((~state<1> & ~state<0>) & (~position<4> & position<3> & position<2> & ~position<1> & ~position<0>) & upReg) U (~state<1> & state<0>))

#PASS: (3)
#To get from State 2 to State 0 either downReg=1 or State 3 must occur.
AG((state<1> & ~state<0>) -> ~E ~downReg & ~(state<1> & state<0>) U (~state<1> & ~state<0>))

#PASS: (4)
#To get from State 1 to State 0 either upReg=1 or State 2 must occur.
AG((~state<1> & state<0>) -> ~E ~upReg & ~(state<1> & ~state<0>) U (~state<1> & ~state<0>))


