#PASS: (0-7) Trivial local invariants
AG (cs0.owned<1> | ~cs0.owned<0>)
AG (cs1.owned<1> | ~cs1.owned<0>)
AG (cs2.owned<1> | ~cs2.owned<0>)
AG (cs3.owned<1> | ~cs3.owned<0>)

AG (~ph0.state<1> | ~ph0.state<0>)
AG (~ph1.state<1> | ~ph1.state<0>)
AG (~ph2.state<1> | ~ph2.state<0>)
AG (~ph3.state<1> | ~ph3.state<0>)

#PASS: (8-11) Mutual exclusion
AG(~eating<0> | ~eating<1>)
AG(~eating<1> | ~eating<2>)
AG(~eating<2> | ~eating<3>)
AG(~eating<3> | ~eating<0>)

#PASS: (12) Mutual exclusion all at once
AG((~eating<0> | ~eating<1>) & (~eating<1> | ~eating<2>) &
   (~eating<2> | ~eating<3>) & (~eating<3> | ~eating<0>))

#PASS: (13-16) An eating philosopher holds both chopsticks
AG(eating<0> -> (cs0.owned<1> & cs0.owned<0> & cs3.owned<1> & ~cs3.owned<0>))
AG(eating<1> -> (cs1.owned<1> & cs1.owned<0> & cs0.owned<1> & ~cs0.owned<0>))
AG(eating<2> -> (cs2.owned<1> & cs2.owned<0> & cs1.owned<1> & ~cs1.owned<0>))
AG(eating<3> -> (cs3.owned<1> & cs3.owned<0> & cs2.owned<1> & ~cs2.owned<0>))

#PASS: (17-20) A philosopher cannot hold a clean chopstick while thinking
AG(clean<0> & cs0.owned<1> & cs0.owned<0> -> ~thinking<0>)
AG(clean<1> & cs1.owned<1> & cs1.owned<0> -> ~thinking<1>)
AG(clean<2> & cs2.owned<1> & cs2.owned<0> -> ~thinking<2>)
AG(clean<3> & cs3.owned<1> & cs3.owned<0> -> ~thinking<3>)

#PASS: (21-24) Start eating only if hungry and holding both chopsticks
AG((cs0.owned<1> & cs0.owned<0> & cs3.owned<1> & ~cs3.owned<0> & ~thinking<0>) | AX(~eating<0>))
AG((cs1.owned<1> & cs1.owned<0> & cs0.owned<1> & ~cs0.owned<0> & ~thinking<1>) | AX(~eating<1>))
AG((cs2.owned<1> & cs2.owned<0> & cs1.owned<1> & ~cs1.owned<0> & ~thinking<2>) | AX(~eating<2>))
AG((cs3.owned<1> & cs3.owned<0> & cs2.owned<1> & ~cs2.owned<0> & ~thinking<3>) | AX(~eating<3>))

#PASS: (25-28) Each chopstick is held by either philosopher at all times
AG(cs0.owned<1>)
AG(cs1.owned<1>)
AG(cs2.owned<1>)
AG(cs3.owned<1>)

#PASS: (29-36) No philosopher eats twice without a hungry neighbor eating
#      at least once in between
AG(eating<0> & hungry<1> -> AX(~eating<0> -> (A eating<1> R ~eating<0>)))
AG(eating<1> & hungry<2> -> AX(~eating<1> -> (A eating<2> R ~eating<1>)))
AG(eating<2> & hungry<3> -> AX(~eating<2> -> (A eating<3> R ~eating<2>)))
AG(eating<3> & hungry<0> -> AX(~eating<3> -> (A eating<0> R ~eating<3>)))
AG(eating<0> & hungry<3> -> AX(~eating<0> -> (A eating<3> R ~eating<0>)))
AG(eating<1> & hungry<0> -> AX(~eating<1> -> (A eating<0> R ~eating<1>)))
AG(eating<2> & hungry<1> -> AX(~eating<2> -> (A eating<1> R ~eating<2>)))
AG(eating<3> & hungry<2> -> AX(~eating<3> -> (A eating<2> R ~eating<3>)))

#FAIL: (37-40) A hungry philosopher may be beaten to the punch by a
#      thinking neighbor
AG(hungry<0> & thinking<1> & thinking<3> -> AX(eating<0>))
AG(hungry<1> & thinking<2> & thinking<0> -> AX(eating<1>))
AG(hungry<2> & thinking<3> & thinking<1> -> AX(eating<2>))
AG(hungry<3> & thinking<0> & thinking<2> -> AX(eating<3>))

#PASS: (41-44) Philosophers cannot go from hungry to thinking directly
AG(hungry<0> -> AX(~thinking<0>))
AG(hungry<1> -> AX(~thinking<1>))
AG(hungry<2> -> AX(~thinking<2>))
AG(hungry<3> -> AX(~thinking<3>))

# The following properties (except resetability) require fairness constraints

#PASS: (45-48) No starvation
AG(hungry<0> -> AF(eating<0>))
AG(hungry<1> -> AF(eating<1>))
AG(hungry<2> -> AF(eating<2>))
AG(hungry<3> -> AF(eating<3>))

#PASS: (49-52) A weaker form of no starvation
AG AF(~hungry<0>)
AG AF(~hungry<1>)
AG AF(~hungry<2>)
AG AF(~hungry<3>)

#PASS: (53-60) Requests for chopsticks are eventually granted
AG(hungry<0> -> AF(cs0.owned<1> & ~cs0.owned<0>))
AG(hungry<1> -> AF(cs1.owned<1> & ~cs1.owned<0>))
AG(hungry<2> -> AF(cs2.owned<1> & ~cs2.owned<0>))
AG(hungry<3> -> AF(cs3.owned<1> & ~cs3.owned<0>))
AG(hungry<0> -> AF(~cs3.owned<1> & cs3.owned<0>))
AG(hungry<1> -> AF(~cs0.owned<1> & cs0.owned<0>))
AG(hungry<2> -> AF(~cs1.owned<1> & cs1.owned<0>))
AG(hungry<3> -> AF(~cs2.owned<1> & cs2.owned<0>))

#PASS: (61-66) Resetability properties
AG EF(clean<3> & clean<2> & clean<1> & clean<0>)
AG EF(~clean<3> & ~clean<2> & ~clean<1> & ~clean<0>)
AG EF(~eating<3> & ~eating<2> & ~eating<1> & ~eating<0>)
AG EF(~eating<3> & eating<2> & ~eating<1> & eating<0>)
AG EF(eating<3> & ~eating<2> & eating<1> & ~eating<0>)
AG EF(hungry<3> & hungry<2> & hungry<1> & hungry<0>)

#PASS: (67-70) Each chopstick is dirty infinitely often
AG AF(~clean<0>)
AG AF(~clean<1>)
AG AF(~clean<2>)
AG AF(~clean<3>)

#FAIL: (71-74) A chopstick may remain eventually dirty if one
#      of the two philosophers who may use it never eats again
AG AF(clean<0>)
AG AF(clean<1>)
AG AF(clean<2>)
AG AF(clean<3>)
