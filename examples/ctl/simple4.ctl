#PASS: (0-3) Absence of starvation.  Needs fairness constraints.
AG(~P0.state<1> & P0.state<0> -> AF (P0.state<1> & ~P0.state<0>))
AG(~P1.state<1> & P1.state<0> -> AF (P1.state<1> & ~P1.state<0>))
AG(~P2.state<1> & P2.state<0> -> AF (P2.state<1> & ~P2.state<0>))
AG(~P3.state<1> & P3.state<0> -> AF (P3.state<1> & ~P3.state<0>))

#PASS: (4-7)
AG(~P0.state<1> & ~P0.state<0> -> AX (~P0.state<1> | P0.state<0>))
AG(~P1.state<1> & ~P1.state<0> -> AX (~P1.state<1> | P1.state<0>))
AG(~P2.state<1> & ~P2.state<0> -> AX (~P2.state<1> | P2.state<0>))
AG(~P3.state<1> & ~P3.state<0> -> AX (~P3.state<1> | P3.state<0>))

#PASS: (8)
AG EF (~P0.state<1> & ~P0.state<0> & ~P1.state<1> & ~P1.state<0> &
       ~P2.state<1> & ~P2.state<0> & ~P3.state<1> & ~P3.state<0>)
