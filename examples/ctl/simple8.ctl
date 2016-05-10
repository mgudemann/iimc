#PASS: (0-7) Absence of starvation.  Needs fairness constraints.
AG (~P0.state<1> & P0.state<0> -> AF (P0.state<1> & ~P0.state<0>))
AG (~P1.state<1> & P1.state<0> -> AF (P1.state<1> & ~P1.state<0>))
AG (~P2.state<1> & P2.state<0> -> AF (P2.state<1> & ~P2.state<0>))
AG (~P3.state<1> & P3.state<0> -> AF (P3.state<1> & ~P3.state<0>))
AG (~P4.state<1> & P4.state<0> -> AF (P4.state<1> & ~P4.state<0>))
AG (~P5.state<1> & P5.state<0> -> AF (P5.state<1> & ~P5.state<0>))
AG (~P6.state<1> & P6.state<0> -> AF (P6.state<1> & ~P6.state<0>))
AG (~P7.state<1> & P7.state<0> -> AF (P7.state<1> & ~P7.state<0>))

#PASS: (8-15)
AG(~P0.state<1> & ~P0.state<0> -> AX (~P0.state<1> | P0.state<0>))
AG(~P1.state<1> & ~P1.state<0> -> AX (~P1.state<1> | P1.state<0>))
AG(~P2.state<1> & ~P2.state<0> -> AX (~P2.state<1> | P2.state<0>))
AG(~P3.state<1> & ~P3.state<0> -> AX (~P3.state<1> | P3.state<0>))
AG(~P4.state<1> & ~P4.state<0> -> AX (~P4.state<1> | P4.state<0>))
AG(~P5.state<1> & ~P5.state<0> -> AX (~P5.state<1> | P5.state<0>))
AG(~P6.state<1> & ~P6.state<0> -> AX (~P6.state<1> | P6.state<0>))
AG(~P7.state<1> & ~P7.state<0> -> AX (~P7.state<1> | P7.state<0>))

#PASS: (16)
AG EF(~P0.state<1> & ~P0.state<0> & ~P1.state<1> & ~P1.state<0> &
      ~P2.state<1> & ~P2.state<0> & ~P3.state<1> & ~P3.state<0> &
      ~P4.state<1> & ~P4.state<0> & ~P5.state<1> & ~P5.state<0> &
      ~P6.state<1> & ~P6.state<0> & ~P7.state<1> & ~P7.state<0>)

#PASS: (17-23)
AG (~P0.state<1> | P0.state<0> | ~P1.state<1> | P1.state<0>)
AG (~P0.state<1> | P0.state<0> | ~P2.state<1> | P2.state<0>)
AG (~P0.state<1> | P0.state<0> | ~P3.state<1> | P3.state<0>)
AG (~P0.state<1> | P0.state<0> | ~P4.state<1> | P4.state<0>)
AG (~P0.state<1> | P0.state<0> | ~P5.state<1> | P5.state<0>)
AG (~P0.state<1> | P0.state<0> | ~P6.state<1> | P6.state<0>)
AG (~P0.state<1> | P0.state<0> | ~P7.state<1> | P7.state<0>)
