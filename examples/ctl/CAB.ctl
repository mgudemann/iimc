#PASS: (0)
AG(p0.state & p2.state -> AF ~p0.state)
#FAIL: (1)
AG(p0.state & p2.state -> AF ~p2.state)
#PASS: (2)
AG(p0.state & p2.state -> EF ~p2.state)
#PASS: (3)
AG AF(~cabc.count<2> & ~cabc.count<1> & ~cabc.count<0> & ~cabc.shreg<11> &
      cabc.shreg<10> & ~cabc.shreg<9> & cabc.shreg<8>)
#PASS: (4)
AG AF(~cabc.count<2> & ~cabc.count<1> & ~cabc.count<0> & cabc.shreg<11> &
      cabc.shreg<10> & cabc.shreg<9> & cabc.shreg<8>)
#PASS: (5)
AG((~cabc.count<2> & ~cabc.count<1> & ~cabc.count<0>) ->
   (cabc.shreg<10> & cabc.shreg<8> & 
    (~cabc.shreg<11> & ~cabc.shreg<9> | cabc.shreg<11> & cabc.shreg<9>)))
#PASS: (6)
AG((~cab0.cstate<2> & ~cab0.cstate<1> & ~cab0.cstate<0>) |
   ((cab0.cstate<2> == cabc.count<2>) & (cab0.cstate<1> == cabc.count<1>) &
    (cab0.cstate<0> == cabc.count<0>)))
#PASS: (7)
AG((~cab1.cstate<2> & ~cab1.cstate<1> & ~cab1.cstate<0>) |
   ((cab1.cstate<2> == cabc.count<2>) & (cab1.cstate<1> == cabc.count<1>) &
    (cab1.cstate<0> == cabc.count<0>)))
#PASS: (8)
AG((~cab2.cstate<2> & ~cab2.cstate<1> & ~cab2.cstate<0>) |
   ((cab2.cstate<2> == cabc.count<2>) & (cab2.cstate<1> == cabc.count<1>) &
    (cab2.cstate<0> == cabc.count<0>)))
#PASS: (9)
AG((~cab3.cstate<2> & ~cab3.cstate<1> & ~cab3.cstate<0>) |
   ((cab3.cstate<2> == cabc.count<2>) & (cab3.cstate<1> == cabc.count<1>) &
    (cab3.cstate<0> == cabc.count<0>)))
#PASS: (10)
AG((p0.state == p2.state) -> (cab0.estate == cab2.estate))
#PASS: (11)
AG((p1.state == p3.state) -> (cab1.estate == cab3.estate))
#PASS: (12)
AG(~cabc.squash<*0*><0>)
#FAIL: (13)
AG(~cabc.squash<*5*><0>)
#PASS: (14)
AG(cabc.squash<*5*><0> -> AF ~cabc.squash<*5*><0>)
#PASS: (15)
AG ~(cab3.pstate & (cab0.pstate | cab2.pstate))
#PASS: (16)
AG ~(cab1.pstate & (cab0.pstate | cab2.pstate))
#FAIL: (17)
AG ~(cab0.pstate & cab2.pstate | cab1.pstate & cab3.pstate)
