#FAIL: (0)
AG ~bad

#FAIL: (1)
AG((~pc2<1> & pc2<0>) -> AX((pc2<1> & ~pc2<0>) -> AG(~bad)))

#FAIL: (2)
AG((thread<1> & ~thread<0>) -> AX((thread<1> & ~thread<0>) -> AG(~bad)))

#PASS: (3)
AG(~pc2<1> & thread<1> & ~thread<0> -> AX(pc2<1> -> AG(~bad)))

#FAIL: (4)
A ~bad U (~bad & pc3<1> & ~pc3<0>)

#FAIL: (5)
A ~bad U (~bad & pc3<1> & ~pc3<0> & pc2<1> & ~pc2<0> & pc1<1> & ~pc1<0>)
