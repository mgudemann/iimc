#PASS: (0)
#The contents of a cell cannot change unless it is addressed.
AG((M<*0*>) -> ~E ~(~posn<4> & ~posn<3> & ~posn<2> & ~posn<1> & ~posn<0>) U (~(~posn<4> & ~posn<3> & ~posn<2> & ~posn<1> & ~posn<0>) & ~M<*0*>))

#FAIL: (1)
#Incorrect version of previous formula.
AG((M<*0*>) -> ~E ~(~posn<4> & ~posn<3> & ~posn<2> & ~posn<1> & ~posn<0>) U ~M<*0*>)

