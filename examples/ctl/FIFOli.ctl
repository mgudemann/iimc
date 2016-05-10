#PASS: (0)
AG AF(pushReg -> srFull & rbFull)
#PASS: (1)
AG AF(popReg & ~pushReg -> srEmpty & rbEmpty)
#PASS: (2)
AG EF (~rb.tail<3> & ~rb.tail<2> & ~rb.tail<1> & ~rb.tail<0> &
       ~sr.tail<3> & ~sr.tail<2> & ~sr.tail<1> & ~sr.tail<0>)
#FAIL: (3)
AG((rb.tail<3> == sr.tail<3>) & (rb.tail<2> == sr.tail<2>) &
   (rb.tail<1> == sr.tail<1>) & (rb.tail<0> == sr.tail<0>))
#PASS: (4) Trivially true.
AF((rb.tail<3> == sr.tail<3>) & (rb.tail<2> == sr.tail<2>) &
   (rb.tail<1> == sr.tail<1>) & (rb.tail<0> == sr.tail<0>))
#FAIL: (5)
AG AF((rb.tail<3> == sr.tail<3>) & (rb.tail<2> == sr.tail<2>) &
      (rb.tail<1> == sr.tail<1>) & (rb.tail<0> == sr.tail<0>))
