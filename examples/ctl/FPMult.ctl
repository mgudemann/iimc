#PASS: (0)
#Legal operands cannot produce illegal results. The only illegal
# operands in our case are the denormals.
AG(((start & !FPM.state<1> & !FPM.state<0>) & ((!y<6> & !y<5> & !y<4> & !y<3>) -> (!y<2> & !y<1> & !y<0>)) & ((!x<6> & !x<5> & !x<4> & !x<3>) -> (!x<2> & !x<1> & !x<0>))) -> AX AX AX((!z<6> & !z<5> & !z<4> & !z<3>) -> (!z<2> & !z<1> & !z<0>)))

#FAIL: (1)
#If the sign bits are different the result is negative.
# This formula fails because one operand may be NaN.
AG(((start & !FPM.state<1> & !FPM.state<0>) & (y<7> ^ x<7>)) -> AX AX AX (z<7>))

#PASS: (2)
#If the sign bits are the same the result is positive.
AG(((start & !FPM.state<1> & !FPM.state<0>) & !(y<7> ^ x<7>)) -> AX AX AX (!z<7>))

#PASS: (3)
#If one of the operands is NaN the result is NaN.
AG(((start & !FPM.state<1> & !FPM.state<0>) & ((y<6> & y<5> & y<4> & y<3> &
!(!y<2> & !y<1> & !y<0>)) | (x<6> & x<5> & x<4> & x<3> & !(!x<2> & !x<1> &
!x<0>)))) -> AX AX AX ((z<6> & z<5> & z<4> & z<3> & !(!z<2> & !z<1> & !z<0>))))

#FAIL: (4-5)
#If one of the operands is zero and the other operand is
#      not NaN the result is zero.
# These properties should fail, because infinity * zero = NaN.
AG(((start & !FPM.state<1> & !FPM.state<0>) & !y<6> & !y<5> & !y<4> & !y<3> &
!y<2> & !y<1> & !y<0> & !(x<6> & x<5> & x<4> & x<3> & !(!x<2> & !x<1> &
!x<0>))) -> AX AX AX (!z<6> & !z<5> & !z<4> & !z<3> & !z<2> & !z<1> & !z<0>))
AG(((start & !FPM.state<1> & !FPM.state<0>) & !x<6> & !x<5> & !x<4> & !x<3> &
!x<2> & !x<1> & !x<0> & !(y<6> & y<5> & y<4> & y<3> & !(!y<2> & !y<1> &
!y<0>))) -> AX AX AX (!z<6> & !z<5> & !z<4> & !z<3> & !z<2> & !z<1> & !z<0>))

#PASS: (6-7)
#If one of the operands is infinite and the other operand is
#      neither NaN nor zero the result is infinite.
AG(((start & !FPM.state<1> & !FPM.state<0>) & (y<6> & y<5> & y<4> & y<3> & !y<2> & !y<1> & !y<0>) & !(x<6> & x<5> & x<4> & x<3> & !(!x<2> & !x<1> & !x<0>)) & !(!x<6> & !x<5> & !x<4> & !x<3>)) -> AX AX AX (z<6> & z<5> & z<4> & z<3> & !z<2> & !z<1> & !z<0>))
AG(((start & !FPM.state<1> & !FPM.state<0>) & (x<6> & x<5> & x<4> & x<3> & !x<2> & !x<1> & !x<0>) & !(y<6> & y<5> & y<4> & y<3> & !(!y<2> & !y<1> & !y<0>)) & !(!y<6> & !y<5> & !y<4> & !y<3>)) -> AX AX AX (z<6> & z<5> & z<4> & z<3> & !z<2> & !z<1> & !z<0>))

