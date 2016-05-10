#PASS: (0)
AG ((rcvmsg) -> A (rcvmsg) U ((~rcvmsg) & A (~rcvmsg) U (sndmsg)))

#PASS: (1)
AG ((sndmsg) & (~s.smsg<1> & s.smsg<0>) -> A (sndmsg) U ((~sndmsg) & A (~sndmsg) U ((rcvmsg) & (~r.rmsg<1> & r.rmsg<0>))))

#PASS: (2)
AG ((sndmsg) & (~s.smsg<1> & ~s.smsg<0>) -> A (sndmsg) U ((~sndmsg) & A (~sndmsg) U ((rcvmsg) & (~r.rmsg<1> & ~r.rmsg<0>))))
