#PASS: (0)
#phi0-2.  If robin does not get a chance to change, then the first
# time two simultaneous requests occur when no acknowledgment is issued, 0
# is acknowledged.
~E (~req0 | ~req1 | ack0 | ack1 | EX(~ack0)) U
   (req0 & req1 & ~ack0 & ~ack1 & EX(~ack0))

#PASS: (1)
#phi7.  If there are two simultaneous requests with no acknowledgment,
# and the one acknowledged in the next clock cycle is 0, then the next time
# two simultaneous requests occur, the one acknowledged will be 1.
AG(req0 & req1 & ~ack0 & ~ack1 ->
   AX(ack0 -> ~E (~req0 | ~req1 | ack0 | ack1 | EX(~ack1)) U
                   (req0 & req1 & ~ack0 & ~ack1 & EX(~ack1))))

#PASS: (2)
#phi8.  If there are two simultaneous requests with no acknowledgment,
# and the one acknowledged in the next clock cycle is 1, then the next time
# two simultaneous requests occur, the one acknowledged will be 0.
AG(req0 & req1 & ~ack0 & ~ack1 ->
   AX(ack1 -> ~E (~req0 | ~req1 | ack0 | ack1 | EX(~ack0)) U
                   (req0 & req1 & ~ack0 & ~ack1 & EX(~ack0))))

#PASS: (3)
#phi2.  If there are no requests, there will be no acknowledgments
# in the next clock cycle.
AG(~req0 & ~req1 -> AX(~ack0 & ~ack1))

#PASS: (4)
#phi3.  If 0 requests and 1 does not, 0 will be acknowledged
# in the next clock cycle.
AG(req0 & ~req1 -> AX ack0)

#PASS: (5)
#phi4.  If 1 requests and 0 does not, 1 will be acknowledged
# in the next clock cycle.
AG(~req0 & req1 -> AX ack1)

#PASS: (6)
#phi5.  If 1 requests and 0 is currently acknowledged, 1 will be
# acknowledged in the next clock cycle.
AG(req1 & ack0 -> AX ack1)

#PASS: (7)
#phi6.  If 0 requests and 1 is currently acknowledged, 0 will be
# acknowledged in the next clock cycle.
AG(req0 & ack1 -> AX ack0)

 
