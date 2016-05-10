# ACTL formulae from the CHARME99 paper by Katz, Grumberg, and Geist.
# Rewritten according to the syntax accepted by VIS and separated.
#
# The first two formulae describe the initial state of the arbiter.
# For ack0 and ack1 things are easy, but for robin we need to be a bit
# more clever, because we do not want to refer explicitly to internal
# variables.  A similar observation applies to the remaining formulae
# describing the steady-state behavior of the arbiter: Formulae phi7
# and phi8 describe round-robin arbitration.

# Author: Fabio Somenzi <Fabio@Colorado.EDU>

#PASS: (0)
# phi0-1.  In the initial state, no acknowledgment is issued.
~ack0 & ~ack1

#PASS: (1)
# phi0-2.  If robin does not get a chance to change, then the first
# time two simultaneous requests occur when no acknowledgment is issued, 0
# is acknowledged.
A (~req0<0> | ~req1<0> | ack0 | ack1) W
  (req0<0> & req1<0> & ~ack0 & ~ack1 & AX(ack0))

#PASS: (2)
# phi1.  Mutual exclusion.
AG(~ack0 | ~ack1)

#PASS: (3)
# phi2.  If there are no requests, there will be no acknowledgments
# in the next clock cycle.
AG(~req0<0> & ~req1<0> -> AX(~ack0 & ~ack1))

#PASS: (4)
# phi3.  If 0 requests and 1 does not, 0 will be acknowledged 
# in the next clock cycle.
AG(req0<0> & ~req1<0> -> AX ack0)

#PASS: (5)
# phi4.  If 1 requests and 0 does not, 1 will be acknowledged 
# in the next clock cycle.
AG(~req0<0> & req1<0> -> AX ack1)

#PASS: (6)
# phi5.  If 1 requests and 0 is currently acknowledged, 1 will be
# acknowledged in the next clock cycle.
AG(req1<0> & ack0 -> AX ack1)

#PASS: (7)
# phi6.  If 0 requests and 1 is currently acknowledged, 0 will be
# acknowledged in the next clock cycle.
AG(req0<0> & ack1 -> AX ack0)

#PASS: (8)
# phi7.  If there are two simultaneous requests with no acknowledgment,
# and the one acknowledged in the next clock cycle is 0, then the next time
# two simultaneous requests occur, the one acknowledged will be 1.
AG(req0<0> & req1<0> & ~ack0 & ~ack1 ->
   AX(ack0 -> A (~req0<0> | ~req1<0> | ack0 | ack1) W
                  (req0<0> & req1<0> & ~ack0 & ~ack1 & AX ack1)))

#PASS: (9)
# phi8.  If there are two simultaneous requests with no acknowledgment,
# and the one acknowledged in the next clock cycle is 1, then the next time
# two simultaneous requests occur, the one acknowledged will be 0.
AG(req0<0> & req1<0> & ~ack0 & ~ack1 ->
   AX(ack1 -> A (~req0<0> | ~req1<0> | ack0 | ack1) W
                  (req0<0> & req1<0> & ~ack0 & ~ack1 & AX ack0)))

#FAIL: (10)
A (~req0<0> | ~req1<0> | ack0 | ack1) W
  (req0<0> & req1<0> & ~ack0 & ~ack1 & AX(~ack0))