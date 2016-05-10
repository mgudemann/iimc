################################################################################
#FAIL: (0)
#Always at the next state delayed version of the same signal should have its
#previous value.
#===============================================================================
AG(IStall_s1 -> AX IStall_s2)

################################################################################
#FAIL: (1)
#===============================================================================
AG(ADynamicBit_s2r -> AX ADynamicBit_s1e)

################################################################################
#FAIL: (2) even when only MemStall_s1 = 0
#===============================================================================
AG(PrevState_s2<3> & PrevState_s2<2> & PrevState_s2<1> & PrevState_s2<0> ->
  AF(PresState_s1<1> & 
      ((~PresState_s1<3> & ~PresState_s1<2> & ~PresState_s1<0>) |
       (PresState_s1<3> & PresState_s1<2> & PresState_s1<0>)
      )
  )
)

################################################################################
#PASS: (3) when added register variable Match_s3r and ICacheLineValid_s3r
#to keep the values respectively and initialized them to 1.
# This property is related with the instruction cache refilling state machine.
# From all the states where an instruction cache miss occurs there exist a
# path to a $REFETCH$ state, meaning that instruction cache has been refilled.
# The reason to use $EF$ instead of $AF$ is that whenever a reset occurs this
# may not be accomplished since you have to return back to the $CACHEHIT$
# state. While checking for this formula VIS gave the error "Node
# ICacheMiss\_v2r is not driven only by latches and constants" so I added
# register variables $Match\_s3r$ and $ICacheLineValid\_s3r$ to keep the
# values respectively and initialized them to 1.
#===============================================================================
AG(ICacheMiss_v2r -> 
  EF(PrevState_s2<3> & PrevState_s2<2> & PrevState_s2<1> & PrevState_s2<0>)
)

################################################################################
#PASS: (4)
# This property attempts to say that always a cache refill operation should
# be completed.
#===============================================================================
AG(~PresState_s1<3> & ~PresState_s1<2> & PresState_s1<1> & ~PresState_s1<0> ->
  EF(PresState_s1<3> & PresState_s1<2> & PresState_s1<1> & PresState_s1<0>)
)

################################################################################
#PASS: (5)
# If the present state is different than $CACHEHIT$ state(which means there
# is no cache miss) then we must have a cache miss and instruction pipeline
# should be stalled unless a higher priority event takes place like resetting.
#===============================================================================
AG(
  ~(~PresState_s1<3> & ~PresState_s1<2> & PresState_s1<1> &
     ~PresState_s1<0>) -> EF IStall_s1
)

################################################################################
#PASS: (6)
#===============================================================================
AG(~IFetchStall_s2 -> EF ~(~PrevState_s2<3> & ~PrevState_s2<2> &
  PrevState_s2<1> & ~PrevState_s2<0>))

################################################################################
#PASS: (7)
#Similar to the above formula
#===============================================================================
AG(~(~PrevState_s2<3> & ~PrevState_s2<2> & PrevState_s2<1> & ~PrevState_s2<0>) -> EF ~IFetchStall_s2)

################################################################################
#PASS: (8)
# WriteCache\_s2 becomes one in some paths before WriteTag\_s2 becomes one.
# Again not for all states because if a reset arrives then $WriteCache\_s2$
# may not become one since we wont be in instruction transfer states.
#===============================================================================
E ~WriteTag_s2 U (WriteCache_s2 & ~WriteTag_s2)

