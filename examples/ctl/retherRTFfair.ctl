#PASS: (0)
#CC: Token rotation cycle completion.
AG(start -> AX(A ~start U cycle))

#PASS: (1-4)
#RT0-3: Bandwidth guarantee for RT nodes.
AG(res<*0*> -> ~(EG(~rt<*0*>) |
                 E (cycle -> EX(E ~rt<*0*> U cycle)) U rt<*0*>))
AG(res<*1*> -> ~(EG(~rt<*1*>) |
                 E (cycle -> EX(E ~rt<*1*> U cycle)) U rt<*1*>))
AG(res<*2*> -> ~(EG(~rt<*2*>) |
                 E (cycle -> EX(E ~rt<*2*> U cycle)) U rt<*2*>))
AG(res<*3*> -> ~(EG(~rt<*3*>) |
                 E (cycle -> EX(E ~rt<*3*> U cycle)) U rt<*3*>))

#PASS: (5)
#RTT: At least one RT data transmission in each cycle.
AG(start -> ~E ~(rt<*0*> | rt<*1*> | rt<*2*> | rt<*3*>) U cycle)

#PASS: (6)
#NRT: At least one NRT data transmission in each cycle.
AG(start -> ~E ~(nrt<*0*> | nrt<*1*> | nrt<*2*> | nrt<*3*>) U cycle)

#PASS: (7)
#T3T: A total of three data transmissions in each cycle.  This property
# has a number of vacuous passes with either policy.  See below for
# strengthened properties that pass non vacuously for one policy, but fail
# for the other.
AG(start -> ~E ~((rt<*0*> | rt<*1*> | rt<*2*> | rt<*3*>) | (nrt<*0*> | nrt<*1*> | nrt<*2*> | nrt<*3*>)) U EX(E ~((rt<*1*> | rt<*2*> | rt<*3*>) | (nrt<*0*> | nrt<*1*> | nrt<*2*> | nrt<*3*>)) U EX(E ~((rt<*0*> | rt<*1*> | rt<*2*> | rt<*3*>) | (nrt<*0*> | nrt<*1*> | nrt<*2*> | nrt<*3*>)) U cycle)))

#PASS: (8)
#RTF: RT-first property.
AG((nrt<*0*> | nrt<*1*> | nrt<*2*> | nrt<*3*>) -> ~E ~cycle U (rt<*0*> | rt<*1*> | rt<*2*> | rt<*3*>))

#PASS: (9-12)
#At most one reservation per cycle for each node.
AG~(res<*0*> & EX E ~cycle U res<*0*>)
AG~(res<*1*> & EX E ~cycle U res<*1*>)
AG~(res<*2*> & EX E ~cycle U res<*2*>)
AG~(res<*3*> & EX E ~cycle U res<*3*>)

#PASS: (13-16)
#All nodes with reserved bandwidth at the begginning of the cycle
# perform their RT transmission during the cycle.
AG(start & node<*0*> -> ~E ~rt<*0*> U cycle)
AG(start & node<*1*> -> ~E ~rt<*1*> U cycle)
AG(start & node<*2*> -> ~E ~rt<*2*> U cycle)
AG(start & node<*3*> -> ~E ~rt<*3*> U cycle)

#PASS: (17-19)
#RT requests are served in ID order.
AG~(rt<*1*> & E ~cycle U rt<*0*>)
AG~(rt<*2*> & E ~cycle U rt<*1*>)
AG~(rt<*3*> & E ~cycle U rt<*2*>)

#PASS: (20)
#This stronger version of the T3T property holds for the RTF policy.
# It says that in each cycle there are exactly three transmissions: The first
# is always an RT transmission; the last is always an NRT transmission; and
# the middle one can be anything but an RT transmission by Node 0.
AG(start -> ~E ~(rt<*0*> | rt<*1*> | rt<*2*> | rt<*3*>) U EX(E ~((rt<*1*> | rt<*2*> | rt<*3*>) | (nrt<*0*> | nrt<*1*> | nrt<*2*> | nrt<*3*>)) U EX(E ~(nrt<*0*> | nrt<*1*> | nrt<*2*> | nrt<*3*>) U cycle)))

#FAIL: (21)
#This stronger version of the T3T property holds for the SQO policy.
# It says that in each cycle there are exactly three transmissions: The first
# cannot be by Node 3; the second cannot be rt<*0*> or nrt<*3*>; and the
# the third cannot be by Node 0.
AG(start -> ~E ~(rt<*0*> | rt<*1*> | rt<*2*> | nrt<*0*> | nrt<*1*> | nrt<*2*>) U EX(E ~(rt<*1*> | rt<*2*> | rt<*3*> | nrt<*0*> | nrt<*1*> | nrt<*2*>) U EX(E ~(rt<*1*> | rt<*2*> |  rt<*3*> | nrt<*1*> | nrt<*2*> | nrt<*3*>) U cycle)))


