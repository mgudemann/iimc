#PASS: Mutual exclusion
AG ~(u_ack<0> & u_ack<1>)

#PASS: acknowledgements must be preceded by requests
AG(~u_ack<0> -> (A u_req<0> R ~u_ack<0>))
AG(~u_ack<1> -> (A u_req<1> R ~u_ack<1>))

#PASS: No starvation (needs fairness constraints)
AG(u_req<0> -> AF u_ack<0>)
AG(u_req<1> -> AF u_ack<1>)

#PASS: Another form of no starvation
AG AF(u_req<0> -> u_ack<0>)
AG AF(u_req<1> -> u_ack<1>)

#PASS: Yet another property related to no starvation
AG(u_req<1> -> AF ~u_ack<0>)
AG(u_req<0> -> AF ~u_ack<1>)
