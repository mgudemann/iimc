#PASS: (0) Mutual exclusion
AG ~bad

#PASS: (1-4) Acknowledgements must be preceded by requests
AG(~u_ack<0> -> (A u_req<0> R ~u_ack<0>))
AG(~u_ack<1> -> (A u_req<1> R ~u_ack<1>))
AG(~u_ack<2> -> (A u_req<2> R ~u_ack<2>))
AG(~u_ack<3> -> (A u_req<3> R ~u_ack<3>))

#PASS: (5-14) Token-related invariants
AG((token<4>==token<1>) -> (token<0>==token<4>))
AG((token<0>==token<2>) -> (token<1>==token<0>))
AG((token<1>==token<3>) -> (token<2>==token<1>))
AG(!(token<2>==token<4>) -> (token<3>==token<2>))

AG((token<4>==token<2>) -> (token<1>==token<4>))
AG((token<4>==token<3>) -> (token<2>==token<4>))

AG(in_cs<0> -> (token<4> & ~token<3> & ~token<2> & ~token<1> & ~token<0>))
AG(in_cs<1> -> (token<4> & ~token<3> & ~token<2> & ~token<1> &  token<0>))
AG(in_cs<2> -> (token<4> & ~token<3> & ~token<2> &  token<1> &  token<0>))
AG(in_cs<3> -> (token<4> & ~token<3> &  token<2> &  token<1> &  token<0>))

#PASS: (15-23) Various accessibility properties
AG EF ~(token<4> | token<3> | token<2> | token<1> | token<0>)
AG EF (token<4> & token<3> & token<2> & token<1> & token<0>)
AG EF ~(u_ack<3> | u_ack<2> | u_ack<1> | u_ack<0>)
AG EF (u_ack<3> & u_ack<2> & u_ack<1> & u_ack<0>)
AG EF ~(in_cs<3> | in_cs<2> | in_cs<1> | in_cs<0>)
AG EF in_cs<0>
AG EF in_cs<1>
AG EF in_cs<2>
AG EF in_cs<3>

#PASS: (24-47) Clients do not have to enter the CS in order
AG EF(in_cs<0> & (E ~in_cs<1> U in_cs<2>))
AG EF(in_cs<1> & (E ~in_cs<2> U in_cs<3>))
AG EF(in_cs<2> & (E ~in_cs<3> U in_cs<0>))
AG EF(in_cs<3> & (E ~in_cs<0> U in_cs<1>))

AG EF(in_cs<0> & (E (~in_cs<1> & ~in_cs<2>) U in_cs<3>))
AG EF(in_cs<1> & (E (~in_cs<2> & ~in_cs<3>) U in_cs<0>))
AG EF(in_cs<2> & (E (~in_cs<3> & ~in_cs<0>) U in_cs<1>))
AG EF(in_cs<3> & (E (~in_cs<0> & ~in_cs<1>) U in_cs<2>))

AG(~u_req<1> & ~u_req<2> -> (E (~in_cs<1> & ~in_cs<2>) U in_cs<3>))
AG(~u_req<2> & ~u_req<3> -> (E (~in_cs<2> & ~in_cs<3>) U in_cs<0>))
AG(~u_req<3> & ~u_req<0> -> (E (~in_cs<3> & ~in_cs<0>) U in_cs<1>))
AG(~u_req<0> & ~u_req<1> -> (E (~in_cs<0> & ~in_cs<1>) U in_cs<2>))

AG(~u_req<0> -> (E ~in_cs<0> U in_cs<3>))
AG(~u_req<1> -> (E ~in_cs<1> U in_cs<3>))
AG(~u_req<2> -> (E ~in_cs<2> U in_cs<3>))
AG(~u_req<0> -> (E ~in_cs<0> U in_cs<2>))
AG(~u_req<1> -> (E ~in_cs<1> U in_cs<2>))
AG(~u_req<3> -> (E ~in_cs<3> U in_cs<2>))
AG(~u_req<0> -> (E ~in_cs<0> U in_cs<1>))
AG(~u_req<2> -> (E ~in_cs<2> U in_cs<1>))
AG(~u_req<3> -> (E ~in_cs<3> U in_cs<1>))
AG(~u_req<1> -> (E ~in_cs<1> U in_cs<0>))
AG(~u_req<2> -> (E ~in_cs<2> U in_cs<0>))
AG(~u_req<3> -> (E ~in_cs<3> U in_cs<0>))

#PASS: (48-51) Starvation freedom (requires fairness constraints)
AG(u_req<0> -> AF in_cs<0>)
AG(u_req<1> -> AF in_cs<1>)
AG(u_req<2> -> AF in_cs<2>)
AG(u_req<3> -> AF in_cs<3>)
