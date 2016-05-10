#PASS: (0) IDLE infinitely often.
AG AF(~State<1> & ~State<0>)

#FAIL: (1) Round=3 is inevitably followed by Round=0.
AG(Round<1> & Round<0> -> AF ~(Round<1> | Round<0>))

#PASS: (2) After Round=3, Round=0 is possible.
AG(Round<1> & Round<0> -> EF ~(Round<1> | Round<0>))

#PASS: (3) Phase=1 is inevitably followed by Phase=0...
AG(Phase -> AF ~Phase)

#FAIL: (4) ...but not the other way around
AG(~Phase -> AF Phase)

#PASS: (5) Instead, from Phase=0, Phase=1 is merely possible.
AG(~Phase -> EF Phase)

#PASS: (6) Round=2 is transient.
AG(Round<1> & ~Round<0> -> AF (~Round<1> | Round<0>))

#PASS: (7) Round=1 is transient.
AG(~Round<1> & Round<0> -> AF (Round<1> | ~Round<0>))

#PASS: (8) Round=3 may persist.
EF EG(Round<1> & Round<0>)
