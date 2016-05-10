#PASS: (0)
A gate R ~r1
#FAIL: (1)
A ~r1 U gate
#PASS: (2)
AG(r0 -> AX r1)
#PASS: (3)
AG((~phi -> AX phi) & (phi -> AX ~phi))
#PASS: (4)
A gate R ~r0
#FAIL: (5)
A ~r0 U gate
#PASS: (6-9)
AG((phi & ~r0) -> AX ~r0)
AG((phi & r0) -> AX r0)
AG((~phi & ~r1) -> AX ~r1)
AG((~phi & r1) -> AX r1)
