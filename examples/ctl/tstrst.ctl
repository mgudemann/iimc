#PASS: (0)
AG EF (o & t & s)

#PASS: (1)
AG (o | ~t | s)

#PASS: (2)
AG(~(o | t | s) -> AX (~o & ~t & s))

#PASS: (3)
EF ~(o | t | s)

#FAIL: (4)
AF AG (o | t | s)
