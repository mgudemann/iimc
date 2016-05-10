#PASS: (0) players 0 and 1 cannot both win.
AG !(win & lose)
#PASS: (1) the first player may win from a winning position.
AG((~turn & winning) -> EF win)
#PASS: (2) the second player may win from a winning position.
AG((turn & winning) -> EF lose)
#FAIL: (3) the first player always wins from a winning position.
AG((~turn & winning) -> AF win)
#PASS: (4) the second player always wins from a winning position.
AG((turn & winning) -> AF lose)
#PASS: (5) termination is inevitable.
AF(win | lose)
#PASS: (6)
AG(turn & winning -> AG(turn == winning))
#PASS: (7)
AG(winning -> AX ~win)
#PASS: (8)
AG(~win & (turn == winning) -> AX(~win))
#PASS: (9)
AG(turn & winning -> AG((turn == winning) & ~win))
#PASS: (10)
AG(turn & winning -> AG(~win))
#PASS: (11)
AG(winning -> ~win)
#PASS: (12)
AG(turn -> ~win)
#PASS: (13)
AG(~turn & ~winning -> AX(valid -> winning))
#PASS: (14)
AG(~load<2> & ~load<1> & ~load<0> & ~turn & ~winning ->
  AG(turn == winning))
