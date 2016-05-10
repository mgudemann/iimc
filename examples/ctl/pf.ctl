#FAIL: (0) it is always possible to return to the state in which the
#       low priority process is idle
AG EF ~(meteo.state<1> | meteo.state<0>)

#FAIL: (1) liveness of the bus management task.
AG(~busMgmt.state<1> & busMgmt.state<0> -> 
  AF(~busMgmt.state<1> & ~busMgmt.state<0>))

#FAIL: (2) liveness of the meteo task.
AG(~meteo.state<1> & meteo.state<0> -> 
  AF(~meteo.state<1> & ~meteo.state<0>))
