#PASS: (0)
~hlock<0> & ~hbusreq<0> & ~hlock<1> & ~hbusreq<1> & ~hlock<2> & ~hbusreq<2> & ~hlock<3> & ~hbusreq<3> & hready

#PASS: (1-4)
AG (hlock<0> -> hbusreq<0>)
AG (hlock<1> -> hbusreq<1>)
AG (hlock<2> -> hbusreq<2>)
AG (hlock<3> -> hbusreq<3>)

#PASS: (5-8)
AG (~master<1> & ~master<0> -> (hbusreq<0> == busreq))
AG (~master<1> &  master<0> -> (hbusreq<1> == busreq))
AG ( master<1> & ~master<0> -> (hbusreq<2> == busreq))
AG ( master<1> &  master<0> -> (hbusreq<3> == busreq))

#PASS: (9)
~hmastlock & ~master<1> & ~master<0> & hgrant<0> & ~hgrant<1> & ~hgrant<2> &
~hgrant<3>;

#PASS: (10-13)
AG (hready -> ((hgrant<0>  -> AX(~master<1> & ~master<0>)) & (~hgrant<0>  -> AX~(~master<1> & ~master<0>))))
AG (hready -> ((hgrant<1>  -> AX(~master<1> &  master<0>)) & (~hgrant<1>  -> AX~(~master<1> &  master<0>))))
AG (hready -> ((hgrant<2>  -> AX( master<1> & ~master<0>)) & (~hgrant<2>  -> AX~( master<1> & ~master<0>))))
AG (hready -> ((hgrant<3>  -> AX( master<1> &  master<0>)) & (~hgrant<3>  -> AX~( master<1> &  master<0>))))

#PASS: (14-16)
AG (~hgrant<1> -> (A ~hgrant<1> W hbusreq<1>))
AG (~hgrant<2> -> (A ~hgrant<2> W hbusreq<2>))
AG (~hgrant<3> -> (A ~hgrant<3> W hbusreq<3>))

#PASS: (17)
AG (~hready -> AX ~arb.start)
