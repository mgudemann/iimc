#PASS: (0-15) persistent requests are eventually acknowledged
AG AF(lreq<0>  -> ack<0>)
AG AF(lreq<1>  -> ack<1>)
AG AF(lreq<2>  -> ack<2>)
AG AF(lreq<3>  -> ack<3>)
AG AF(lreq<4>  -> ack<4>)
AG AF(lreq<5>  -> ack<5>)
AG AF(lreq<6>  -> ack<6>)
AG AF(lreq<7>  -> ack<7>)
AG AF(lreq<8>  -> ack<8>)
AG AF(lreq<9>  -> ack<9>)
AG AF(lreq<10> -> ack<10>)
AG AF(lreq<11> -> ack<11>)
AG AF(lreq<12> -> ack<12>)
AG AF(lreq<13> -> ack<13>)
AG AF(lreq<14> -> ack<14>)
AG AF(lreq<15> -> ack<15>)

#PASS: (16-31) The token goes round and round...
AG AF c0.token
AG AF c1.token
AG AF c2.token
AG AF c3.token
AG AF c4.token
AG AF c5.token
AG AF c6.token
AG AF c7.token
AG AF c8.token
AG AF c9.token
AG AF c10.token
AG AF c11.token
AG AF c12.token
AG AF c13.token
AG AF c14.token
AG AF c15.token

#PASS: (32-47) Another version of the previous one
AG AF (
  c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & c11.token & ~c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & c12.token & ~c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & c13.token & ~c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & c14.token &
  ~c15.token
)
AG AF (
  ~c0.token & ~c1.token & ~c2.token & ~c3.token & ~c4.token &
  ~c5.token & ~c6.token & ~c7.token & ~c8.token & ~c9.token &
  ~c10.token & ~c11.token & ~c12.token & ~c13.token & ~c14.token &
  c15.token
)

#PASS: (48-63)
AG EF (c0.waiting & c0.token)
AG EF (c1.waiting & c1.token)
AG EF (c2.waiting & c2.token)
AG EF (c3.waiting & c3.token)
AG EF (c4.waiting & c4.token)
AG EF (c5.waiting & c5.token)
AG EF (c6.waiting & c6.token)
AG EF (c7.waiting & c7.token)
AG EF (c8.waiting & c8.token)
AG EF (c9.waiting & c9.token)
AG EF (c10.waiting & c10.token)
AG EF (c11.waiting & c11.token)
AG EF (c12.waiting & c12.token)
AG EF (c13.waiting & c13.token)
AG EF (c14.waiting & c14.token)
AG EF (c15.waiting & c15.token)

#PASS: (64-79)
AG EF EG ack<0>
AG EF EG ack<1>
AG EF EG ack<2>
AG EF EG ack<3>
AG EF EG ack<4>
AG EF EG ack<5>
AG EF EG ack<6>
AG EF EG ack<7>
AG EF EG ack<8>
AG EF EG ack<9>
AG EF EG ack<10>
AG EF EG ack<11>
AG EF EG ack<12>
AG EF EG ack<13>
AG EF EG ack<14>
AG EF EG ack<15>

#FAIL: (80-95)
AG AF EG ack<0>
AG AF EG ack<1>
AG AF EG ack<2>
AG AF EG ack<3>
AG AF EG ack<4>
AG AF EG ack<5>
AG AF EG ack<6>
AG AF EG ack<7>
AG AF EG ack<8>
AG AF EG ack<9>
AG AF EG ack<10>
AG AF EG ack<11>
AG AF EG ack<12>
AG AF EG ack<13>
AG AF EG ack<14>
AG AF EG ack<15>
