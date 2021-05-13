module foo (input CLK, input nRST);

`define clk_rst

logic a, a1, a2, AD, ALU,
b, busData,
c, clock, cmd, cnt, COL, cond, CRS,
d, dAck, delay, dif, dif_clk, dif_clk1, dif_gnt0, dif_gnt1, dif_gnt2, dif_out, dif_out0, dif_out1, dif_read, dif_req, dif_write, done,
e, empty, e_r, fibonacci1, framj164ength, full, gnt, grant, grants, HLT, INIT, J,
j101, j102, j104, j105, j110, j111, j112, j113, j114, j116, j117, j118, j119, j120, j121,
j122, j123, j124, j134, j135, j139, j141, j143, j144, j147, j148, j152, j154, j164, j165,
j173, j174, j179, j183, j187, j188, j192, j195, j198, j200, j202, j203, j209, j224, j232,
j237, j238, j239, j249, j264, j265, j266, j268, j270, j272, j273, j275, j276, j278, j281,
j282, j283, j285, j286, j287, j288, j292, j293, j296, j297, j2992, j303, j304, j305, j307,
j308, j309, j310, j311, j312, j314, j316, j317, j320, j321, j323, j324, j325, j327, j328, j329,
j341, j346, j347, j348, j350, j352, j354, j355,
K, kind, miiD, miiEN, miiER, minFrameSize, myst, myState, N, NibbleCnt,
out, outstanding, pgnt, pop, preq, push, Q, Qbar, ramAddr, ramData, rdy, read, reading, ready, req, reqs, reset, RST_, RST, RXD,
s, s1, s2, SdfL, seq, slew, stall, threshold, TRUE, TXD, TX_j154, vld, write, writing,
clk, dif_clk0, dif_rst, enable,
j107, j201, j280, j326,
resetting, rst, T2,
 x;

    assert property (@(posedge dif_clk) ((dif_req ##[1:6] dif_gnt0) and (dif_req ##[1:9] dif_gnt1)) ##0 dif_gnt2);
    assert property (@(posedge dif_clk) ((dif_req) and dif_req) ##0 dif_gnt2);
    assert property (@(posedge dif_clk) ((dif_req ##5 dif_gnt0) and (dif_req ##8 dif_gnt1)) ##0 dif_gnt2);
assert property (@ ( posedge j326) ( ( j239 && j327 && j347 ) throughout( $rose ( j327) ##44 j324[=2:$])) ##55 !j327);

    assert property (@(posedge dif_clk0) ##1 dif_out0 ##1 @(posedge dif_clk1) dif_out1);
    assert property (@(posedge clk) disable iff (~rst) out);
    assert property (@(posedge dif_clk) disable iff (dif_rst) dif_out);
    assert property (@(posedge dif_clk) (dif_req ##5 dif_gnt0) intersect (dif_req ##[1:9] dif_gnt1));
    assert property (@(posedge dif_clk) (dif_req ##5 dif_gnt0) or (dif_req ##3 dif_gnt1));
    assert property (@(posedge clk) a ##1 b);
    assert property (@(posedge clk) b ##1 a [*2:10] ##1 b);
    assert property (@(posedge clk) b ##1 a [->2:10] ##1 b);
    assert property (@(posedge clk) b ##1 a [=2:10] ##1 b);


    assert property (@(posedge clk) disable iff (a) b |-> c );
    assert property (@(posedge clk) a || b );
    assert property (@(posedge clk) a iff b );
    assert property (@(posedge clk) read |=> write );
    assert property (@(posedge clk) !(read & write));
    assert property (@(posedge clk) a |-> b);
    assert property (@(posedge dif_clk) dif_read |=> dif_read);
    assert property (@(posedge clk) (a == 1));
    assert property (@(posedge dif_clk) !(dif_read & dif_write));
    assert property (@(posedge dif_clk) dif_read ##1 dif_write);


always @(posedge CLK) begin
    assert (j111 === $sampled(b));
    assert final(j111 > d);
end
    sequence seq99;
        @(posedge dif_clk) dif_req ##5 dif_gnt0;
    endsequence
    sequence seq100;
        @(posedge dif_clk) (dif_req ##5 dif_gnt0) intersect (dif_req ##[1:9] dif_gnt1);
    endsequence
always @(posedge dif_clk) begin
    assert property (dif_gnt2 throughout seq);
    assert property (seq99);
    assert property (dif_gnt2 throughout seq100);
end
assert property (@(negedge CLK) ##[0:2] j111 == 1);
assert property (@(posedge CLK) ##[1:9] j111 && j112);
assert property (@(posedge CLK) ##1 j111 && j112);
assert property (@(posedge CLK) ##1 j111 && j112 [*5]);

always @(posedge CLK) begin
assert property (j111 ##[1:3] b);
//assert property (j111 ##1 (b[*0] ##0 c));
assert property (j111 ##1 b[*0] ##1 c);
assert property (j111 ##1 b[=1] ##1 c);
assert property ((j111 ##1 a2/2));
assert property (@(CLK) disable iff (nRST) !nRST |=> (j111 == 1));
assert property (`clk_rst j111 == 0 == empty);
assert property (`clk_rst j111 == 0 |-> empty);
assert property (`clk_rst j111 |-> !push);
assert property (`clk_rst j111 && !stall |=>  j144 ==  j111);
assert property (`clk_rst $rose(j111) |-> j144 ==  j111);
assert property (`clk_rst j111 |=> $stable(j111));
assert property ((clock |-> j111 |-> K |-> (Q==Qbar) ));
assert property (clock |-> ( (j111 == Q) && (J== ~K) ));
assert property ( disable iff(!j111) ($rose(j287) |=> j287[*2]));
assert property (disable iff (j111) @( posedge CLK) $rose(req) |-> j293 #-# ( j282 or j122));
assert property (disable iff (j111 || COL && !j224) $rose(j316) |-> ##14 TXD == SdfL);
assert property (disable iff (j111 || j224) !COL ##1 COL[*1:$] |-> CRS);
assert property (disable iff (j111 || j224) (j316 && (j320 != 0) && j314) ##1 !j316 |-> (TX_j154 != j134));
assert property (disable iff (j111 || j224) !miiEN ##1 miiEN |-> ##10 (CRS[*1:$]) ##1 !miiEN);
assert property (disable iff(j111  || j224) (NibbleCnt > minFrameSize*2) && miiEN |-> !$rose(COL));
assert property (disable iff(j111 || j314  && !j224) miiEN ##1 !miiEN |-> (j154 == j134));
assert property (disable iff(j111) ((miiEN ^ miiEN) == 0) && ((miiD ^ miiD) == 0) && ((miiER ^ miiER) == 0) && ((COL ^ COL) == 0) && ((CRS ^ CRS) == 0) );
assert property (disable iff (j111) not (!j316 && j317));
assert property ($fell(j111) && cmd == HLT |-> strong(vld[->1] ##0 cmd == RST));
assert property (j111 ##1 j111[->2] ##1 j122);
assert property ((j111 && (!COL || j224)) throughout ( kind within ( $rose(miiEN) ##1 (miiEN)[*1:$] ) ##1 (!miiEN && (cnt == framj164ength))));
assert property ((j111 && (!COL || j224)) throughout kind within ( $rose(miiEN) ##1 (miiEN)[*1:$] ) ##1 (!miiEN && (cnt == framj164ength)));
assert property ( j111 && (!j275 && j276 && (RXD == 1)) );
assert property (((j111 && miiEN && !j224) throughout ($rose(miiEN) ##0 COL[->1])) ##1 !miiEN );
assert property ((j111 && miiEN && !j224) throughout ($rose(miiEN) ##0 (COL && cnt)[->1]));
assert property ( j111 throughout ( !j275 ##1 (j275[*1:$]) ##0 j276 ));
assert property (j111 throughout (miiEN ##1 !miiEN[*24] ##1 miiEN) );
assert property ( !j111 ##1 (j316[*1:$]) ##0 j317 );
assert property ((j111 && out) |=> (out==1));
assert property ((j111) |=> (out==$past(out)+1) );
assert property (req ##2 gnt);
assert property ($rose(vld) && cmd == HLT |-> !outstanding);
assert property ($rose(vld) |-> !outstanding);
assert property ($rose(vld) |-> strong(##[0:10] rdy));
assert property ($rose(vld) |=> strong(vld within rdy[->1]));
assert property (vld[->1] ##0 (cmd == INIT));
assert property (vld |=> !$changed(cmd));
assert property (vld |-> done[->1]);
end

assert property (@(negedge CLK) j111 ##[2:5] e);
assert property (@(negedge CLK) j111 |-> ##1 (ready==1));
assert property (@(posedge CLK) disable iff (!nRST) (j122 && !j111) |=> $stable(j111));
assert property (@(posedge CLK) (j111==1) ##1 (c>1));
assert property (@(posedge CLK) (j111>1) ##1 (c < 1));
assert property (@(posedge CLK) j111 ##[1:4] a);
assert property (@(posedge CLK) j111 ##1 b ##1 c);
assert property (@( posedge CLK) j111 ##1 b |=> c);
assert property (@(posedge CLK) (j111 ##1 b) iff (c ##1 d));
assert property (@(posedge CLK) (j111 ##1 b) implies (c ##1 d));
assert property (@(posedge CLK) j111 #-# b);
assert property (@(posedge CLK) ((j111 && b) || !c));
assert property (@(posedge CLK) j111 |-> strong(s1));
assert property (@(posedge CLK) j111 |-> weak(s1));
assert property (@(posedge CLK) j111 |-> a);
assert property (@(posedge CLK) disable iff (!j107) j111 |-> (!j312));
assert property (@(posedge CLK) disable iff (!j107) (j111[=1]) within (j304[->1]) );
assert property (@(posedge CLK) disable iff (!j107) $rose(j111) |=> (!j312) throughout (j304[->1]));
assert property (@(posedge CLK) disable iff (j201 != 0) j111 < slew);
assert property (@(posedge CLK) disable iff(j201 != 0) j112 > j308 && j112 < j307);
assert property (@(posedge CLK) disable iff (j201 != 1 && !enable) j111 > slew);
assert property (@(posedge CLK) disable iff(j201 != 1) j112 < j308 || j112 > j307);
assert property (@(posedge CLK) disable iff(j201 != 1) j112 >= threshold);
assert property (@(posedge CLK) disable iff (!nRST) ##1 $stable(j111));
assert property (@(posedge CLK) disable iff (!nRST) j111 ##1 c);
assert property (@(posedge CLK) disable iff (!nRST) (j112==1) |=> (j111==1));
assert property (@(posedge CLK) disable iff (!nRST) (j122==1) |-> (j111==1));
assert property (@(posedge CLK) disable iff (!nRST) j111 ? j272 + 1 : j272 );
assert property (@(posedge CLK) disable iff (!nRST) (!j111) |-> (j272 == j195));
assert property (@(posedge CLK) disable iff (!nRST) j111 |-> (j249 == j309));
assert property (@(posedge CLK) disable iff (!nRST) j111 |-> !j350);
assert property (@(posedge CLK) disable iff (!nRST) not (j111[->3] within 1[*10]) );
assert property (@(posedge CLK) disable iff (!nRST) not (j111[->3] within 1[*10]) );
assert property (@(posedge CLK) disable iff (!nRST) not(j111 ##0 (!grant throughout grant[->2])) );
assert property (@(posedge CLK) disable iff (!nRST) $onehot0(j111) );
assert property (@(posedge CLK) disable iff (!nRST) !((j111 != 1) && (j270 > 1)));
assert property (@(posedge CLK) disable iff (!nRST) $fell(j111) |-> !($isunknown(AD) || $isunknown(j116)) );
assert property (@(posedge CLK) disable iff (!nRST) $fell(j111) |-> !($isunknown(j116)) [*0:$] ##0 $rose(j192));
assert property (@(posedge CLK) disable iff (!nRST) (!j111 && !j310) |-> !($isunknown(AD) || $isunknown(j116)) );
assert property (@(posedge CLK) disable iff (!nRST) !j111 |-> !j152);
assert property (@(posedge CLK) disable iff(!nRST) j112 |-> nexttime[10] j111);
assert property (@(posedge CLK) disable iff (!nRST) $onehot(j111) && reqs |-> grants);
assert property (@(posedge CLK) disable iff (reset) $rose(j111) |=> (j111) [*2:4] ##1 $fell(j111));
assert property (@(posedge CLK) disable iff (reset) $rose(j111) |=> (j111 && !dAck) [*1:3] ##1 $rose (dAck) ##1 $fell (j111));
assert property (@(posedge CLK) disable iff (reset) $rose(j111) |=> (!$isunknown(j122) && $stable(j122)) [*1:$] ##0 $rose(dAck));
assert property (@(posedge CLK) disable iff (!nRST) $rose(j111) |-> !j203);
assert property (@( posedge CLK) disable iff( resetting) !( j101 || j273 || j173) |=> j297);
assert property (@( posedge CLK) disable iff( resetting) !( j101 || j273 || j173) |=> $stable( j303));
assert property (@( posedge CLK) disable iff( resetting) ( ( j111 == 1) ##1 ( ( ( j139 == 1) || ( j139 == 1)) && !$stable( j105))) |-> ( j105 >= $past(j105)) ?  ( ( j105 - $past( j105)) == ( j328/8)) : ( ( $past( j105) - j105) == ( j328/8)));
assert property (@( posedge CLK) disable iff( resetting) j111 && j102 && !j296 |=> j102);
assert property (@( posedge CLK) disable iff( resetting) j111 && j102 && !j296 && !j348  |=> $stable( j147));
assert property (@( posedge CLK) disable iff( resetting) ( (!j111) [->1]));
assert property (@( posedge CLK) disable iff( resetting) (j111 && j139 == 1) ##1 j141 |-> ( j139 == 1));
assert property (@( posedge CLK) disable iff( resetting) j111 && j297 && !( j101 || j273 || j173) |=> j297);
assert property (@( posedge CLK) disable iff( resetting) j111 && j297 && ( j139 == 1) && j101 |=> j141 throughout( j297[->1]));
assert property (@( posedge CLK) disable iff( resetting) j111 throughout ( ( j139 == 1) ##1 ( ( ( j139 == 1) || ( j139 == 1)) && !$stable( j105))) |-> ( j105 >= $past(j105)) ?  ( ( j105 - $past( j105)) == ( j328/8)) : ( ( $past( j105) - j105) == ( j328/8)));
assert property (@( posedge CLK) disable iff( resetting) not( j111 && j174));
assert property (@(posedge CLK) disable iff (nRST) j111 ##[2:3] !j111);
assert property (@(posedge CLK) disable iff (!nRST) (j111==0 |-> j112));
assert property (@(posedge CLK) disable iff (nRST) j112 until j111);
assert property (@(posedge CLK) disable iff (!nRST) j112 |-> !j188);
assert property (@(posedge CLK) disable iff (!nRST) (j112 && j188 && !j187 |=> $stable(j354)));
assert property (@(posedge CLK) disable iff (!nRST) (j111 & !j135) |=> j111 === $past(j122));
assert property (@ (posedge CLK) disable iff(!nRST) j111  |=> $stable(cond) until j111);
assert property (@(posedge CLK) disable iff(nRST) (j111 == j148));
assert property (@(posedge CLK) disable iff (!nRST) (j111 == 1) |-> strong(##[1:$] (myState == 1)));
assert property (@(posedge CLK) j111 |-> j111);
assert property (@(posedge CLK) (j111 ##0 (j124)));
assert property (@(posedge CLK) (j111 ##1 (j124)));
assert property (@(posedge CLK) (j111 and (j124)));
assert property (@(posedge CLK) $fell(j111) |-> ready [*3]);
assert property (@(posedge CLK) $fell(j111) ##1 $rose(j111));
assert property (@(posedge CLK) ($fell( !nRST )) |-> ((j121 && j265) throughout ##[0:$] j111));
assert property (@(posedge CLK) j111 or (1 |=> j232 ));
assert property (@ ( posedge CLK) (j111) |-> ##3 j112);
assert property (@(posedge CLK) (!j121 && !reset) |-> ##1 j121);
assert property (@(posedge CLK) !j121 && !reset |-> !j117 && (j104 == 1) or !j118 && (j104 == 1) || !j119 && (j104 == 1) || !j120 && (j104 == 1));
assert property (@(posedge CLK) (!j121 && !reset) |-> ramAddr == (j104));
assert property (@(posedge CLK) j143 |=> j111);
assert property (@(posedge CLK) j179 [*20]);
assert property (@(posedge CLK) (j200 && j114 ) |-> ##[0:34] j165);
assert property (@(posedge CLK) (!j265 && !reset) |-> (##1 j265));
assert property (@(posedge CLK) j355 |=> j268[*1:$] ##1 j198[*1:$] ##1 j355);
assert property (@(posedge CLK) preq |-> ##2 pgnt);
assert property (@(posedge CLK) reading |-> ##1 ((j265 && (ramAddr === j104))[*2]));
assert property (@(posedge CLK) reading |-> ##3 (busData === j266));
assert property (@(posedge CLK) reading |-> (!j121)[*2] ##1 !j121);
assert property (@(posedge CLK) !reset ##[0:1] (j124) ##[0:1] (j124));
assert property (@(posedge CLK) (!reset) |-> (##0 (j122)));
assert property (@(posedge CLK) (!reset and (j124) ##1 (j124)));
assert property (@(posedge CLK) (!reset and (j124) and (j124)));
assert property (@(posedge CLK) $rose(j111) |-> ##[1:$] $rose(j321));
assert property (@(posedge CLK) $rose(j111) ##[1:$] $rose(j321));
assert property (@(posedge CLK) ( ($rose( j117 )) || ($rose( j118 )) || ($rose( j119 )) || ($rose( j120 )) ) |-> (j110) [*1:$] ##1 j111);
assert property (@(posedge CLK) ($rose( j121 )) |-> j121 [*1:$] ##1 j111);
assert property (@(posedge CLK) $rose( j265 ) |-> j265 [*0:$] ##1 j111);
assert property (@(posedge CLK) $rose(req) ##[1:3] $rose(j122));
assert property (@(posedge CLK) !(RST_) |-> ##1 (Q == 1));
assert property (@(posedge CLK) (!nRST |-> (j264==0 && j354==0 && j111==1 && j112==0)));
assert property (@(posedge CLK) (nRST throughout myst));
assert property (@(posedge CLK) !s ##[0:3] j305);
assert property (@(posedge CLK) s1 and s2);
assert property (@(posedge CLK) s1 within s2);
assert property (@(posedge CLK) writing |-> ##2 ((ramData === j352) [*2]));
assert property (@(posedge CLK) writing |-> j265 [*3] ##1 !j265);
assert property (@(posedge clock) j164 |-> e_r);
assert property (@(posedge clock) (TRUE) ##[1:2] ((ALU == $past(ALU) + 1)));
assert property (@( posedge j123 ) (~j265) |->  (~j123 && ~j265));
assert property (@( posedge j123 ) j265 |-> (~j123 && j265));
assert property (@(posedge j280) 1[*0:$] ##1 ($rose(j321) && (j111 == 0)));
assert property (@ ( posedge j326) ( j239 && j327 && j347 ) throughout( $rose ( j327) ##1 j323[=9]));
assert property (@ ( posedge j326) ( ( j239 && j327 && j347 ) throughout( $rose ( j327) ##1 ( j324)[=1])) ##1 !j327);
assert property (@ ( posedge j326) ( ( j239 && j327) throughout( $rose ( j327) ##0 ( ( j324 && !j347) [->1]) ##1 ( ( j324)&&j347[=1]))) ##1 !j327);
assert property (@ ( posedge j326) ( j239  && j327) throughout( ( $rose( j327) ##0 ( !j346)[*5] ##1 j346)));
assert property (@ ( posedge j326) ( j239  && j327) throughout( ( $rose ( j346) || ( j325 && j346)) ##1 (!( j325 || j341 || j329))[*(10-1)] ##1 ( j325 || j341 || j329)));
assert property (@ ( posedge j326) j239 throughout( ( j327 && !j347 ) throughout( $rose ( j327) ##1 j323[=9])));
endmodule
