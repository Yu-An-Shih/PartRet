// WISHBONE interface
// Rule 3.20
//assert property (@(posedge clk_i) (rst_i |=> !wb0_cyc_o && !wb0_stb_o));
//assume property (@(posedge clk_i) (rst_i |=> !wb0_cyc_i && !wb0_stb_i));
//assert property (@(posedge clk_i) (rst_i |=> !wb1_cyc_o && !wb1_stb_o));
//assume property (@(posedge clk_i) (rst_i |=> !wb1_cyc_i && !wb1_stb_i));

// Observation 3.10, conflicts with Permission 3.35?
assume property (@(posedge clk_i) (!wb0_stb_o |-> !wb0_ack_i && !wb0_err_i && !wb0_rty_i)); // master 0
assert property (@(posedge clk_i) (!wb0_stb_i |-> !wb0_ack_o && !wb0_err_o && !wb0_rty_o)); // slave 0
assume property (@(posedge clk_i) (!wb1_stb_o |-> !wb1_ack_i && !wb1_err_i && !wb1_rty_i)); // master 1
assert property (@(posedge clk_i) (!wb1_stb_i |-> !wb1_ack_o && !wb1_err_o && !wb1_rty_o)); // slave 1

// Rule 3.25, Observation 3.25
assert property (@(posedge clk_i) (wb0_stb_o |-> wb0_cyc_o));
assume property (@(posedge clk_i) (wb0_stb_i |-> wb0_cyc_i));
assert property (@(posedge clk_i) (wb1_stb_o |-> wb1_cyc_o));
assume property (@(posedge clk_i) (wb1_stb_i |-> wb1_cyc_i));

// 3.1.3 Handshaking protocol
assert property (@(posedge clk_i) ($fell(wb0_stb_o) |-> $past(wb0_ack_i || wb0_err_i || wb0_rty_i)));
assume property (@(posedge clk_i) ($fell(wb0_stb_i) |-> $past(wb0_ack_o || wb0_err_o || wb0_rty_o)));
assert property (@(posedge clk_i) ($fell(wb1_stb_o) |-> $past(wb1_ack_i || wb1_err_i || wb1_rty_i)));
assume property (@(posedge clk_i) ($fell(wb1_stb_i) |-> $past(wb1_ack_o || wb1_err_o || wb1_rty_o)));
// Conflicts with example in Section 3.3
//assert property (@(posedge clk_i) ($rose(wb0_ack_i || wb0_err_i || wb0_rty_i) |=> $fell(wb0_stb_o)));
//assume property (@(posedge clk_i) ($rose(wb0_ack_o || wb0_err_o || wb0_rty_o) |=> $fell(wb0_stb_i)));
//assert property (@(posedge clk_i) ($rose(wb1_ack_i || wb1_err_i || wb1_rty_i) |=> $fell(wb1_stb_o)));
//assume property (@(posedge clk_i) ($rose(wb1_ack_o || wb1_err_o || wb1_rty_o) |=> $fell(wb1_stb_i)));

// Rule 3.35
assume property (@(posedge clk_i) ($rose(wb0_cyc_o && wb0_stb_o) |-> ##[0:$] $rose(wb0_ack_i || wb0_err_i || wb0_rty_i)));
assert property (@(posedge clk_i) ($rose(wb0_cyc_i && wb0_stb_i) |-> ##[0:$] $rose(wb0_ack_o || wb0_err_o || wb0_rty_o)));
assume property (@(posedge clk_i) ($rose(wb1_cyc_o && wb1_stb_o) |-> ##[0:$] $rose(wb1_ack_i || wb1_err_i || wb1_rty_i)));
assert property (@(posedge clk_i) ($rose(wb1_cyc_i && wb1_stb_i) |-> ##[0:$] $rose(wb1_ack_o || wb1_err_o || wb1_rty_o)));

// Rule 3.45
assume property (@(posedge clk_i) (!((wb0_ack_i && wb0_err_i) || (wb0_ack_i && wb0_rty_i) || (wb0_err_i && wb0_rty_i))));
assert property (@(posedge clk_i) (!((wb0_ack_o && wb0_err_o) || (wb0_ack_o && wb0_rty_o) || (wb0_err_o && wb0_rty_o))));
assume property (@(posedge clk_i) (!((wb1_ack_i && wb1_err_i) || (wb1_ack_i && wb1_rty_i) || (wb1_err_i && wb1_rty_i))));
assert property (@(posedge clk_i) (!((wb1_ack_o && wb1_err_o) || (wb1_ack_o && wb1_rty_o) || (wb1_err_o && wb1_rty_o))));

// Rule 3.50, covered by Observation 3.10 and Rule 3.35
//assume property (@(posedge clk_i) ($fell(wb0_stb_o) |-> ##[0:$] $fell(wb0_ack_i || wb0_err_i || wb0_rty_i)));
//assert property (@(posedge clk_i) ($fell(wb0_stb_i) |-> $fell(wb0_ack_o || wb0_err_o || wb0_rty_o)));
//assume property (@(posedge clk_i) ($fell(wb1_stb_o) |-> ##[0:$] $fell(wb1_ack_i || wb1_err_i || wb1_rty_i)));
//assert property (@(posedge clk_i) ($fell(wb1_stb_i) |-> $fell(wb1_ack_o || wb1_err_o || wb1_rty_o)));

// Rule 3.60
assert property (@(posedge clk_i) (($past(wb0_stb_o && !wb0_ack_i) && wb0_stb_o) |-> ($stable(wb0_addr_o) && $stable(wb0_sel_o) && $stable(wb0_we_o))));
assert property (@(posedge clk_i) (($past(wb0_stb_o && !wb0_ack_i) && wb0_stb_o && wb0_we_o) |-> $stable(wb0m_data_o)));                                    // failed
assume property (@(posedge clk_i) (($past(wb0_stb_i && !wb0_ack_o) && wb0_stb_i) |-> ($stable(wb0_addr_i) && $stable(wb0_sel_i) && $stable(wb0_we_i))));
assume property (@(posedge clk_i) (($past(wb0_stb_i && !wb0_ack_o) && wb0_stb_i && wb0_we_i) |-> $stable(wb0s_data_i)));
assert property (@(posedge clk_i) (($past(wb1_stb_o && !wb1_ack_i) && wb1_stb_o) |-> ($stable(wb1_addr_o) && $stable(wb1_sel_o) && $stable(wb1_we_o))));
assert property (@(posedge clk_i) (($past(wb1_stb_o && !wb1_ack_i) && wb1_stb_o && wb1_we_o) |-> $stable(wb1m_data_o)));
assume property (@(posedge clk_i) (($past(wb1_stb_i && !wb1_ack_o) && wb1_stb_i) |-> ($stable(wb1_addr_i) && $stable(wb1_sel_i) && $stable(wb1_we_i))));
assume property (@(posedge clk_i) (($past(wb1_stb_i && !wb1_ack_o) && wb1_stb_i && wb1_we_i) |-> $stable(wb1s_data_i)));

// Observation 3.55?

// wb_dma specific constraints needed for the WISHBONE assertions to pass
// MASTER channels always get acknowledged
assume property (@(posedge clk_i) (!wb0_err_i && !wb0_rty_i && !wb1_err_i && !wb1_rty_i));
// No software-forced STOP
// Note: writing to CSR register of channel i: wb0_addr_i[9:2] == {5'hi, 3'b0}
assume property (@(posedge clk_i) (wb0_stb_i && wb0_we_i && wb0_addr_i[4:2] == 3'b0 |-> wb0m_data_i[9] == 1'b0));
// No pass through mode when MASTERs are transferring data
assume property (@(posedge clk_i) (wb0_cyc_o |-> wb1_addr_i[31:28] == 4'b0));
assume property (@(posedge clk_i) (wb1_cyc_o |-> wb0_addr_i[31:28] == 4'b0));
// No change of csr when MASTERs are transferring data
assume property (@(posedge clk_i) (wb0_cyc_o || wb1_cyc_o |-> $past(wb0_addr_i[4:2] != 3'b0)));

// Needed for the failed assertion to pass - bug?
//assume property (@(posedge clk_i) (wb0_stb_o |-> $past(!wb0_stb_i && $stable(wb0_addr_i[9:3]))));

// Additional control signals

assume property (@(posedge clk_i) (dma_req_i == 1'b0));
assert property (@(posedge clk_i) (dma_ack_o == 1'b0));
// Assume no HW handshake mode: Needed for the above assertion to pass
assume property (@(posedge clk_i) (wb0_stb_i && wb0_we_i && wb0_addr_i[4:2] == 3'b0 |-> wb0m_data_i[5] != 1'b1));

assume property (@(posedge clk_i) (dma_nd_i == 1'b0));
assume property (@(posedge clk_i) (dma_rest_i == 1'b0));

//assert property (@(posedge clk_i) (inta_o == 1'b0));
//assert property (@(posedge clk_i) (intb_o == 1'b0));
// Disable interrupts: Needed for the previous assertions to pass
//assume property (@(posedge clk_i) (wb0_stb_i && wb0_we_i && wb0_addr_i[9:2] == 8'h1 |-> wb0m_data_i == 32'b0));
//assume property (@(posedge clk_i) (wb0_stb_i && wb0_we_i && wb0_addr_i[9:2] == 8'h2 |-> wb0m_data_i == 32'b0));


// Q-channel interface
//assume property (@(posedge clk_i) (qreqn));
assume property (@(posedge clk_i) ($fell(qreqn) |-> $past(qacceptn && !qdeny)));
assume property (@(posedge clk_i) ($rose(qreqn) |-> $past(qacceptn == qdeny)));

assert property (@(posedge clk_i) ($fell(qacceptn) |-> $past(!qreqn && !qdeny)));
assert property (@(posedge clk_i) ($rose(qacceptn) |-> $past(qreqn && !qdeny)));
assert property (@(posedge clk_i) ($fell(qdeny) |-> $past(qreqn && qacceptn)));
assert property (@(posedge clk_i) ($rose(qdeny) |-> $past(!qreqn && qacceptn)));

// Optional Q-channel assumption
//assume property (@(posedge clk_i) ($fell(qreqn) |-> ##[1:$] $rose(qreqn)));

// Constraints for retention registers
wire standby_state = !qreqn && !qacceptn;

assume property (@(posedge clk_i) ($rose(pr_restore) |-> $past(standby_state)));
assume property (@(posedge clk_i) ($rose(pr_restore) |=> $rose(qreqn) && $fell(pr_restore)));
assume property (@(posedge clk_i) (standby_state && !pr_restore |=> !qreqn));
