// WISHBONE interface
// Rule 3.20
//assume property (@(posedge wb_clk_i) (rst_i |=> !wb_cyc_i && !wb_stb_i));

// Observation 3.10, conflicts with Permission 3.35?
assert property (@(posedge wb_clk_i) (!wb_stb_i |-> !wb_ack_o && !wb_err_o));

// Rule 3.25, Observation 3.25
assume property (@(posedge wb_clk_i) (wb_stb_i |-> wb_cyc_i));

// 3.1.3 Handshaking protocol
assume property (@(posedge wb_clk_i) ($fell(wb_stb_i) |-> $past(wb_ack_o || wb_err_o)));
// Conflicts with example in Section 3.3
//assume property (@(posedge wb_clk_i) ($rose(wb_ack_o || wb_err_o) |=> $fell(wb_stb_i)));

// Rule 3.35
assert property (@(posedge wb_clk_i) ($rose(wb_cyc_i && wb_stb_i) |-> ##[0:$] $rose(wb_ack_o || wb_err_o)));

// Rule 3.45
assert property (@(posedge wb_clk_i) (!(wb_ack_o && wb_err_o)));

// Rule 3.50, covered by Observation 3.10 and Rule 3.35
//assert property (@(posedge wb_clk_i) ($fell(wb_stb_i) |-> $fell(wb_ack_o || wb_err_o)));

// Rule 3.60
assume property (@(posedge wb_clk_i) (($past(wb_stb_i && !wb_ack_o) && wb_stb_i) |-> ($stable(wb_adr_i) && $stable(wb_sel_i) && $stable(wb_we_i))));
assume property (@(posedge wb_clk_i) (($past(wb_stb_i && !wb_ack_o) && wb_stb_i && wb_we_i) |-> $stable(wb_dat_i)));

// Observation 3.55?


// Q-channel interface
//assume property (@(posedge wb_clk_i) (qreqn));
assume property (@(posedge wb_clk_i) ($fell(qreqn) |-> $past(qacceptn && !qdeny)));
assume property (@(posedge wb_clk_i) ($rose(qreqn) |-> $past(qacceptn == qdeny)));

assert property (@(posedge wb_clk_i) ($fell(qacceptn) |-> $past(!qreqn && !qdeny)));
assert property (@(posedge wb_clk_i) ($rose(qacceptn) |-> $past(qreqn && !qdeny)));
assert property (@(posedge wb_clk_i) ($fell(qdeny) |-> $past(qreqn && qacceptn)));
assert property (@(posedge wb_clk_i) ($rose(qdeny) |-> $past(!qreqn && qacceptn)));

// Optional Q-channel assumption
//assume property (@(posedge wb_clk_i) ($fell(qreqn) |-> ##[1:$] $rose(qreqn)));

// Constraints for retention registers
wire standby_state = !qreqn && !qacceptn;

assume property (@(posedge wb_clk_i) ($rose(pr_restore) |-> $past(standby_state)));
assume property (@(posedge wb_clk_i) ($rose(pr_restore) |=> $rose(qreqn) && $fell(pr_restore)));
assume property (@(posedge wb_clk_i) (standby_state && !pr_restore |=> !qreqn));
