// Request Channel
assume property (@(posedge nvdla_core_clk) ($fell(csb2cmac_a_req_pvld) |-> $past(csb2cmac_a_req_prdy)));

// TODO: constraints for dp2reg_done_i?

// Q-channel interface
//assume property (@(posedge nvdla_core_clk) (qreqn));
assume property (@(posedge nvdla_core_clk) ($fell(qreqn) |-> $past(qacceptn && !qdeny)));
assume property (@(posedge nvdla_core_clk) ($rose(qreqn) |-> $past(qacceptn == qdeny)));

assert property (@(posedge nvdla_core_clk) ($fell(qacceptn) |-> $past(!qreqn && !qdeny)));
assert property (@(posedge nvdla_core_clk) ($rose(qacceptn) |-> $past(qreqn && !qdeny)));
assert property (@(posedge nvdla_core_clk) ($fell(qdeny) |-> $past(qreqn && qacceptn)));
assert property (@(posedge nvdla_core_clk) ($rose(qdeny) |-> $past(!qreqn && qacceptn)));

// Optional Q-channel assumption
assume property (@(posedge nvdla_core_clk) ($fell(qreqn) |-> ##[1:$] $rose(qreqn)));

// Constraints for retention registers
wire standby_state = !qreqn && !qacceptn;

assume property (@(posedge nvdla_core_clk) ($rose(pr_restore) |-> $past(standby_state)));
assume property (@(posedge nvdla_core_clk) ($rose(pr_restore) |=> $rose(qreqn) && $fell(pr_restore)));
assume property (@(posedge nvdla_core_clk) (standby_state && !pr_restore |=> !qreqn));