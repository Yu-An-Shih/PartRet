// This is the testbench that wraps the original and partial retention designs.
// This script will be used by the retention explorer tool, 
// so please (only) modify it as instructed (marked with "// TODO: ...") if you want to call the explorer.

module wrapper;

wire nvdla_core_clk;
wire nvdla_core_rstn;
wire [62:0] csb2cmac_a_req_pd;
wire [0:0] csb2cmac_a_req_pvld;
wire [0:0] dp2reg_done_i;
wire [0:0] qreqn;
wire [33:0] cmac_a2csb_resp_pd, cmac_a2csb_resp_pd_test;
wire [0:0] cmac_a2csb_resp_valid, cmac_a2csb_resp_valid_test;
wire [0:0] csb2cmac_a_req_prdy, csb2cmac_a_req_prdy_test;
wire [0:0] qacceptn, qacceptn_test;
wire [0:0] qdeny, qdeny_test;
wire [0:0] reg2dp_conv_mode_o, reg2dp_conv_mode_o_test;
wire [0:0] reg2dp_op_en_o, reg2dp_op_en_o_test;
wire [1:0] reg2dp_proc_precision_o, reg2dp_proc_precision_o_test;
wire [10:0] slcg_op_en_o, slcg_op_en_o_test;
wire check_cond;

assign check_cond = qacceptn;

NV_NVDLA_cmac_qchannel design_golden (
    .nvdla_core_clk(nvdla_core_clk),
    .nvdla_core_rstn(nvdla_core_rstn),
    .csb2cmac_a_req_pd(csb2cmac_a_req_pd),
    .csb2cmac_a_req_pvld(csb2cmac_a_req_pvld),
    .dp2reg_done_i(dp2reg_done_i),
    .qreqn(qreqn),
    .cmac_a2csb_resp_pd(cmac_a2csb_resp_pd),
    .cmac_a2csb_resp_valid(cmac_a2csb_resp_valid),
    .csb2cmac_a_req_prdy(csb2cmac_a_req_prdy),
    .qacceptn(qacceptn),
    .qdeny(qdeny),
    .reg2dp_conv_mode_o(reg2dp_conv_mode_o),
    .reg2dp_op_en_o(reg2dp_op_en_o),
    .reg2dp_proc_precision_o(reg2dp_proc_precision_o),
    .slcg_op_en_o(slcg_op_en_o)
);

NV_NVDLA_cmac_qchannel_test design_test (
    .nvdla_core_clk(nvdla_core_clk),
    .nvdla_core_rstn(nvdla_core_rstn),
    .csb2cmac_a_req_pd(csb2cmac_a_req_pd),
    .csb2cmac_a_req_pvld(csb2cmac_a_req_pvld),
    .dp2reg_done_i(dp2reg_done_i),
    .qreqn(qreqn),
    .cmac_a2csb_resp_pd(cmac_a2csb_resp_pd_test),
    .cmac_a2csb_resp_valid(cmac_a2csb_resp_valid_test),
    .csb2cmac_a_req_prdy(csb2cmac_a_req_prdy_test),
    .qacceptn(qacceptn_test),
    .qdeny(qdeny_test),
    .reg2dp_conv_mode_o(reg2dp_conv_mode_o_test),
    .reg2dp_op_en_o(reg2dp_op_en_o_test),
    .reg2dp_proc_precision_o(reg2dp_proc_precision_o_test),
    .slcg_op_en_o(slcg_op_en_o_test),
    .pr_restore(pr_restore)
);

// TODO: Please add the formal interface constraints either here or in ret_checker.tcl.

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
//assume property (@(posedge nvdla_core_clk) ($fell(qreqn) |-> ##[1:$] $rose(qreqn)));

// Optional: Does not affect the verification result
//assume property (@(posedge nvdla_core_clk) ($rose(qreqn) |-> ##[1:$] $stable(qreqn)));

// Constraints for retention registers
wire standby_state = !qreqn && !qacceptn;

assume property (@(posedge nvdla_core_clk) $rose(standby_state) |=> $rose(pr_restore));     // Added to increase verification speed
assume property (@(posedge nvdla_core_clk) ($rose(pr_restore) |-> $past(standby_state)));
assume property (@(posedge nvdla_core_clk) ($rose(pr_restore) |=> $rose(qreqn) && $fell(pr_restore)));
assume property (@(posedge nvdla_core_clk) (standby_state && !pr_restore |=> !qreqn));

endmodule
