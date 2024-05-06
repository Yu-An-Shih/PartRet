// This is the testbench that wraps the original and partial retention designs.
// This script will be used by the retention explorer tool, 
// so please (only) modify it as instructed (marked with "// TODO: ...") if you want to call the explorer.

module wrapper;

wire nvdla_core_clk;
wire nvdla_core_rstn;
wire [62:0] csb2cacc_req_pd;
wire [0:0] csb2cacc_req_pvld;
wire [0:0] dp2reg_done;
wire [31:0] dp2reg_sat_count;
wire [0:0] qreqn;
wire [33:0] cacc2csb_resp_pd, cacc2csb_resp_pd_test;
wire [0:0] cacc2csb_resp_valid, cacc2csb_resp_valid_test;
wire [0:0] csb2cacc_req_prdy, csb2cacc_req_prdy_test;
wire [0:0] qacceptn, qacceptn_test;
wire [0:0] qdeny, qdeny_test;
wire [4:0] reg2dp_batches, reg2dp_batches_test;
wire [4:0] reg2dp_clip_truncate, reg2dp_clip_truncate_test;
wire [0:0] reg2dp_conv_mode, reg2dp_conv_mode_test;
wire [31:0] reg2dp_cya, reg2dp_cya_test;
wire [26:0] reg2dp_dataout_addr, reg2dp_dataout_addr_test;
wire [12:0] reg2dp_dataout_channel, reg2dp_dataout_channel_test;
wire [12:0] reg2dp_dataout_height, reg2dp_dataout_height_test;
wire [12:0] reg2dp_dataout_width, reg2dp_dataout_width_test;
wire [0:0] reg2dp_line_packed, reg2dp_line_packed_test;
wire [18:0] reg2dp_line_stride, reg2dp_line_stride_test;
wire [0:0] reg2dp_op_en, reg2dp_op_en_test;
wire [1:0] reg2dp_proc_precision, reg2dp_proc_precision_test;
wire [0:0] reg2dp_surf_packed, reg2dp_surf_packed_test;
wire [18:0] reg2dp_surf_stride, reg2dp_surf_stride_test;
wire [6:0] slcg_op_en, slcg_op_en_test;
wire check_cond;

assign check_cond = qacceptn;

NV_NVDLA_cacc_qchannel design_golden (
    .nvdla_core_clk(nvdla_core_clk),
    .nvdla_core_rstn(nvdla_core_rstn),
    .csb2cacc_req_pd(csb2cacc_req_pd),
    .csb2cacc_req_pvld(csb2cacc_req_pvld),
    .dp2reg_done(dp2reg_done),
    .dp2reg_sat_count(dp2reg_sat_count),
    .qreqn(qreqn),
    .cacc2csb_resp_pd(cacc2csb_resp_pd),
    .cacc2csb_resp_valid(cacc2csb_resp_valid),
    .csb2cacc_req_prdy(csb2cacc_req_prdy),
    .qacceptn(qacceptn),
    .qdeny(qdeny),
    .reg2dp_batches(reg2dp_batches),
    .reg2dp_clip_truncate(reg2dp_clip_truncate),
    .reg2dp_conv_mode(reg2dp_conv_mode),
    .reg2dp_cya(reg2dp_cya),
    .reg2dp_dataout_addr(reg2dp_dataout_addr),
    .reg2dp_dataout_channel(reg2dp_dataout_channel),
    .reg2dp_dataout_height(reg2dp_dataout_height),
    .reg2dp_dataout_width(reg2dp_dataout_width),
    .reg2dp_line_packed(reg2dp_line_packed),
    .reg2dp_line_stride(reg2dp_line_stride),
    .reg2dp_op_en(reg2dp_op_en),
    .reg2dp_proc_precision(reg2dp_proc_precision),
    .reg2dp_surf_packed(reg2dp_surf_packed),
    .reg2dp_surf_stride(reg2dp_surf_stride),
    .slcg_op_en(slcg_op_en)
);

NV_NVDLA_cacc_qchannel_test design_test (
    .nvdla_core_clk(nvdla_core_clk),
    .nvdla_core_rstn(nvdla_core_rstn),
    .csb2cacc_req_pd(csb2cacc_req_pd),
    .csb2cacc_req_pvld(csb2cacc_req_pvld),
    .dp2reg_done(dp2reg_done),
    .dp2reg_sat_count(dp2reg_sat_count),
    .qreqn(qreqn),
    .cacc2csb_resp_pd(cacc2csb_resp_pd_test),
    .cacc2csb_resp_valid(cacc2csb_resp_valid_test),
    .csb2cacc_req_prdy(csb2cacc_req_prdy_test),
    .qacceptn(qacceptn_test),
    .qdeny(qdeny_test),
    .reg2dp_batches(reg2dp_batches_test),
    .reg2dp_clip_truncate(reg2dp_clip_truncate_test),
    .reg2dp_conv_mode(reg2dp_conv_mode_test),
    .reg2dp_cya(reg2dp_cya_test),
    .reg2dp_dataout_addr(reg2dp_dataout_addr_test),
    .reg2dp_dataout_channel(reg2dp_dataout_channel_test),
    .reg2dp_dataout_height(reg2dp_dataout_height_test),
    .reg2dp_dataout_width(reg2dp_dataout_width_test),
    .reg2dp_line_packed(reg2dp_line_packed_test),
    .reg2dp_line_stride(reg2dp_line_stride_test),
    .reg2dp_op_en(reg2dp_op_en_test),
    .reg2dp_proc_precision(reg2dp_proc_precision_test),
    .reg2dp_surf_packed(reg2dp_surf_packed_test),
    .reg2dp_surf_stride(reg2dp_surf_stride_test),
    .slcg_op_en(slcg_op_en_test),
    .pr_restore(pr_restore)
);

// TODO: Please add the formal interface constraints either here or in ret_checker.tcl.

// Request Channel
assume property (@(posedge nvdla_core_clk) ($fell(csb2cacc_req_pvld) |-> $past(csb2cacc_req_prdy)));

// TODO: constraints for dp2reg_done?

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
