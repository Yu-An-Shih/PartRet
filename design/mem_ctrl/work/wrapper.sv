// This is the testbench that wraps the original and partial retention designs.
// This script will be used by the retention explorer tool, 
// so please (only) modify it as instructed (marked with "// TODO: ...") if you want to call the explorer.

module wrapper;

wire clk_i;
wire rst_i;
wire mc_clk_i;
wire [0:0] mc_ack_pad_i;
wire [0:0] mc_br_pad_i;
wire [31:0] mc_data_pad_i;
wire [3:0] mc_dp_pad_i;
wire [0:0] mc_sts_pad_i;
wire [0:0] resume_req_i;
wire [0:0] susp_req_i;
wire [31:0] wb_addr_i;
wire [0:0] wb_cyc_i;
wire [31:0] wb_data_i;
wire [3:0] wb_sel_i;
wire [0:0] wb_stb_i;
wire [0:0] wb_we_i;
wire [23:0] mc_addr_pad_o, mc_addr_pad_o_test;
wire [0:0] mc_adsc_pad_o_, mc_adsc_pad_o__test;
wire [0:0] mc_adv_pad_o_, mc_adv_pad_o__test;
wire [0:0] mc_bg_pad_o, mc_bg_pad_o_test;
wire [0:0] mc_cas_pad_o_, mc_cas_pad_o__test;
wire [0:0] mc_cke_pad_o_, mc_cke_pad_o__test;
wire [0:0] mc_coe_pad_coe_o, mc_coe_pad_coe_o_test;
wire [7:0] mc_cs_pad_o_, mc_cs_pad_o__test;
wire [31:0] mc_data_pad_o, mc_data_pad_o_test;
wire [0:0] mc_doe_pad_doe_o, mc_doe_pad_doe_o_test;
wire [3:0] mc_dp_pad_o, mc_dp_pad_o_test;
wire [3:0] mc_dqm_pad_o, mc_dqm_pad_o_test;
wire [0:0] mc_oe_pad_o_, mc_oe_pad_o__test;
wire [0:0] mc_ras_pad_o_, mc_ras_pad_o__test;
wire [0:0] mc_rp_pad_o_, mc_rp_pad_o__test;
wire [0:0] mc_vpen_pad_o, mc_vpen_pad_o_test;
wire [0:0] mc_we_pad_o_, mc_we_pad_o__test;
wire [0:0] mc_zz_pad_o, mc_zz_pad_o_test;
wire [31:0] poc_o, poc_o_test;
wire [0:0] suspended_o, suspended_o_test;
wire [0:0] wb_ack_o, wb_ack_o_test;
wire [31:0] wb_data_o, wb_data_o_test;
wire [0:0] wb_err_o, wb_err_o_test;
wire check_cond;

assign check_cond = !suspended_o;

mc_top design_golden (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .mc_clk_i(mc_clk_i),
    .mc_ack_pad_i(mc_ack_pad_i),
    .mc_br_pad_i(mc_br_pad_i),
    .mc_data_pad_i(mc_data_pad_i),
    .mc_dp_pad_i(mc_dp_pad_i),
    .mc_sts_pad_i(mc_sts_pad_i),
    .resume_req_i(resume_req_i),
    .susp_req_i(susp_req_i),
    .wb_addr_i(wb_addr_i),
    .wb_cyc_i(wb_cyc_i),
    .wb_data_i(wb_data_i),
    .wb_sel_i(wb_sel_i),
    .wb_stb_i(wb_stb_i),
    .wb_we_i(wb_we_i),
    .mc_addr_pad_o(mc_addr_pad_o),
    .mc_adsc_pad_o_(mc_adsc_pad_o_),
    .mc_adv_pad_o_(mc_adv_pad_o_),
    .mc_bg_pad_o(mc_bg_pad_o),
    .mc_cas_pad_o_(mc_cas_pad_o_),
    .mc_cke_pad_o_(mc_cke_pad_o_),
    .mc_coe_pad_coe_o(mc_coe_pad_coe_o),
    .mc_cs_pad_o_(mc_cs_pad_o_),
    .mc_data_pad_o(mc_data_pad_o),
    .mc_doe_pad_doe_o(mc_doe_pad_doe_o),
    .mc_dp_pad_o(mc_dp_pad_o),
    .mc_dqm_pad_o(mc_dqm_pad_o),
    .mc_oe_pad_o_(mc_oe_pad_o_),
    .mc_ras_pad_o_(mc_ras_pad_o_),
    .mc_rp_pad_o_(mc_rp_pad_o_),
    .mc_vpen_pad_o(mc_vpen_pad_o),
    .mc_we_pad_o_(mc_we_pad_o_),
    .mc_zz_pad_o(mc_zz_pad_o),
    .poc_o(poc_o),
    .suspended_o(suspended_o),
    .wb_ack_o(wb_ack_o),
    .wb_data_o(wb_data_o),
    .wb_err_o(wb_err_o)
);

mc_top_test design_test (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .mc_clk_i(mc_clk_i),
    .mc_ack_pad_i(mc_ack_pad_i),
    .mc_br_pad_i(mc_br_pad_i),
    .mc_data_pad_i(mc_data_pad_i),
    .mc_dp_pad_i(mc_dp_pad_i),
    .mc_sts_pad_i(mc_sts_pad_i),
    .resume_req_i(resume_req_i),
    .susp_req_i(susp_req_i),
    .wb_addr_i(wb_addr_i),
    .wb_cyc_i(wb_cyc_i),
    .wb_data_i(wb_data_i),
    .wb_sel_i(wb_sel_i),
    .wb_stb_i(wb_stb_i),
    .wb_we_i(wb_we_i),
    .mc_addr_pad_o(mc_addr_pad_o_test),
    .mc_adsc_pad_o_(mc_adsc_pad_o__test),
    .mc_adv_pad_o_(mc_adv_pad_o__test),
    .mc_bg_pad_o(mc_bg_pad_o_test),
    .mc_cas_pad_o_(mc_cas_pad_o__test),
    .mc_cke_pad_o_(mc_cke_pad_o__test),
    .mc_coe_pad_coe_o(mc_coe_pad_coe_o_test),
    .mc_cs_pad_o_(mc_cs_pad_o__test),
    .mc_data_pad_o(mc_data_pad_o_test),
    .mc_doe_pad_doe_o(mc_doe_pad_doe_o_test),
    .mc_dp_pad_o(mc_dp_pad_o_test),
    .mc_dqm_pad_o(mc_dqm_pad_o_test),
    .mc_oe_pad_o_(mc_oe_pad_o__test),
    .mc_ras_pad_o_(mc_ras_pad_o__test),
    .mc_rp_pad_o_(mc_rp_pad_o__test),
    .mc_vpen_pad_o(mc_vpen_pad_o_test),
    .mc_we_pad_o_(mc_we_pad_o__test),
    .mc_zz_pad_o(mc_zz_pad_o_test),
    .poc_o(poc_o_test),
    .suspended_o(suspended_o_test),
    .wb_ack_o(wb_ack_o_test),
    .wb_data_o(wb_data_o_test),
    .wb_err_o(wb_err_o_test),
    .pr_restore(pr_restore)
);

// TODO: Please add the formal interface constraints either here or in ret_checker.tcl.

// WISHBONE interface
// Rule 3.20
//assume property (@(posedge clk_i) (rst_i |=> !wb_cyc_i && !wb_stb_i));

// Observation 3.10, conflicts with Permission 3.35?
assert property (@(posedge clk_i) (!wb_stb_i |-> !wb_ack_o && !wb_err_o));

// Rule 3.25, Observation 3.25
assume property (@(posedge clk_i) (wb_stb_i |-> wb_cyc_i));

// 3.1.3 Handshaking protocol
assume property (@(posedge clk_i) ($fell(wb_stb_i) |-> $past(wb_ack_o || wb_err_o)));
// Conflicts with example in Section 3.3
//assume property (@(posedge clk_i) ($rose(wb_ack_o || wb_err_o) |=> $fell(wb_stb_i)));

// Rule 3.35
assert property (@(posedge clk_i) ($rose(wb_cyc_i && wb_stb_i) |-> ##[0:$] $rose(wb_ack_o || wb_err_o)));

// Rule 3.45
assert property (@(posedge clk_i) (!(wb_ack_o && wb_err_o)));

// Rule 3.50, covered by Observation 3.10 and Rule 3.35
//assert property (@(posedge clk_i) ($fell(wb_stb_i) |-> $fell(wb_ack_o || wb_err_o)));

// Rule 3.60
assume property (@(posedge clk_i) (($past(wb_stb_i && !wb_ack_o) && wb_stb_i) |-> ($stable(wb_addr_i) && $stable(wb_sel_i) && $stable(wb_we_i))));
assume property (@(posedge clk_i) (($past(wb_stb_i && !wb_ack_o) && wb_stb_i && wb_we_i) |-> $stable(wb_data_i)));

// Observation 3.55?

// Optional WISHBONE interface assumptions
assume property (@(posedge clk_i) wb_addr_i[31:29] == 3'b000);  // Always selects memory - never modifies configuration registers
assume property (@(posedge clk_i) wb_addr_i[28:21] == 8'b0000_0000);  // BA_MASK

assume property (@(posedge clk_i) (wb_stb_i == wb_cyc_i));

//assume property (@(posedge clk_i) (wb_we_i |-> wb_stb_i));


// Memory interface

// Power-On Configuration
reg	rst_r1;

always @(posedge mc_clk_i or posedge rst_i)
	if(rst_i)	rst_r1 <= #1 1'b1;
	else		rst_r1 <= #1 1'b0;

// assume property (@(posedge clk_i) rst_i |-> mc_data_pad_i == {28'hzzz_zzzz, 2'b11, 2'b10});                         // Declare in ret_check.tcl?
//assume property (@(posedge clk_i) rst_r3 |-> mc_data_pad_i == {28'b0, 2'b11, 2'b10});    // Sync. Device, 32-bit data bus
//assume property (@(posedge mc_clk_i) rst_r1 |-> mc_data_pad_i[3:0] == {2'b11, 2'b10});    // Sync. Device, 32-bit data bus
assume property (@(posedge mc_clk_i) rst_r1 |-> mc_data_pad_i == {28'b0, 2'b11, 2'b10});    // Sync. Device, 32-bit data bus


assert property (@(posedge mc_clk_i) (mc_cs_pad_o_[7:1] == 7'b111_1111));   // Only chip select 0 is used

// Connect Chip Select 0 to a Sync. Device
wire mc_cs = mc_coe_pad_coe_o ? mc_cs_pad_o_[0] : 1'b1;
wire mc_oe = mc_coe_pad_coe_o ? mc_oe_pad_o_ : 1'b1;
wire mc_we = mc_coe_pad_coe_o ? mc_we_pad_o_ : 1'b1;
//assert property (@(posedge mc_clk_i) (mc_coe_pad_coe_o == 1'b1));

wire mem_op = ~mc_cs & (~mc_oe | ~mc_we);

assert property (@(posedge mc_clk_i) ($fell(mc_cs) |-> $past(~mc_ack_pad_i)));
assert property (@(posedge mc_clk_i) ($rose(mc_cs) |-> $past(mc_ack_pad_i)));

assume property (@(posedge mc_clk_i) ($rose(mc_ack_pad_i) |-> $past(mem_op)));
assume property (@(posedge mc_clk_i) ($fell(mc_ack_pad_i) |-> $fell(mem_op)));  // optional?
assume property (@(posedge mc_clk_i) ($fell(mem_op) |-> $fell(mc_ack_pad_i)));

//assert property (@(posedge mc_clk_i) ~mc_cs |-> (~mc_oe & mc_we) || (mc_oe & ~mc_we));
assert property (@(posedge mc_clk_i) $fell(mc_cs) |=> (~mc_oe & mc_we) || (mc_oe & ~mc_we));
assert property (@(posedge mc_clk_i) mem_op && $past(mem_op) |-> $stable(mc_oe) && $stable(mc_we));

// Never assert external bus request
assume property (@(posedge mc_clk_i) mc_br_pad_i == 1'b0);
assert property (@(posedge mc_clk_i) mc_bg_pad_o == 1'b0);

// No parity check for Sync. Device
assume property (@(posedge mc_clk_i) mc_dp_pad_i == 4'b0000);
//assert property (@(posedge mc_clk_i) mc_dp_pad_o == 4'b0000);

// Does not connect to Flash
assume property (@(posedge mc_clk_i) mc_sts_pad_i == 1'b0);

// Optional memory interface assumptions
//assume property (@(posedge mc_clk_i) $fell(mc_cs) |-> ##[0:$] $rose(mc_ack_pad_i));
assume property (@(posedge mc_clk_i) ($rose(mem_op) |=> $rose(mc_ack_pad_i)));


// Power management interface
assume property (@(posedge clk_i) ($rose(susp_req_i) |-> $past(!suspended_o)));
assume property (@(posedge clk_i) ($fell(susp_req_i) |-> $past(suspended_o)));
assume property (@(posedge clk_i) ($rose(suspended_o) |=> $fell(susp_req_i)));

assume property (@(posedge clk_i) ($rose(resume_req_i) |-> $past(suspended_o)));
assume property (@(posedge clk_i) ($fell(resume_req_i) |-> $past(!suspended_o)));
assume property (@(posedge clk_i) ($fell(suspended_o) |=> $fell(resume_req_i)));

assert property (@(posedge clk_i) ($rose(suspended_o) |-> (susp_req_i && !resume_req_i)));
assert property (@(posedge clk_i) ($fell(suspended_o) |-> (!susp_req_i && resume_req_i)));
assert property (@(posedge clk_i) ($rose(susp_req_i) |-> ##[0:$] $rose(suspended_o)));
assert property (@(posedge clk_i) ($rose(resume_req_i) |-> ##[0:$] $fell(suspended_o)));

// Optional power management assumption
//assume property (@(posedge clk_i) ($rose(suspended_o) |-> ##[1:$] $rose(resume_req_i)));

// Optional: Does not affect the verification result
//assume property (@(posedge clk_i) ($fell(susp_req_i) |-> not (##[1:$] $rose(susp_req_i))));
//assume property (@(posedge clk_i) ($fell(resume_req_i) |-> ##[1:$] $stable(resume_req_i)));

// Constraints for retention registers

assume property (@(posedge clk_i) $rose(suspended_o) |=> $rose(pr_restore));
assume property (@(posedge clk_i) $rose(pr_restore) |-> $past($rose(suspended_o)));
assume property (@(posedge clk_i) $rose(pr_restore) |=> $rose(resume_req_i) && $fell(pr_restore));
assume property (@(posedge clk_i) $rose(resume_req_i) |-> $past($rose(pr_restore)));
//assume property (@(posedge clk_i) $fell(pr_restore) |-> $past($rose(pr_restore)));


// TODO: interaction between interfaces (Optional)
// No memory operation and suspend request at the same time
//assume property (@(posedge clk_i) !(wb_stb_i && susp_req_i));

endmodule
