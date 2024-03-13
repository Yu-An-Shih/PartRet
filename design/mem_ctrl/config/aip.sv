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
assume property (@(posedge clk_i) disable iff (rst_i) wb_addr_i[28:21] == 8'b0000_0000);  // BA_MASK

assume property (@(posedge clk_i) (wb_stb_i == wb_cyc_i));

//assume property (@(posedge clk_i) (wb_we_i |-> wb_stb_i));


// Memory interface

assert property (@(posedge mc_clk_i) (mc_cs_pad_o_[7:1] == 7'b111_1111));   // Only chip select 0 is used

// Connect Chip Select 0 to a Sync. Device
wire mc_cs = mc_coe_pad_coe_o ? mc_cs_pad_o_[0] : 1'b1;
wire mc_oe = mc_coe_pad_coe_o ? mc_oe_pad_o_ : 1'b1;
wire mc_we = mc_coe_pad_coe_o ? mc_we_pad_o_ : 1'b1;
//assert property (@(posedge mc_clk_i) (mc_coe_pad_coe_o == 1'b1));

wire mem_op = ~mc_cs & (~mc_oe | ~mc_we);

assert property (@(posedge mc_clk_i) ($fell(mc_cs) |-> $past(~mc_ack_pad_i)));
assert property (@(posedge mc_clk_i) ($rose(mc_cs) |-> $past(mc_ack_pad_i)));

assume property (@(posedge mc_clk_i) ($rose(mc_ack_pad_i) |-> ~mc_cs));
assume property (@(posedge mc_clk_i) ($fell(mc_ack_pad_i) |-> mc_cs));
assume property (@(posedge mc_clk_i) ($rose(mc_cs) |-> $fell(mc_ack_pad_i)));

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


// Constraints for retention registers

//wire standby_state = suspended_o && !resume_req_i;
//assume property (@(posedge clk_i) ($rose(pr_restore) |-> $past(standby_state)));
//assume property (@(posedge clk_i) ($rose(pr_restore) |=> $rose(resume_req_i) && $fell(pr_restore)));
//assume property (@(posedge clk_i) (standby_state && !pr_restore |=> !resume_req_i));

assume property (@(posedge clk_i) ($rose(pr_restore) |-> $rose(suspended_o)));
assume property (@(posedge clk_i) ($rose(suspended_o) |-> $rose(pr_restore)));
assume property (@(posedge clk_i) ($rose(pr_restore) |=> $rose(resume_req_i) && $fell(pr_restore)));


// Optional: No memory operation and suspend request at the same time
//assume property (@(posedge clk_i) !(wb_stb_i && susp_req_i));
