/////////////////////////////////////////////////////////////////////
//
// WISHBONE SLAVE INTERFACE
//
// 3.1.1 Reset Operation
//Assume_WISHBONE_Rule_3_20: assume property (@(posedge clk_i) !(rst_i && (wb_stb_i || wb_cyc_i)));
// 3.1.2 Transfer Cycle Initiation
// Assume_WISHBONE_Rule_3_25: assume property (@(posedge clk_i) !(!wb_cyc_i && wb_stb_i));
// 3.1.3 Handshake Protocol
// Assert_WISHBONE_Rule_3_35: assert property (@(posedge clk_i) );
// Assert_WISHBONE_Rule_3_45: assert property (@(posedge clk_i) !(wb_ack_o && wb_err_o));
// TODO: manage MASTER behavior for handshake protocol
// Only allow single read/write?

// Single Read/Write Cycle
//
// Reset Operation (3.1.1)
// Assume_WISHBONE_Rule_3_20: assume property (@(posedge clk_i) rst_i |-> (!wb_stb_i && !wb_cyc_i));   // Declare in ret_check.tcl?
//
// General Cases
assume property (@(posedge clk_i) disable iff (rst_i) wb_cyc_i == wb_stb_i);
assert property (@(posedge clk_i) disable iff (rst_i) !(wb_ack_o && wb_err_o));
//assume property (@(posedge clk_i) disable iff (rst_i) $onehot(wb_sel_i));
assume property (@(posedge clk_i) disable iff (rst_i) wb_sel_i == 4'b1111);
// TODO: valid address range
//
assume property (@(posedge clk_i) disable iff (rst_i) wb_addr_i[31:29] == 3'b000);  // Always selects memory - never modifies configuration registers
assume property (@(posedge clk_i) disable iff (rst_i) wb_addr_i[28:21] == 8'b0000_0000);
//
// (1) 
assert property (@(posedge clk_i) disable iff (rst_i) (!wb_stb_i && !wb_ack_o) |=> !wb_ack_o);
assert property (@(posedge clk_i) disable iff (rst_i) (!wb_stb_i && !wb_err_o) |=> !wb_err_o);
//
// (2)
assume property (@(posedge clk_i) disable iff (rst_i) (wb_stb_i && !(wb_ack_o || wb_err_o)) |=> wb_stb_i);
assert property (@(posedge clk_i) disable iff (rst_i) ($rose(wb_stb_i) && !(wb_ack_o || wb_err_o)) |-> ##[1:$] ($rose(wb_ack_o) || $rose(wb_err_o)));
assume property (@(posedge clk_i) disable iff (rst_i) wb_stb_i |-> ($stable(wb_we_i) && $stable(wb_addr_i) && $stable(wb_sel_i) && $stable(wb_data_i)));
//
// (3)
assume property (@(posedge clk_i) disable iff (rst_i) (wb_stb_i && (wb_ack_o || wb_err_o)) |=> !wb_stb_i);
assert property (@(posedge clk_i) disable iff (rst_i) $rose(wb_ack_o) |=> $fell(wb_ack_o));
assert property (@(posedge clk_i) disable iff (rst_i) $rose(wb_err_o) |=> $fell(wb_err_o));

assert property (@(posedge clk_i) disable iff (rst_i) $fell(wb_stb_i) |-> ($fell(wb_ack_o) || $fell(wb_err_o)));

//assert property (@(posedge clk_i) disable iff (rst_i) ((wb_stb_i && wb_ack_o) |=> wb_ack_o));
//assert property (@(posedge clk_i) disable iff (rst_i) ((wb_stb_i && wb_err_o) |=> wb_err_o));
//assert property (@(posedge clk_i) disable iff (rst_i) ((wb_stb_i && wb_ack_o && !wb_we_i) |=> $stable(wb_data_o)));
//
// (4)
//assume property (@(posedge clk_i) disable iff (rst_i) (!wb_stb_i && (wb_ack_o || wb_err_o)) |=> !wb_stb_i);
//assert property (@(posedge clk_i) disable iff (rst_i) (!wb_stb_i && wb_ack_o) |-> ##[1:$] !wb_ack_o);
//assert property (@(posedge clk_i) disable iff (rst_i) (!wb_stb_i && wb_err_o) |-> ##[1:$] !wb_err_o);


/////////////////////////////////////////////////////////////////////
//
// Suspend Resume Interface
//
// Reset Condition
// assume property (@(posedge clk_i) rst_i |-> (!susp_req_i && !resume_req_i));    // Declare in ret_check.tcl?
//
// (1)
assert property (@(posedge clk_i) disable iff (rst_i) (!susp_req_i && !suspended_o) |=> !suspended_o);
assume property (@(posedge clk_i) disable iff (rst_i) rst_r1 |-> !resume_req_i);                            // Optional // Note: To avoid signal being asserted right after reset
assume property (@(posedge clk_i) disable iff (rst_i) (!suspended_o && !resume_req_i) |=> !resume_req_i);   // Optional
//
// (2)
assume property (@(posedge clk_i) disable iff (rst_i) (susp_req_i && !suspended_o) |=> susp_req_i);
assert property (@(posedge clk_i) disable iff (rst_i) $rose(susp_req_i) |-> ##[1:$] $rose(suspended_o));
//
// (3)
assume property (@(posedge clk_i) disable iff (rst_i) $rose(suspended_o) |=> $fell(susp_req_i));
//
// (4)
assert property (@(posedge clk_i) disable iff (rst_i) (suspended_o && !resume_req_i) |=> suspended_o);
assume property (@(posedge clk_i) disable iff (rst_i) (suspended_o && !susp_req_i) |=> !susp_req_i);
assume property (@(posedge clk_i) disable iff (rst_i) $fell(susp_req_i) |=> $rose(resume_req_i));           // Optional?
//
// (5)
assume property (@(posedge clk_i) disable iff (rst_i) (resume_req_i && suspended_o) |=> resume_req_i);
assert property (@(posedge clk_i) disable iff (rst_i) $rose(resume_req_i) |-> ##[1:$] $fell(suspended_o));
//
// (6)
assume property (@(posedge clk_i) disable iff (rst_i) $fell(suspended_o) |=> $fell(resume_req_i));  // Covered by other (optional) assumptions


/////////////////////////////////////////////////////////////////////
//
// Memory INTERFACE
//
// Power-On Configuration
reg	rst_r1, rst_r2, rst_r3, rst_r4;

always @(posedge clk_i or posedge rst_i)
	if(rst_i)	rst_r1 <= #1 1'b1;
	else		rst_r1 <= #1 1'b0;

always @(posedge clk_i or posedge rst_i)
	if(rst_i)	rst_r2 <= #1 1'b1;
	else		rst_r2 <= #1 rst_r1;

always @(posedge clk_i or posedge rst_i)
	if(rst_i)	rst_r3 <= #1 1'b1;
	else		rst_r3 <= #1 rst_r2;

always @(posedge clk_i or posedge rst_i)
	if(rst_i)	rst_r4 <= #1 1'b1;
	else		rst_r4 <= #1 rst_r3;

// assume property (@(posedge clk_i) rst_i |-> mc_data_pad_i == {28'hzzz_zzzz, 2'b11, 2'b10});                         // Declare in ret_check.tcl?
assume property (@(posedge clk_i) disable iff (rst_i) rst_r4 |-> mc_data_pad_i == {28'hzzz_zzzz, 2'b11, 2'b10});    // Sync. Device, 32-bit data bus

assert property (@(posedge mc_clk_i) disable iff (rst_i) mc_cs_pad_o_[7:1] == 7'b111_1111);
// assert property (@(posedge mc_clk_i) disable iff (rst_i) mc_cs_pad_o_[0] == 1'b1);

// Connect Chip Select 0 to a Sync. Device
wire mc_cs = mc_coe_pad_coe_o ? mc_cs_pad_o_[0] : 1'b1;
wire mc_oe = mc_coe_pad_coe_o ? mc_oe_pad_o_ : 1'b1;
wire mc_we = mc_coe_pad_coe_o ? mc_we_pad_o_ : 1'b1;
wire rd_or_wr = !mc_cs && (!mc_oe || !mc_we);
//
// assume property (@(posedge clk_i) rst_i |-> !mc_ack_pad_i);
// (1)
assume property (@(posedge clk_i) disable iff (rst_i) rst_r1 |-> !mc_ack_pad_i);                        // Note: To avoid signal being asserted right after reset
assume property (@(posedge mc_clk_i) disable iff (rst_i) (mc_cs && !mc_ack_pad_i) |=> !mc_ack_pad_i);
// assert property (@(posedge mc_clk_i) disable iff (rst_i) mc_cs |-> (mc_oe && mc_we));
//
// (2)
assert property (@(posedge mc_clk_i) disable iff (rst_i) $fell(mc_cs) |=> (!mc_oe || !mc_we));
assert property (@(posedge mc_clk_i) disable iff (rst_i) !(!mc_oe && !mc_we));
assume property (@(posedge mc_clk_i) disable iff (rst_i) (rd_or_wr && !mc_ack_pad_i) |=> mc_ack_pad_i);
//
// (3)
assume property (@(posedge mc_clk_i) disable iff (rst_i) ($past(rd_or_wr) && rd_or_wr) |-> mc_ack_pad_i);
Assert_MC_failed: assert property (@(posedge mc_clk_i) disable iff (rst_i) $rose(mc_ack_pad_i) |-> ##[1:$] $fell(rd_or_wr));
//
// (4)
assume property (@(posedge mc_clk_i) disable iff (rst_i) $fell(rd_or_wr) |-> $fell(mc_ack_pad_i));

// Never assert external bus request
assume property (mc_br_pad_i == 1'b0);
assert property (@(posedge mc_clk_i) disable iff (rst_i) mc_bg_pad_o == 1'b0);
// No parity check for Sync. Device
// assume property (mc_dp_pad_i == 4'b0000);
// assert property (@(posedge mc_clk_i) disable iff (rst_r4) mc_dp_pad_o == 4'b0000);
// Does not connect to SDRAM
// assert property (@(posedge mc_clk_i) disable iff (rst_i) !(susp_req_i || resume_req_i) |=> (mc_cas_pad_o_ == 1'b1));
// assert property (@(posedge mc_clk_i) disable iff (rst_i) !(susp_req_i || resume_req_i) |=> (mc_ras_pad_o_ == 1'b1));
// Does not connect to Flash
assert property (@(posedge mc_clk_i) disable iff (rst_i) !suspended_o |=> (mc_rp_pad_o_ == 1'b1));
//assume property (mc_sts_pad_i == 1'b0);
assert property (@(posedge mc_clk_i) disable iff (rst_i) mc_vpen_pad_o == 1'b0);
// Does not connect to SSRAM
assert property (@(posedge mc_clk_i) disable iff (rst_i) mc_adsc_pad_o_ == 1'b1);
assert property (@(posedge mc_clk_i) disable iff (rst_i) mc_adv_pad_o_ == 1'b1);
assert property (@(posedge mc_clk_i) disable iff (rst_i) !suspended_o |=> (mc_zz_pad_o == 1'b0));


// TODO: interaction between interfaces (Optional)
// No memory operation and suspend request at the same time
assume property (@(posedge clk_i) disable iff (rst_i) !(wb_stb_i && susp_req_i));
