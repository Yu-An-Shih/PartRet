// This is the testbench that wraps the original and partial retention designs.
// This script will be used by the retention explorer tool, 
// so please (only) modify it as instructed (marked with "// TODO: ...") if you want to call the explorer.

module wrapper;

wire wb_clk_i;
wire wb_rst_i;
wire [0:0] miso_pad_i;
wire [0:0] qreqn;
wire [4:0] wb_adr_i;
wire [0:0] wb_cyc_i;
wire [31:0] wb_dat_i;
wire [3:0] wb_sel_i;
wire [0:0] wb_stb_i;
wire [0:0] wb_we_i;
wire [0:0] mosi_pad_o, mosi_pad_o_test;
wire [0:0] qacceptn, qacceptn_test;
wire [0:0] qdeny, qdeny_test;
wire [0:0] sclk_pad_o, sclk_pad_o_test;
wire [7:0] ss_pad_o, ss_pad_o_test;
wire [0:0] wb_ack_o, wb_ack_o_test;
wire [31:0] wb_dat_o, wb_dat_o_test;
wire [0:0] wb_err_o, wb_err_o_test;
wire [0:0] wb_int_o, wb_int_o_test;
wire check_cond;

assign check_cond = qacceptn;

spi_qchannel design_golden (
    .wb_clk_i(wb_clk_i),
    .wb_rst_i(wb_rst_i),
    .miso_pad_i(miso_pad_i),
    .qreqn(qreqn),
    .wb_adr_i(wb_adr_i),
    .wb_cyc_i(wb_cyc_i),
    .wb_dat_i(wb_dat_i),
    .wb_sel_i(wb_sel_i),
    .wb_stb_i(wb_stb_i),
    .wb_we_i(wb_we_i),
    .mosi_pad_o(mosi_pad_o),
    .qacceptn(qacceptn),
    .qdeny(qdeny),
    .sclk_pad_o(sclk_pad_o),
    .ss_pad_o(ss_pad_o),
    .wb_ack_o(wb_ack_o),
    .wb_dat_o(wb_dat_o),
    .wb_err_o(wb_err_o),
    .wb_int_o(wb_int_o)
);

spi_qchannel_test design_test (
    .wb_clk_i(wb_clk_i),
    .wb_rst_i(wb_rst_i),
    .miso_pad_i(miso_pad_i),
    .qreqn(qreqn),
    .wb_adr_i(wb_adr_i),
    .wb_cyc_i(wb_cyc_i),
    .wb_dat_i(wb_dat_i),
    .wb_sel_i(wb_sel_i),
    .wb_stb_i(wb_stb_i),
    .wb_we_i(wb_we_i),
    .mosi_pad_o(mosi_pad_o_test),
    .qacceptn(qacceptn_test),
    .qdeny(qdeny_test),
    .sclk_pad_o(sclk_pad_o_test),
    .ss_pad_o(ss_pad_o_test),
    .wb_ack_o(wb_ack_o_test),
    .wb_dat_o(wb_dat_o_test),
    .wb_err_o(wb_err_o_test),
    .wb_int_o(wb_int_o_test),
    .pr_restore(pr_restore)
);

// TODO: Please add the formal interface constraints either here or in ret_checker.tcl.

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

// Optional: Does not affect the verification result
//assume property (@(posedge wb_clk_i) ($rose(qreqn) |-> ##[1:$] $stable(qreqn)));

// Constraints for retention registers
wire standby_state = !qreqn && !qacceptn;

assume property (@(posedge wb_clk_i) $rose(standby_state) |=> $rose(pr_restore));     // Added to increase verification speed
assume property (@(posedge wb_clk_i) ($rose(pr_restore) |-> $past(standby_state)));
assume property (@(posedge wb_clk_i) ($rose(pr_restore) |=> $rose(qreqn) && $fell(pr_restore)));
assume property (@(posedge wb_clk_i) (standby_state && !pr_restore |=> !qreqn));

endmodule
