// This is the testbench that wraps the original and partial retention designs.
// This script will be used by the retention explorer tool, 
// so please (only) modify it as instructed (marked with "// TODO: ...") if you want to call the explorer.

module wrapper;

wire clk;
wire resetn;
wire [31:0] irq;
wire [31:0] mem_rdata;
wire [0:0] mem_ready;
wire [31:0] pcpi_rd;
wire [0:0] pcpi_ready;
wire [0:0] pcpi_wait;
wire [0:0] pcpi_wr;
wire [0:0] qreqn;
wire [31:0] eoi, eoi_test;
wire [31:0] mem_addr, mem_addr_test;
wire [0:0] mem_instr, mem_instr_test;
wire [31:0] mem_la_addr, mem_la_addr_test;
wire [0:0] mem_la_read, mem_la_read_test;
wire [31:0] mem_la_wdata, mem_la_wdata_test;
wire [0:0] mem_la_write, mem_la_write_test;
wire [3:0] mem_la_wstrb, mem_la_wstrb_test;
wire [0:0] mem_valid, mem_valid_test;
wire [31:0] mem_wdata, mem_wdata_test;
wire [3:0] mem_wstrb, mem_wstrb_test;
wire [31:0] pcpi_insn, pcpi_insn_test;
wire [31:0] pcpi_rs1, pcpi_rs1_test;
wire [31:0] pcpi_rs2, pcpi_rs2_test;
wire [0:0] pcpi_valid, pcpi_valid_test;
wire [0:0] qacceptn, qacceptn_test;
wire [0:0] qdeny, qdeny_test;
wire [35:0] trace_data, trace_data_test;
wire [0:0] trace_valid, trace_valid_test;
wire [0:0] trap, trap_test;
wire check_cond;

assign check_cond = qacceptn;

picorv32_qchannel design_golden (
    .clk(clk),
    .resetn(resetn),
    .irq(irq),
    .mem_rdata(mem_rdata),
    .mem_ready(mem_ready),
    .pcpi_rd(pcpi_rd),
    .pcpi_ready(pcpi_ready),
    .pcpi_wait(pcpi_wait),
    .pcpi_wr(pcpi_wr),
    .qreqn(qreqn),
    .eoi(eoi),
    .mem_addr(mem_addr),
    .mem_instr(mem_instr),
    .mem_la_addr(mem_la_addr),
    .mem_la_read(mem_la_read),
    .mem_la_wdata(mem_la_wdata),
    .mem_la_write(mem_la_write),
    .mem_la_wstrb(mem_la_wstrb),
    .mem_valid(mem_valid),
    .mem_wdata(mem_wdata),
    .mem_wstrb(mem_wstrb),
    .pcpi_insn(pcpi_insn),
    .pcpi_rs1(pcpi_rs1),
    .pcpi_rs2(pcpi_rs2),
    .pcpi_valid(pcpi_valid),
    .qacceptn(qacceptn),
    .qdeny(qdeny),
    .trace_data(trace_data),
    .trace_valid(trace_valid),
    .trap(trap)
);

picorv32_qchannel_test design_test (
    .clk(clk),
    .resetn(resetn),
    .irq(irq),
    .mem_rdata(mem_rdata),
    .mem_ready(mem_ready),
    .pcpi_rd(pcpi_rd),
    .pcpi_ready(pcpi_ready),
    .pcpi_wait(pcpi_wait),
    .pcpi_wr(pcpi_wr),
    .qreqn(qreqn),
    .eoi(eoi_test),
    .mem_addr(mem_addr_test),
    .mem_instr(mem_instr_test),
    .mem_la_addr(mem_la_addr_test),
    .mem_la_read(mem_la_read_test),
    .mem_la_wdata(mem_la_wdata_test),
    .mem_la_write(mem_la_write_test),
    .mem_la_wstrb(mem_la_wstrb_test),
    .mem_valid(mem_valid_test),
    .mem_wdata(mem_wdata_test),
    .mem_wstrb(mem_wstrb_test),
    .pcpi_insn(pcpi_insn_test),
    .pcpi_rs1(pcpi_rs1_test),
    .pcpi_rs2(pcpi_rs2_test),
    .pcpi_valid(pcpi_valid_test),
    .qacceptn(qacceptn_test),
    .qdeny(qdeny_test),
    .trace_data(trace_data_test),
    .trace_valid(trace_valid_test),
    .trap(trap_test),
    .pr_restore(pr_restore)
);

// TODO: Please add the formal interface constraints either here or in ret_checker.tcl.

// Memory Interface
//assume property (@(posedge clk) (mem_valid |-> ##[0:$] mem_ready));
assume property (@(posedge clk) (mem_ready == 1'b1));

//assert property (@(posedge clk) ($fell(mem_valid) |-> $past(mem_ready)));

assert property (@(posedge clk) (mem_wstrb == 4'b0000 || mem_wstrb == 4'b1111 || mem_wstrb == 4'b0011 || mem_wstrb == 4'b1100
                                || mem_wstrb == 4'b0001 || mem_wstrb == 4'b0010 || mem_wstrb == 4'b0100 || mem_wstrb == 4'b1000));

wire inst_fetch = (mem_valid && mem_instr && mem_ready);
// TODO: instruction encoding
// ADD
//assume property (@(posedge clk) (inst_fetch |-> mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b000 && mem_rdata[31:25] == 7'b0000000));
wire is_reg_reg = (mem_rdata[6:0] == 7'b0110011) && ((mem_rdata[31:25] == 7'b0000000) || ((mem_rdata[31:25] == 7'b0100000) && ((mem_rdata[14:12] == 3'b000) || (mem_rdata[14:12] == 3'b101))));
wire is_reg_imm = (mem_rdata[6:0] == 7'b0010011) && (!(mem_rdata[14:12] == 3'b001) || (mem_rdata[31:25] == 7'b0000000)) && (!(mem_rdata[14:12] == 3'b101) || ((mem_rdata[31:25] == 7'b0100000) || (mem_rdata[31:25] == 7'b0000000)) );
//wire is_load = (mem_rdata[6:0] == 7'b0000011) && ((mem_rdata[14:12] == 3'b000) || (mem_rdata[14:12] == 3'b001) || (mem_rdata[14:12] == 3'b010) || (mem_rdata[14:12] == 3'b100) || (mem_rdata[14:12] == 3'b101));
wire is_load_byte = (mem_rdata[6:0] == 7'b0000011) && ((mem_rdata[14:12] == 3'b000) || (mem_rdata[14:12] == 3'b100));
//wire is_store = (mem_rdata[6:0] == 7'b0100011) && ((mem_rdata[14:12] == 3'b000) || (mem_rdata[14:12] == 3'b001) || (mem_rdata[14:12] == 3'b010));
wire is_store_byte = (mem_rdata[6:0] == 7'b0100011) && (mem_rdata[14:12] == 3'b000);
//wire is_jump = (mem_rdata[6:0] == 7'b1101111) || ((mem_rdata[6:0] == 7'b1100111) && (mem_rdata[14:12] == 3'b000));
wire is_jal = ((mem_rdata[6:0] == 7'b1101111) && (mem_rdata[21] == 1'b0));
//wire is_branch = (mem_rdata[6:0] == 7'b1100011) && ((mem_rdata[14:12] != 3'b010) && (mem_rdata[14:12] != 3'b011));
wire is_branch = (mem_rdata[6:0] == 7'b1100011) && ((mem_rdata[14:12] != 3'b010) && (mem_rdata[14:12] != 3'b011)) && (mem_rdata[8:7] == 2'b00);
wire is_lui = (mem_rdata[6:0] == 7'b0110111);
wire is_auipc = (mem_rdata[6:0] == 7'b0010111);

assume property (@(posedge clk) (inst_fetch |-> (is_reg_reg || is_reg_imm || is_load_byte || is_store_byte || is_jal || is_branch || is_lui || is_auipc)));
//assume property (@(posedge clk) (inst_fetch |-> (is_reg_reg || is_reg_imm || is_load_byte || is_store_byte || is_jal || is_branch || is_lui || is_auipc)));

assert property (@(posedge clk) (trap == 1'b0));
assert property (@(posedge clk) ($fell(qreqn) |-> ##[1:$] $fell(qacceptn)));


// Pico Co-Processor Interface (PCPI)
assert property (@(posedge clk) (pcpi_valid == 1'b0));  // PCPI not activated

assume property (@(posedge clk) (pcpi_ready == 1'b0));
assume property (@(posedge clk) (pcpi_wait == 1'b0));


// IRQ Interface
assume property (@(posedge clk) (irq == 32'h0));  // No IRQs
assert property (@(posedge clk) (eoi == 32'h0));


// Trace Interface
assert property (@(posedge clk) (trace_valid == 1'b0));  // No execution trace
assert property (@(posedge clk) (trace_data == 36'h0));


// Q-channel interface
assume property (@(posedge clk) ($fell(qreqn) |-> $past(qacceptn && !qdeny)));
assume property (@(posedge clk) ($rose(qreqn) |-> $past(qacceptn == qdeny)));

assert property (@(posedge clk) ($fell(qacceptn) |-> $past(!qreqn && !qdeny)));
assert property (@(posedge clk) ($rose(qacceptn) |-> $past(qreqn && !qdeny)));
assert property (@(posedge clk) ($fell(qdeny) |-> $past(qreqn && qacceptn)));
assert property (@(posedge clk) ($rose(qdeny) |-> $past(!qreqn && qacceptn)));

// Optional Q-channel assumption
//assume property (@(posedge clk) ($fell(qreqn) |-> ##[1:$] $rose(qreqn)));

// Optional: Does not affect the verification result
//assume property (@(posedge clk) ($rose(qreqn) |-> ##[1:$] $stable(qreqn)));

// Constraints for retention registers
wire standby_state = !qreqn && !qacceptn;

assume property (@(posedge clk) $rose(standby_state) |=> $rose(pr_restore));     // Added to increase verification speed
assume property (@(posedge clk) ($rose(pr_restore) |-> $past(standby_state)));
assume property (@(posedge clk) ($rose(pr_restore) |=> $rose(qreqn) && $fell(pr_restore)));
assume property (@(posedge clk) (standby_state && !pr_restore |=> !qreqn));

endmodule
