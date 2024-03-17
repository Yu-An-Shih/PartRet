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

// Constraints for retention registers
wire standby_state = !qreqn && !qacceptn;

assume property (@(posedge clk) ($rose(pr_restore) |-> $past(standby_state)));
assume property (@(posedge clk) ($rose(pr_restore) |=> $rose(qreqn) && $fell(pr_restore)));
assume property (@(posedge clk) (standby_state && !pr_restore |=> !qreqn));
