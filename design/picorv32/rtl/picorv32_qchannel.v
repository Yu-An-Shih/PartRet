module picorv32_qchannel
(
    clk, resetn,
    trap,
    // Memory Interface
    mem_valid, mem_instr, mem_ready, mem_addr, mem_wdata, mem_wstrb, mem_rdata,
    // Look-Ahead Interface
    mem_la_read, mem_la_write, mem_la_addr, mem_la_wdata, mem_la_wstrb,
    // Pico Co-Processor Interface (PCPI)
    pcpi_valid, pcpi_insn, pcpi_rs1, pcpi_rs2, pcpi_wr, pcpi_rd, pcpi_wait, pcpi_ready,
    // IRQ Interface
    irq, eoi,
    // Trace Interface
    trace_valid, trace_data,
    // Q-Channel Interface
    qreqn, qacceptn, qdeny
);

input clk;
input resetn;

output trap;

// Memory Interface
output        mem_valid;
output        mem_instr;
input         mem_ready;
output [31:0] mem_addr;
output [31:0] mem_wdata;
output [ 3:0] mem_wstrb;
input  [31:0] mem_rdata;

// Look-Ahead Interface
output        mem_la_read;
output        mem_la_write;
output [31:0] mem_la_addr;
output [31:0] mem_la_wdata;
output [ 3:0] mem_la_wstrb;

// Pico Co-Processor Interface (PCPI)
output        pcpi_valid;
output [31:0] pcpi_insn;
output [31:0] pcpi_rs1;
output [31:0] pcpi_rs2;
input         pcpi_wr;
input  [31:0] pcpi_rd;
input         pcpi_wait;
input         pcpi_ready;

// IRQ Interface
input  [31:0] irq;
output [31:0] eoi;

// Trace Interface
output        trace_valid;
output [35:0] trace_data;

// Q-Channel Interface
input   qreqn;
output  qacceptn;
output  qdeny;

localparam ST_STOP  = 2'b00;
localparam ST_RUN   = 2'b01;
localparam ST_PRE   = 2'b10;
//localparam ST_PRE_2 = 2'b11;

reg [1:0] state, state_next;
reg [1:0] counter, counter_next;

assign qacceptn = (state != ST_STOP);
assign qdeny = 1'b0;

wire        mem_ready_int = (state == ST_RUN) ? mem_ready : 1'b0;
wire [31:0] mem_rdata_int = (state == ST_RUN) ? mem_rdata : 32'b0;
wire        pcpi_wr_int = (state == ST_RUN) ? pcpi_wr : 1'b0;
wire [31:0] pcpi_rd_int = (state == ST_RUN) ? pcpi_rd : 32'b0;
wire        pcpi_wait_int = (state == ST_RUN) ? pcpi_wait : 1'b0;
wire        pcpi_ready_int = (state == ST_RUN) ? pcpi_ready : 1'b0;
wire [31:0] irq_int = (state == ST_RUN) ? irq : 32'b0;

wire mem_valid_int;
wire mem_instr_int;

assign mem_valid = (state == ST_RUN) ? mem_valid_int : 1'b0;
assign mem_instr = (state == ST_RUN) ? mem_instr_int : 1'b0;

wire inst_fetching = mem_valid_int && mem_instr_int && !mem_ready_int;

wire [7:0] cpu_state;

picorv32 #(
    .ENABLE_COUNTERS(0),
    .ENABLE_COUNTERS64(0)
) picorv32_inst (
    .clk(clk),
    .resetn(resetn),
    .trap(trap),
    // Memory Interface
    .mem_valid(mem_valid_int),
    .mem_instr(mem_instr_int),
    .mem_ready(mem_ready_int),
    .mem_addr(mem_addr),
    .mem_wdata(mem_wdata),
    .mem_wstrb(mem_wstrb),
    .mem_rdata(mem_rdata_int),
    // Look-Ahead Interface
    .mem_la_read(mem_la_read),
    .mem_la_write(mem_la_write),
    .mem_la_addr(mem_la_addr),
    .mem_la_wdata(mem_la_wdata),
    .mem_la_wstrb(mem_la_wstrb),
    // Pico Co-Processor Interface (PCPI)
    .pcpi_valid(pcpi_valid),
    .pcpi_insn(pcpi_insn),
    .pcpi_rs1(pcpi_rs1),
    .pcpi_rs2(pcpi_rs2),
    .pcpi_wr(pcpi_wr_int),
    .pcpi_rd(pcpi_rd_int),
    .pcpi_wait(pcpi_wait_int),
    .pcpi_ready(pcpi_ready_int),
    // IRQ Interface
    .irq(irq_int),
    .eoi(eoi),
    // Trace Interface
    .trace_valid(trace_valid),
    .trace_data(trace_data),
    // For power-down decisions
    .cpu_state_o(cpu_state)
);

always @(*) begin
    
    state_next = state;
    counter_next = counter;
    
    case (state)
        ST_STOP: begin
            if (qreqn) begin
                state_next = ST_RUN;
            end
        end
        ST_RUN: begin
            if (!qreqn && !inst_fetching) begin
                state_next = ST_PRE;
            end
        end
        ST_PRE: begin
            if (cpu_state == 8'b01000000 || cpu_state == 8'b00000010 || cpu_state == 8'b00000001 || cpu_state == 8'b00001000) begin // cpu_state_fetch, cpu_state_stmem, cpu_state_ldmem, cpu_state_exec
                counter_next = counter + 2'b1;
                if (counter == 2'b11) begin
                    state_next = ST_STOP;
                end
            end else begin
                counter_next = 2'b0;
            end
        end
        /*ST_PRE_2: begin
            state_next = ST_STOP;
        end*/
    endcase
end

always @(posedge clk) begin
    if (!resetn) begin
        state <= ST_STOP;
        counter <= 2'b0;
    end
    else begin
        state <= state_next;
        counter <= counter_next;
    end
end

endmodule