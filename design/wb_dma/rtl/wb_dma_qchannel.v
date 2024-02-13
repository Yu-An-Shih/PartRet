module wb_dma_qchannel
(
    clk_i, rst_i,

    wb0s_data_i, wb0s_data_o, wb0_addr_i, wb0_sel_i, wb0_we_i, wb0_cyc_i,
	wb0_stb_i, wb0_ack_o, wb0_err_o, wb0_rty_o,
	wb0m_data_i, wb0m_data_o, wb0_addr_o, wb0_sel_o, wb0_we_o, wb0_cyc_o,
	wb0_stb_o, wb0_ack_i, wb0_err_i, wb0_rty_i,

    wb1s_data_i, wb1s_data_o, wb1_addr_i, wb1_sel_i, wb1_we_i, wb1_cyc_i,
	wb1_stb_i, wb1_ack_o, wb1_err_o, wb1_rty_o,
	wb1m_data_i, wb1m_data_o, wb1_addr_o, wb1_sel_o, wb1_we_o, wb1_cyc_o,
	wb1_stb_o, wb1_ack_i, wb1_err_i, wb1_rty_i,

    dma_req_i, dma_ack_o, dma_nd_i, dma_rest_i,
    inta_o, intb_o,

    qreqn, qacceptn, qdeny
);

// Module Parameters
parameter ch_count = 1;

input clk_i, rst_i;

// --------------------------------------
// WISHBONE INTERFACE 0

// Slave Interface
input	[31:0]	wb0s_data_i;
output  [31:0]	wb0s_data_o;
input	[31:0]	wb0_addr_i;
input	[3:0]	wb0_sel_i;
input		    wb0_we_i;
input		    wb0_cyc_i;
input		    wb0_stb_i;
output		    wb0_ack_o;
output		    wb0_err_o;
output		    wb0_rty_o;

// Master Interface
input	[31:0]	wb0m_data_i;
output	[31:0]	wb0m_data_o;
output	[31:0]	wb0_addr_o;
output	[3:0]	wb0_sel_o;
output		    wb0_we_o;
output		    wb0_cyc_o;
output		    wb0_stb_o;
input		    wb0_ack_i;
input		    wb0_err_i;
input		    wb0_rty_i;

// --------------------------------------
// WISHBONE INTERFACE 1

// Slave Interface
input	[31:0]	wb1s_data_i;
output	[31:0]	wb1s_data_o;
input	[31:0]	wb1_addr_i;
input	[3:0]	wb1_sel_i;
input		    wb1_we_i;
input		    wb1_cyc_i;
input		    wb1_stb_i;
output		    wb1_ack_o;
output		    wb1_err_o;
output		    wb1_rty_o;

// Master Interface
input	[31:0]	wb1m_data_i;
output	[31:0]	wb1m_data_o;
output	[31:0]	wb1_addr_o;
output	[3:0]	wb1_sel_o;
output		    wb1_we_o;
output		    wb1_cyc_o;
output		    wb1_stb_o;
input		    wb1_ack_i;
input		    wb1_err_i;
input		    wb1_rty_i;

// --------------------------------------
// Misc Signals
input	[ch_count-1:0]	dma_req_i;
output	[ch_count-1:0]	dma_ack_o;
input	[ch_count-1:0]	dma_nd_i;
input	[ch_count-1:0]	dma_rest_i;
output			        inta_o;
output			        intb_o;

// Q-Channel Interface
input   qreqn;
output  qacceptn;
output  qdeny;


localparam ST_STOP = 2'b00;
localparam ST_RUN  = 2'b01;
localparam ST_PRE  = 2'b10;
//localparam ST_PRE2 = 2'b11;

reg [1:0] state, state_next;
reg [2:0] counter, counter_next;

assign qacceptn = (state != ST_STOP);
assign qdeny = 1'b0;

wire ready_to_stop = !wb0_cyc_i && !wb0_cyc_o && !wb1_cyc_i && !wb1_cyc_o;

wire [31:0] wb0s_data_int = (state == ST_RUN) ? wb0s_data_i : 32'b0;
wire [31:0] wb0_addr_int = (state == ST_RUN) ? wb0_addr_i : 32'b0;
wire [3:0]  wb0_sel_int = (state == ST_RUN) ? wb0_sel_i : 4'b0;
wire        wb0_we_int = (state == ST_RUN) ? wb0_we_i : 1'b0;
wire        wb0_cyc_int = (state == ST_RUN) ? wb0_cyc_i : 1'b0;
wire        wb0_stb_int = (state == ST_RUN) ? wb0_stb_i : 1'b0;

wire [31:0] wb0m_data_int = (state == ST_RUN) ? wb0m_data_i : 32'b0;
wire        wb0_ack_int = (state == ST_RUN) ? wb0_ack_i : 1'b0;
wire        wb0_err_int = (state == ST_RUN) ? wb0_err_i : 1'b0;
wire        wb0_rty_int = (state == ST_RUN) ? wb0_rty_i : 1'b0;

wire [31:0] wb1s_data_int = (state == ST_RUN) ? wb1s_data_i : 32'b0;
wire [31:0] wb1_addr_int = (state == ST_RUN) ? wb1_addr_i : 32'b0;
wire [3:0]  wb1_sel_int = (state == ST_RUN) ? wb1_sel_i : 4'b0;
wire        wb1_we_int = (state == ST_RUN) ? wb1_we_i : 1'b0;
wire        wb1_cyc_int = (state == ST_RUN) ? wb1_cyc_i : 1'b0;
wire        wb1_stb_int = (state == ST_RUN) ? wb1_stb_i : 1'b0;

wire [31:0] wb1m_data_int = (state == ST_RUN) ? wb1m_data_i : 32'b0;
wire        wb1_ack_int = (state == ST_RUN) ? wb1_ack_i : 1'b0;
wire        wb1_err_int = (state == ST_RUN) ? wb1_err_i : 1'b0;
wire        wb1_rty_int = (state == ST_RUN) ? wb1_rty_i : 1'b0;

wire [ch_count-1:0] dma_req_int = (state == ST_RUN) ? dma_req_i : {ch_count{1'b0}};
wire [ch_count-1:0] dma_nd_int = (state == ST_RUN) ? dma_nd_i : {ch_count{1'b0}};
wire [ch_count-1:0] dma_rest_int = (state == ST_RUN) ? dma_rest_i : {ch_count{1'b0}};

// top module instantiation
wb_dma_top #(
    .ch_count(ch_count)
) wb_dma_top_inst (
    .clk_i(clk_i),
    .rst_i(rst_i),

    .wb0s_data_i(wb0s_data_int),
    .wb0s_data_o(wb0s_data_o),
    .wb0_addr_i(wb0_addr_int),
    .wb0_sel_i(wb0_sel_int),
    .wb0_we_i(wb0_we_int),
    .wb0_cyc_i(wb0_cyc_int),
    .wb0_stb_i(wb0_stb_int),
    .wb0_ack_o(wb0_ack_o),
    .wb0_err_o(wb0_err_o),
    .wb0_rty_o(wb0_rty_o),

    .wb0m_data_i(wb0m_data_int),
    .wb0m_data_o(wb0m_data_o),
    .wb0_addr_o(wb0_addr_o),
    .wb0_sel_o(wb0_sel_o),
    .wb0_we_o(wb0_we_o),
    .wb0_cyc_o(wb0_cyc_o),
    .wb0_stb_o(wb0_stb_o),
    .wb0_ack_i(wb0_ack_int),
    .wb0_err_i(wb0_err_int),
    .wb0_rty_i(wb0_rty_int),

    .wb1s_data_i(wb1s_data_int),
    .wb1s_data_o(wb1s_data_o),
    .wb1_addr_i(wb1_addr_int),
    .wb1_sel_i(wb1_sel_int),
    .wb1_we_i(wb1_we_int),
    .wb1_cyc_i(wb1_cyc_int),
    .wb1_stb_i(wb1_stb_int),
    .wb1_ack_o(wb1_ack_o),
    .wb1_err_o(wb1_err_o),
    .wb1_rty_o(wb1_rty_o),

    .wb1m_data_i(wb1m_data_int),
    .wb1m_data_o(wb1m_data_o),
    .wb1_addr_o(wb1_addr_o),
    .wb1_sel_o(wb1_sel_o),
    .wb1_we_o(wb1_we_o),
    .wb1_cyc_o(wb1_cyc_o),
    .wb1_stb_o(wb1_stb_o),
    .wb1_ack_i(wb1_ack_int),
    .wb1_err_i(wb1_err_int),
    .wb1_rty_i(wb1_rty_int),

    .dma_req_i(dma_req_int),
    .dma_ack_o(dma_ack_o),
    .dma_nd_i(dma_nd_int),
    .dma_rest_i(dma_rest_int),
    .inta_o(inta_o),
    .intb_o(intb_o)
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
            if (!qreqn && ready_to_stop) begin
                state_next = ST_PRE;
            end
        end
        ST_PRE: begin
            counter_next = counter + 3'b1;
            if (counter == 3'b100) begin
                state_next = ST_STOP;
                counter_next = 3'b0;
            end
        end
        /*ST_PRE2: begin
            state_next = ST_STOP;
        end*/
    endcase
end

always @(posedge clk_i) begin
    if (rst_i) begin
        state <= ST_STOP;
        counter <= 3'b0;
    end
    else begin
        state <= state_next;
        counter <= counter_next;
    end
end
    
endmodule