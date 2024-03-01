`include "spi_defines.v"

module spi_qchannel
(
    wb_clk_i, wb_rst_i,

    wb_adr_i, wb_dat_i, wb_dat_o, wb_sel_i, wb_we_i, wb_stb_i, wb_cyc_i, wb_ack_o, wb_err_o, wb_int_o,

    ss_pad_o, sclk_pad_o, mosi_pad_o, miso_pad_i,

    qreqn, qacceptn, qdeny
);

input                            wb_clk_i;         // master clock input
input                            wb_rst_i;         // synchronous active high reset

// Wishbone signals
input                      [4:0] wb_adr_i;         // lower address bits
input                   [32-1:0] wb_dat_i;         // databus input
output                  [32-1:0] wb_dat_o;         // databus output
input                      [3:0] wb_sel_i;         // byte select inputs
input                            wb_we_i;          // write enable input
input                            wb_stb_i;         // stobe/core select signal
input                            wb_cyc_i;         // valid bus cycle input
output                           wb_ack_o;         // bus cycle acknowledge output
output                           wb_err_o;         // termination w/ error
output                           wb_int_o;         // interrupt request signal output

// SPI signals                                     
output          [`SPI_SS_NB-1:0] ss_pad_o;         // slave select
output                           sclk_pad_o;       // serial clock
output                           mosi_pad_o;       // master out slave in
input                            miso_pad_i;       // master in slave out

// Q-Channel Interface
input   qreqn;
output  qacceptn;
output  qdeny;

// wire Q_RUN = qreqn && qacceptn;
// wire Q_REQUEST = !qreqn && qacceptn;
// wire Q_STOPPED = !qreqn && !qacceptn;
// wire Q_EXIT = qreqn && !qacceptn;

localparam ST_STOP  = 2'b00;
localparam ST_RUN   = 2'b01;
localparam ST_PRE   = 2'b10;
localparam ST_PRE_2 = 2'b11;

reg [1:0] state, state_next;

assign qacceptn = (state != ST_STOP);
assign qdeny = 1'b0;

wire [4:0] wb_adr_int = (state == ST_RUN) ? wb_adr_i : 5'b0;
wire [31:0] wb_dat_int = (state == ST_RUN) ? wb_dat_i : 32'b0;
wire [3:0] wb_sel_int = (state == ST_RUN) ? wb_sel_i : 4'b0;
wire wb_we_int = (state == ST_RUN) ? wb_we_i : 1'b0;
wire wb_stb_int = (state == ST_RUN) ? wb_stb_i : 1'b0;
wire wb_cyc_int = (state == ST_RUN) ? wb_cyc_i : 1'b0;
//wire miso_pad_int = (state == ST_RUN) ? miso_pad_i : 1'b0;
wire miso_pad_int = (state != ST_STOP) ? miso_pad_i : 1'b0;

wire tip;

spi_top spi_top_inst
(
    .wb_clk_i(wb_clk_i),
    .wb_rst_i(wb_rst_i),
    .wb_adr_i(wb_adr_int),
    .wb_dat_i(wb_dat_int),
    .wb_dat_o(wb_dat_o),
    .wb_sel_i(wb_sel_int),
    .wb_we_i(wb_we_i),
    .wb_stb_i(wb_stb_int),
    .wb_cyc_i(wb_cyc_int),
    .wb_ack_o(wb_ack_o),
    .wb_err_o(wb_err_o),
    .wb_int_o(wb_int_o),

    .ss_pad_o(ss_pad_o),
    .sclk_pad_o(sclk_pad_o),
    .mosi_pad_o(mosi_pad_o),
    .miso_pad_i(miso_pad_int),

    .tip(tip)
);

always @(*) begin
    
    state_next = state;
    
    case (state)
        ST_STOP: begin
            if (qreqn) begin
                state_next = ST_RUN;
            end
        end
        ST_RUN: begin
            if (!qreqn && !wb_stb_i) begin
                state_next = ST_PRE;
            end
        end
        ST_PRE: begin
            if (!tip) begin
                //state_next = ST_STOP;
                state_next = ST_PRE_2;
            end
        end
        ST_PRE_2: begin
            state_next = ST_STOP;
        end
    endcase
end

always @(posedge wb_clk_i) begin
    if (wb_rst_i) begin
        state <= ST_STOP;
    end
    else begin
        state <= state_next;
    end
end

endmodule