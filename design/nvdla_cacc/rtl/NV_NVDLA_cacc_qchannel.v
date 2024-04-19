module NV_NVDLA_cacc_qchannel (
    nvdla_core_clk,
    nvdla_core_rstn,

    csb2cacc_req_pvld,
    csb2cacc_req_prdy,
    csb2cacc_req_pd,

    cacc2csb_resp_valid,
    cacc2csb_resp_pd,
    
    mac_a2accu_pvld,
    mac_a2accu_mask,
    mac_a2accu_mode,
    mac_a2accu_data0,
    mac_a2accu_data1,
    mac_a2accu_data2,
    mac_a2accu_data3,
    mac_a2accu_data4,
    mac_a2accu_data5,
    mac_a2accu_data6,
    mac_a2accu_data7,
    mac_a2accu_pd,

    mac_b2accu_pvld,
    mac_b2accu_mask,
    mac_b2accu_mode,
    mac_b2accu_data0,
    mac_b2accu_data1,
    mac_b2accu_data2,
    mac_b2accu_data3,
    mac_b2accu_data4,
    mac_b2accu_data5,
    mac_b2accu_data6,
    mac_b2accu_data7,
    mac_b2accu_pd,

    cacc2sdp_valid,
    cacc2sdp_ready,
    cacc2sdp_pd,

    accu2sc_credit_vld,
    accu2sc_credit_size,

    cacc2glb_done_intr_pd,
    // Q-Channel Interface
    qreqn,
    qacceptn,
    qdeny
);

input  nvdla_core_clk;   /* csb2cacc_req, cacc2csb_resp, mac_a2accu, mac_b2accu, cacc2sdp, accu2sc_credit, cacc2glb_done_intr */
input  nvdla_core_rstn;  /* csb2cacc_req, cacc2csb_resp, mac_a2accu, mac_b2accu, cacc2sdp, accu2sc_credit, cacc2glb_done_intr */

input         csb2cacc_req_pvld;  /* data valid */
output        csb2cacc_req_prdy;  /* data return handshake */
input  [62:0] csb2cacc_req_pd;

output        cacc2csb_resp_valid;  /* data valid */
output [33:0] cacc2csb_resp_pd;     /* pkt_id_width=1 pkt_widths=33,33  */

input         mac_a2accu_pvld;   /* data valid */
input   [7:0] mac_a2accu_mask;
input   [7:0] mac_a2accu_mode;
input [175:0] mac_a2accu_data0;
input [175:0] mac_a2accu_data1;
input [175:0] mac_a2accu_data2;
input [175:0] mac_a2accu_data3;
input [175:0] mac_a2accu_data4;
input [175:0] mac_a2accu_data5;
input [175:0] mac_a2accu_data6;
input [175:0] mac_a2accu_data7;
input   [8:0] mac_a2accu_pd;

input         mac_b2accu_pvld;   /* data valid */
input   [7:0] mac_b2accu_mask;
input   [7:0] mac_b2accu_mode;
input [175:0] mac_b2accu_data0;
input [175:0] mac_b2accu_data1;
input [175:0] mac_b2accu_data2;
input [175:0] mac_b2accu_data3;
input [175:0] mac_b2accu_data4;
input [175:0] mac_b2accu_data5;
input [175:0] mac_b2accu_data6;
input [175:0] mac_b2accu_data7;
input   [8:0] mac_b2accu_pd;

output         cacc2sdp_valid;  /* data valid */
input          cacc2sdp_ready;  /* data return handshake */
output [513:0] cacc2sdp_pd;

output       accu2sc_credit_vld;   /* data valid */
output [2:0] accu2sc_credit_size;

output [1:0] cacc2glb_done_intr_pd;

// Q-Channel Interface
input   qreqn;
output  qacceptn;
output  qdeny;

localparam ST_STOP = 2'b00;
localparam ST_RUN  = 2'b01;
localparam ST_PRE  = 2'b10;
localparam ST_PRE2 = 2'b11;

reg [1:0] state, state_next;
reg [3:0] counter, counter_next;

assign qacceptn = (state != ST_STOP);
assign qdeny = 1'b0;

//wire ready_to_stop = !reg2dp_op_en && !csb2cacc_req_pvld;

wire csb2cacc_req_pvld_int = (state == ST_RUN) ? csb2cacc_req_pvld : 1'b0;
wire [7:0] mac_a2accu_mask_int = (state == ST_RUN) ? mac_a2accu_mask : 8'b0;
wire [7:0] mac_a2accu_mode_int = (state == ST_RUN) ? mac_a2accu_mode : 8'b0;
wire [8:0] mac_a2accu_pd_int = (state == ST_RUN) ? mac_a2accu_pd : 9'b0;
wire       mac_a2accu_pvld_int = (state == ST_RUN) ? mac_a2accu_pvld : 1'b0;
wire [7:0] mac_b2accu_mask_int = (state == ST_RUN) ? mac_b2accu_mask : 8'b0;
wire [7:0] mac_b2accu_mode_int = (state == ST_RUN) ? mac_b2accu_mode : 8'b0;
wire [8:0] mac_b2accu_pd_int = (state == ST_RUN) ? mac_b2accu_pd : 9'b0;
wire       mac_b2accu_pvld_int = (state == ST_RUN) ? mac_b2accu_pvld : 1'b0;
wire cacc2sdp_ready_int = (state == ST_RUN) ? cacc2sdp_ready : 1'b0;

// top module instantiation
NV_NVDLA_cacc NV_NVDLA_cacc_inst (
    .nvdla_core_clk(nvdla_core_clk),
    .nvdla_core_rstn(nvdla_core_rstn),

    .dla_clk_ovr_on_sync(1'b0),
    .global_clk_ovr_on_sync(1'b0),
    .tmc2slcg_disable_clock_gating(1'b0),
    .pwrbus_ram_pd(32'b0),

    .csb2cacc_req_pvld(csb2cacc_req_pvld_int),
    .csb2cacc_req_prdy(csb2cacc_req_prdy),
    .csb2cacc_req_pd(csb2cacc_req_pd),

    .cacc2csb_resp_valid(cacc2csb_resp_valid),
    .cacc2csb_resp_pd(cacc2csb_resp_pd),

    .mac_a2accu_data0(mac_a2accu_data0),
    .mac_a2accu_data1(mac_a2accu_data1),
    .mac_a2accu_data2(mac_a2accu_data2),
    .mac_a2accu_data3(mac_a2accu_data3),
    .mac_a2accu_data4(mac_a2accu_data4),
    .mac_a2accu_data5(mac_a2accu_data5),
    .mac_a2accu_data6(mac_a2accu_data6),
    .mac_a2accu_data7(mac_a2accu_data7),
    .mac_a2accu_mask(mac_a2accu_mask_int),
    .mac_a2accu_mode(mac_a2accu_mode_int),
    .mac_a2accu_pd(mac_a2accu_pd_int),
    .mac_a2accu_pvld(mac_a2accu_pvld_int),
    .mac_b2accu_data0(mac_b2accu_data0),
    .mac_b2accu_data1(mac_b2accu_data1),
    .mac_b2accu_data2(mac_b2accu_data2),
    .mac_b2accu_data3(mac_b2accu_data3),
    .mac_b2accu_data4(mac_b2accu_data4),
    .mac_b2accu_data5(mac_b2accu_data5),
    .mac_b2accu_data6(mac_b2accu_data6),
    .mac_b2accu_data7(mac_b2accu_data7),
    .mac_b2accu_mask(mac_b2accu_mask_int),
    .mac_b2accu_mode(mac_b2accu_mode_int),
    .mac_b2accu_pd(mac_b2accu_pd_int),
    .mac_b2accu_pvld(mac_b2accu_pvld_int),

    .cacc2sdp_pd(cacc2sdp_pd),
    .cacc2sdp_valid(cacc2sdp_valid),
    .cacc2sdp_ready(cacc2sdp_ready_int),

    .accu2sc_credit_size(accu2sc_credit_size),
    .accu2sc_credit_vld(accu2sc_credit_vld),

    .cacc2glb_done_intr_pd(cacc2glb_done_intr_pd),

    .reg2dp_op_en_ori(reg2dp_op_en_ori)
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
            //if (!qreqn && ready_to_stop) begin
            if (!qreqn && !csb2cacc_req_pvld) begin
                state_next = ST_PRE;
            end
        end
        ST_PRE: begin
            if (!reg2dp_op_en_ori)
                counter_next = counter + 4'b1;
            else
                counter_next = 4'b0;
            
            if (counter == 4'b0001) begin
                state_next = ST_PRE2;
                //counter_next = 4'b0;
            end
        end
        ST_PRE2: begin
            counter_next = counter + 4'b1;
            if (counter == 4'b1111) begin
                state_next = ST_STOP;
                //counter_next = 4'b0;
            end
        end
    endcase
end

always @(posedge nvdla_core_clk) begin
    if (!nvdla_core_rstn) begin
        state <= ST_STOP;
        counter <= 4'b0;
    end
    else begin
        state <= state_next;
        counter <= counter_next;
    end
end

endmodule