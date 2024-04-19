module NV_NVDLA_cacc_qchannel (
    nvdla_core_clk,
    nvdla_core_rstn,

    csb2cacc_req_pvld,
    csb2cacc_req_prdy,
    csb2cacc_req_pd,

    cacc2csb_resp_valid,
    cacc2csb_resp_pd,
    // New inputs
    dp2reg_done,
    dp2reg_sat_count,
    // New outputs
    reg2dp_batches,
    reg2dp_clip_truncate,
    reg2dp_conv_mode,
    reg2dp_cya,
    reg2dp_dataout_addr,
    reg2dp_dataout_channel,
    reg2dp_dataout_height,
    reg2dp_dataout_width,
    reg2dp_line_packed,
    reg2dp_line_stride,
    reg2dp_op_en,
    reg2dp_proc_precision,
    reg2dp_surf_packed,
    reg2dp_surf_stride,
    slcg_op_en
    // Q-Channel Interface
    ,qreqn
    ,qacceptn
    ,qdeny
);

input  nvdla_core_clk;   /* csb2cacc_req, cacc2csb_resp, mac_a2accu, mac_b2accu, cacc2sdp, accu2sc_credit, cacc2glb_done_intr */
input  nvdla_core_rstn;  /* csb2cacc_req, cacc2csb_resp, mac_a2accu, mac_b2accu, cacc2sdp, accu2sc_credit, cacc2glb_done_intr */

input         csb2cacc_req_pvld;  /* data valid */
output        csb2cacc_req_prdy;  /* data return handshake */
input  [62:0] csb2cacc_req_pd;

output        cacc2csb_resp_valid;  /* data valid */
output [33:0] cacc2csb_resp_pd;     /* pkt_id_width=1 pkt_widths=33,33  */

// New inputs
input         dp2reg_done;
input  [31:0] dp2reg_sat_count;
// New outputs
output  [4:0] reg2dp_batches;
output  [4:0] reg2dp_clip_truncate;
output  [0:0] reg2dp_conv_mode;
output [31:0] reg2dp_cya;
output [26:0] reg2dp_dataout_addr;
output [12:0] reg2dp_dataout_channel;
output [12:0] reg2dp_dataout_height;
output [12:0] reg2dp_dataout_width;
output  [0:0] reg2dp_line_packed;
output [18:0] reg2dp_line_stride;
output  [0:0] reg2dp_op_en;
output  [1:0] reg2dp_proc_precision;
output  [0:0] reg2dp_surf_packed;
output [18:0] reg2dp_surf_stride;
output  [6:0] slcg_op_en;

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
wire dp2reg_done_int = (state == ST_RUN) ? dp2reg_done : 1'b0;                      // Is this required?
wire [31:0] dp2reg_sat_count_int = (state == ST_RUN) ? dp2reg_sat_count : 32'b0;    // Is this required?

// top module instantiation
NV_NVDLA_cacc NV_NVDLA_cacc_inst (
    .nvdla_core_clk(nvdla_core_clk),
    .nvdla_core_rstn(nvdla_core_rstn),

    .csb2cacc_req_pvld(csb2cacc_req_pvld_int),
    .csb2cacc_req_prdy(csb2cacc_req_prdy),
    .csb2cacc_req_pd(csb2cacc_req_pd),

    .cacc2csb_resp_valid(cacc2csb_resp_valid),
    .cacc2csb_resp_pd(cacc2csb_resp_pd),
    // New inputs
    .dp2reg_done(dp2reg_done_int),
    .dp2reg_sat_count(dp2reg_sat_count_int),
    // New outputs
    .reg2dp_batches(reg2dp_batches),
    .reg2dp_clip_truncate(reg2dp_clip_truncate),
    .reg2dp_conv_mode(reg2dp_conv_mode),
    .reg2dp_cya(reg2dp_cya),
    .reg2dp_dataout_addr(reg2dp_dataout_addr),
    .reg2dp_dataout_channel(reg2dp_dataout_channel),
    .reg2dp_dataout_height(reg2dp_dataout_height),
    .reg2dp_dataout_width(reg2dp_dataout_width),
    .reg2dp_line_packed(reg2dp_line_packed),
    .reg2dp_line_stride(reg2dp_line_stride),
    .reg2dp_op_en(reg2dp_op_en),
    .reg2dp_proc_precision(reg2dp_proc_precision),
    .reg2dp_surf_packed(reg2dp_surf_packed),
    .reg2dp_surf_stride(reg2dp_surf_stride),
    .slcg_op_en(slcg_op_en),

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