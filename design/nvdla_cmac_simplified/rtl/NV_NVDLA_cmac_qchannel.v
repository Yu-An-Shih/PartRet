module NV_NVDLA_cmac_qchannel (
    nvdla_core_clk,
    nvdla_core_rstn,

    csb2cmac_a_req_pvld,
    csb2cmac_a_req_prdy,
    csb2cmac_a_req_pd,

    cmac_a2csb_resp_valid,
    cmac_a2csb_resp_pd,
    // New inputs
    dp2reg_done_i,
    // New outputs
    reg2dp_op_en_o,
    reg2dp_conv_mode_o,
    reg2dp_proc_precision_o,
    slcg_op_en_o,
    // Q-Channel Interface
    qreqn,
    qacceptn,
    qdeny
);

input nvdla_core_clk;
input nvdla_core_rstn;

input csb2cmac_a_req_pvld;
output csb2cmac_a_req_prdy;
input [62:0] csb2cmac_a_req_pd;

output cmac_a2csb_resp_valid;
output [33:0] cmac_a2csb_resp_pd;

// New inputs
input dp2reg_done_i;

// New outputs
output reg2dp_op_en_o;
output reg2dp_conv_mode_o;
output [1:0] reg2dp_proc_precision_o;
output [10:0] slcg_op_en_o;

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

wire ready_to_stop = !reg2dp_op_en_o && !csb2cmac_a_req_pvld;

wire csb2cmac_a_req_pvld_int = (state == ST_RUN) ? csb2cmac_a_req_pvld : 1'b0;
wire dp2reg_done_int = (state == ST_RUN) ? dp2reg_done_i : 1'b0;    // Is this required?

// top module instantiation
NV_NVDLA_cmac NV_NVDLA_cmac_inst (
    .nvdla_core_clk(nvdla_core_clk),
    .nvdla_core_rstn(nvdla_core_rstn),

    .csb2cmac_a_req_pvld(csb2cmac_a_req_pvld_int),
    .csb2cmac_a_req_prdy(csb2cmac_a_req_prdy),
    .csb2cmac_a_req_pd(csb2cmac_a_req_pd),

    .cmac_a2csb_resp_valid(cmac_a2csb_resp_valid),
    .cmac_a2csb_resp_pd(cmac_a2csb_resp_pd),

    // New inputs
    .dp2reg_done_i(dp2reg_done_int),

    // New outputs
    .reg2dp_op_en_o(reg2dp_op_en_o),
    .reg2dp_conv_mode_o(reg2dp_conv_mode_o),
    .reg2dp_proc_precision_o(reg2dp_proc_precision_o),
    .slcg_op_en_o(slcg_op_en_o)
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
            if (counter == 3'b111) begin
                state_next = ST_STOP;
                //counter_next = 3'b0;
            end
        end
        /*ST_PRE2: begin
            state_next = ST_STOP;
        end*/
    endcase
end

always @(posedge nvdla_core_clk) begin
    if (!nvdla_core_rstn) begin
        state <= ST_STOP;
        counter <= 3'b0;
    end
    else begin
        state <= state_next;
        counter <= counter_next;
    end
end

endmodule