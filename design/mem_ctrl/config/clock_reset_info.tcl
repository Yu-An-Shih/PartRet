# Clock and reset commands for the Jasper tool

clock clk_i
clock mc_clk_i -factor 2
reset -expression {rst_i} -non_resettable_regs 0
#reset -formal {rst_i} -bound 10
#reset -non_resettable_regs 0

clock -rate {mc_br_pad_i mc_ack_pad_i mc_data_pad_i mc_dp_pad_i mc_sts_pad_i} mc_clk_i

# Interface constraints during reset - required for getting reset values
assume -reset { !wb_stb_i && !wb_cyc_i } -name Assume_WISHBONE_Rule_3_20
assume -reset { !susp_req_i && !resume_req_i }
assume -reset { mc_data_pad_i == {28'hzzz_zzzz, 2'b11, 2'b10} }
assume -reset { !mc_ack_pad_i }
