# This is the Jasper script for the self composition check.
# This script would be used by the retention explorer tool, 
# so please only modify it as instructed (marked with "# TODO: ...") if you want to call the explorer.

analyze -sv design/mem_ctrl/rtl/mc_adr_sel.v
analyze -sv design/mem_ctrl/rtl/mc_cs_rf.v
analyze -sv design/mem_ctrl/rtl/mc_defines.v
analyze -sv design/mem_ctrl/rtl/mc_dp.v
analyze -sv design/mem_ctrl/rtl/mc_incn_r.v
analyze -sv design/mem_ctrl/rtl/mc_mem_if.v
analyze -sv design/mem_ctrl/rtl/mc_obct_top.v
analyze -sv design/mem_ctrl/rtl/mc_obct.v
analyze -sv design/mem_ctrl/rtl/mc_rd_fifo.v
analyze -sv design/mem_ctrl/rtl/mc_refresh.v
analyze -sv design/mem_ctrl/rtl/mc_rf.v
analyze -sv design/mem_ctrl/rtl/mc_timing.v
analyze -sv design/mem_ctrl/rtl/mc_top.v
analyze -sv design/mem_ctrl/rtl/mc_wb_if.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/mem_ctrl/work/design_test.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/mem_ctrl/work/wrapper.sv

elaborate -top wrapper

clock clk_i
clock mc_clk_i -factor 2
reset rst_i -non_resettable_regs 0

# TODO: You can configure the changing rate of inputs.
clock -rate {mc_br_pad_i mc_ack_pad_i mc_data_pad_i mc_dp_pad_i mc_sts_pad_i} mc_clk_i

assume -reset { wb_stb_i == 1'b0 }
assume -reset { wb_cyc_i == 1'b0 }
assume -reset { resume_req_i == 1'b0 }
assume -reset { mc_data_pad_i == {28'b0, 2'b11, 2'b10} }
assume -reset { mc_ack_pad_i == 1'b0 }
assume -reset { wb_we_i == 1'b0 }
assume -reset { wb_sel_i == 4'b0 }
assume -reset { wb_addr_i == 32'b0 }
assume -reset { wb_data_i == 32'b0 }
assume -reset { susp_req_i == 1'b0 }
assume -reset { mc_br_pad_i == 1'b0 }
assume -reset { mc_dp_pad_i == 4'b0 }
assume -reset { mc_sts_pad_i == 1'b0 }

# TODO: Please add the formal interface constraints either here or in wrapper.sv.
assume -reset { pr_restore == 1'b0 }

# TODO: You can modify the expression part of this assertion.
#assert -name output_equiv { @(posedge clk_i) disable iff (rst_i)
#    ( (suspended_o == suspended_o_test) ) &&
#    ( !(!suspended_o) ||
#    ( (mc_cas_pad_o_ == mc_cas_pad_o__test) &&
#    (mc_dqm_pad_o == mc_dqm_pad_o_test) &&
#    (mc_adsc_pad_o_ == mc_adsc_pad_o__test) &&
#    (mc_vpen_pad_o == mc_vpen_pad_o_test) &&
#    (mc_rp_pad_o_ == mc_rp_pad_o__test) &&
#    (mc_data_pad_o == mc_data_pad_o_test) &&
#    (wb_data_o == wb_data_o_test) &&
#    (wb_err_o == wb_err_o_test) &&
#    (mc_cke_pad_o_ == mc_cke_pad_o__test) &&
#    (mc_we_pad_o_ == mc_we_pad_o__test) &&
#    (poc_o == poc_o_test) &&
#    (mc_adv_pad_o_ == mc_adv_pad_o__test) &&
#    (mc_addr_pad_o == mc_addr_pad_o_test) &&
#    (mc_oe_pad_o_ == mc_oe_pad_o__test) &&
#    (mc_bg_pad_o == mc_bg_pad_o_test) &&
#    (wb_ack_o == wb_ack_o_test) &&
#    (mc_dp_pad_o == mc_dp_pad_o_test) &&
#    (mc_cs_pad_o_ == mc_cs_pad_o__test) &&
#    (mc_ras_pad_o_ == mc_ras_pad_o__test) &&
#    (mc_zz_pad_o == mc_zz_pad_o_test) &&
#    (mc_doe_pad_doe_o == mc_doe_pad_doe_o_test) &&
#    (mc_coe_pad_coe_o == mc_coe_pad_coe_o_test) ) )
#}

# Customize
#assert -name output_equiv { @(posedge clk_i)
#    (suspended_o == suspended_o_test) &&
#    (!wb_stb_i || (
#        (wb_ack_o == wb_ack_o_test) &&
#        (wb_err_o == wb_err_o_test) &&
#        (!wb_ack_o || (wb_data_o == wb_data_o_test)) )) &&
#    (mc_doe_pad_doe_o == mc_doe_pad_doe_o_test) &&
#    (mc_coe_pad_coe_o == mc_coe_pad_coe_o_test) &&
#    (!mc_coe_pad_coe_o || (
#        (mc_cs_pad_o_ == mc_cs_pad_o__test) &&
#        (mc_oe_pad_o_ == mc_oe_pad_o__test) &&
#        (mc_we_pad_o_ == mc_we_pad_o__test) &&
#        (!(~mc_cs_pad_o_[0]) || (
#            (mc_addr_pad_o == mc_addr_pad_o_test) &&
#            (mc_data_pad_o == mc_data_pad_o_test) ) ) ) )
#}

assert -name output_equiv { @(posedge clk_i)
    (suspended_o == suspended_o_test) &&
    ( !(!suspended_o) ||
        (wb_ack_o == wb_ack_o_test) &&
        (wb_err_o == wb_err_o_test) &&
        (wb_data_o == wb_data_o_test) &&
        (mc_doe_pad_doe_o == mc_doe_pad_doe_o_test) &&
        (mc_coe_pad_coe_o == mc_coe_pad_coe_o_test) &&
        (mc_cs_pad_o_ == mc_cs_pad_o__test) &&
        (mc_oe_pad_o_ == mc_oe_pad_o__test) &&
        (mc_we_pad_o_ == mc_we_pad_o__test) &&
        (mc_addr_pad_o == mc_addr_pad_o_test) &&
        (mc_data_pad_o == mc_data_pad_o_test) )
}

# TODO: You can modify the proof settings.
set_engine_mode {B Ht Mp}

set_prove_time_limit 86400s

prove -property output_equiv

get_property_info output_equiv -list status
get_property_info output_equiv -list time
get_property_info output_equiv -list engine
get_property_info output_equiv -list trace_length
get_property_info output_equiv -list proof_effort
get_property_info output_equiv -list min_length
