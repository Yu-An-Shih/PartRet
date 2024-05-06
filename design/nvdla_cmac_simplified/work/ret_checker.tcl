# This is the Jasper script for the self composition check.
# This script would be used by the retention explorer tool, 
# so please only modify it as instructed (marked with "# TODO: ...") if you want to call the explorer.

analyze -sv design/nvdla_cmac_simplified/rtl/NV_NVDLA_cmac.v
analyze -sv design/nvdla_cmac_simplified/rtl/NV_NVDLA_cmac_qchannel.v
analyze -sv design/nvdla_cmac_simplified/rtl/NV_NVDLA_CMAC_reg.v
analyze -sv design/nvdla_cmac_simplified/rtl/NV_NVDLA_CMAC_REG_single.v
analyze -sv design/nvdla_cmac_simplified/rtl/NV_NVDLA_CMAC_REG_dual.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/nvdla_cmac_simplified/work/design_test.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/nvdla_cmac_simplified/work/wrapper.sv

elaborate -top wrapper

clock nvdla_core_clk
reset {~nvdla_core_rstn} -non_resettable_regs 0

# TODO: You can configure the changing rate of inputs.

assume -reset { qreqn == 1'b1 }

# TODO: Please add the formal interface constraints either here or in wrapper.sv.
assume -reset { pr_restore == 1'b0 }

# TODO: You can modify the expression part of this assertion.
assert -name output_equiv { @(posedge nvdla_core_clk)
    ( (qacceptn == qacceptn_test) &&
    (qdeny == qdeny_test) ) &&
    ( !(qacceptn) ||
    ( (cmac_a2csb_resp_valid == cmac_a2csb_resp_valid_test) &&
    (reg2dp_conv_mode_o == reg2dp_conv_mode_o_test) &&
    (csb2cmac_a_req_prdy == csb2cmac_a_req_prdy_test) &&
    (slcg_op_en_o == slcg_op_en_o_test) &&
    (cmac_a2csb_resp_pd == cmac_a2csb_resp_pd_test) &&
    (reg2dp_proc_precision_o == reg2dp_proc_precision_o_test) &&
    (reg2dp_op_en_o == reg2dp_op_en_o_test) ) )
}

# TODO: You can modify the proof settings.
set_engine_mode {B Ht M Mp}

set_prove_time_limit 86400s

prove -property output_equiv

get_property_info output_equiv -list status
get_property_info output_equiv -list time
get_property_info output_equiv -list engine
get_property_info output_equiv -list trace_length
get_property_info output_equiv -list proof_effort
get_property_info output_equiv -list min_length

