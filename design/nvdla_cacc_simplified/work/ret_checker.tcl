# This is the Jasper script for the self composition check.
# This script would be used by the retention explorer tool, 
# so please only modify it as instructed (marked with "# TODO: ...") if you want to call the explorer.

analyze -sv design/nvdla_cacc_simplified/rtl/NV_NVDLA_cacc.v
analyze -sv design/nvdla_cacc_simplified/rtl/NV_NVDLA_cacc_qchannel.v
analyze -sv design/nvdla_cacc_simplified/rtl/NV_NVDLA_CACC_single_reg.v
analyze -sv design/nvdla_cacc_simplified/rtl/NV_NVDLA_CACC_dual_reg.v
analyze -sv design/nvdla_cacc_simplified/rtl/NV_NVDLA_CACC_regfile.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/nvdla_cacc_simplified/work/design_test.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/nvdla_cacc_simplified/work/wrapper.sv

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
    ( (reg2dp_surf_packed == reg2dp_surf_packed_test) &&
    (reg2dp_op_en == reg2dp_op_en_test) &&
    (cacc2csb_resp_valid == cacc2csb_resp_valid_test) &&
    (reg2dp_dataout_width == reg2dp_dataout_width_test) &&
    (reg2dp_proc_precision == reg2dp_proc_precision_test) &&
    (reg2dp_conv_mode == reg2dp_conv_mode_test) &&
    (reg2dp_dataout_channel == reg2dp_dataout_channel_test) &&
    (reg2dp_batches == reg2dp_batches_test) &&
    (reg2dp_clip_truncate == reg2dp_clip_truncate_test) &&
    (reg2dp_cya == reg2dp_cya_test) &&
    (reg2dp_surf_stride == reg2dp_surf_stride_test) &&
    (cacc2csb_resp_pd == cacc2csb_resp_pd_test) &&
    (reg2dp_dataout_height == reg2dp_dataout_height_test) &&
    (reg2dp_line_stride == reg2dp_line_stride_test) &&
    (reg2dp_line_packed == reg2dp_line_packed_test) &&
    (slcg_op_en == slcg_op_en_test) &&
    (csb2cacc_req_prdy == csb2cacc_req_prdy_test) &&
    (reg2dp_dataout_addr == reg2dp_dataout_addr_test) ) )
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

