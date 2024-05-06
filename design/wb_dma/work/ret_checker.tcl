# This is the Jasper script for the self composition check.
# This script would be used by the retention explorer tool, 
# so please only modify it as instructed (marked with "# TODO: ...") if you want to call the explorer.

analyze -sv design/wb_dma/rtl/wb_dma_wb_mast.v
analyze -sv design/wb_dma/rtl/wb_dma_wb_if.v
analyze -sv design/wb_dma/rtl/wb_dma_pri_enc_sub.v
analyze -sv design/wb_dma/rtl/wb_dma_de.v
analyze -sv design/wb_dma/rtl/wb_dma_ch_sel.v
analyze -sv design/wb_dma/rtl/wb_dma_ch_pri_enc.v
analyze -sv design/wb_dma/rtl/wb_dma_rf.v
analyze -sv design/wb_dma/rtl/wb_dma_wb_slv.v
analyze -sv design/wb_dma/rtl/wb_dma_ch_rf.v
analyze -sv design/wb_dma/rtl/wb_dma_inc30r.v
analyze -sv design/wb_dma/rtl/wb_dma_ch_arb.v
analyze -sv design/wb_dma/rtl/wb_dma_top.v
analyze -sv design/wb_dma/rtl/wb_dma_defines.v
analyze -sv design/wb_dma/rtl/wb_dma_qchannel.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/wb_dma/work/design_test.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/wb_dma/work/wrapper.sv

elaborate -top wrapper

clock clk_i
reset rst_i -non_resettable_regs 0

# TODO: You can configure the changing rate of inputs.

assume -reset { qreqn == 1'b1 }

# TODO: Please add the formal interface constraints either here or in wrapper.sv.
assume -reset { pr_restore == 1'b0 }

# TODO: You can modify the expression part of this assertion.
assert -name output_equiv { @(posedge clk_i) disable iff (rst_i)
    ( (qacceptn == qacceptn_test) &&
    (qdeny == qdeny_test) ) &&
    ( !(qacceptn) ||
    ( (wb1_cyc_o == wb1_cyc_o_test) &&
    (wb0_rty_o == wb0_rty_o_test) &&
    (dma_ack_o == dma_ack_o_test) &&
    (wb1_we_o == wb1_we_o_test) &&
    (wb0_we_o == wb0_we_o_test) &&
    (wb0_cyc_o == wb0_cyc_o_test) &&
    (wb1_err_o == wb1_err_o_test) &&
    (intb_o == intb_o_test) &&
    (wb1_addr_o == wb1_addr_o_test) &&
    (wb0_addr_o == wb0_addr_o_test) &&
    (wb1m_data_o == wb1m_data_o_test) &&
    (wb0_err_o == wb0_err_o_test) &&
    (wb0_sel_o == wb0_sel_o_test) &&
    (inta_o == inta_o_test) &&
    (wb0_stb_o == wb0_stb_o_test) &&
    (wb1_sel_o == wb1_sel_o_test) &&
    (wb1_stb_o == wb1_stb_o_test) &&
    (wb0s_data_o == wb0s_data_o_test) &&
    (wb0m_data_o == wb0m_data_o_test) &&
    (wb1s_data_o == wb1s_data_o_test) &&
    (wb1_rty_o == wb1_rty_o_test) &&
    (wb0_ack_o == wb0_ack_o_test) &&
    (wb1_ack_o == wb1_ack_o_test) ) )
}

# Customized
#assert -name output_equiv { @(posedge clk_i)
#    ( (qacceptn == qacceptn_test) &&
#    (qdeny == qdeny_test) ) &&
#    ( !(qacceptn) ||
#    ( (wb1_cyc_o == wb1_cyc_o_test) &&
#    (wb0_rty_o == wb0_rty_o_test) &&
#    (wb1_we_o == wb1_we_o_test) &&
#    (wb0_we_o == wb0_we_o_test) &&
#    (wb0_cyc_o == wb0_cyc_o_test) &&
#    (wb1_err_o == wb1_err_o_test) &&
#    (wb1_addr_o == wb1_addr_o_test) &&
#    (wb0_addr_o == wb0_addr_o_test) &&
#    (wb1m_data_o == wb1m_data_o_test) &&
#    (wb0_err_o == wb0_err_o_test) &&
#    (wb0_sel_o == wb0_sel_o_test) &&
#    (wb0_stb_o == wb0_stb_o_test) &&
#    (wb1_sel_o == wb1_sel_o_test) &&
#    (wb1_stb_o == wb1_stb_o_test) &&
#    (wb0s_data_o == wb0s_data_o_test) &&
#    (wb0m_data_o == wb0m_data_o_test) &&
#    (wb1s_data_o == wb1s_data_o_test) &&
#    (wb1_rty_o == wb1_rty_o_test) &&
#    (wb0_ack_o == wb0_ack_o_test) &&
#    (wb1_ack_o == wb1_ack_o_test) ) )
#}

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

