# This is the Jasper script for the self composition check.
# This script would be used by the retention explorer tool, 
# so please only modify it as instructed (marked with "# TODO: ...") if you want to call the explorer.

analyze -sv design/spi/rtl/spi_clgen.v
analyze -sv design/spi/rtl/spi_defines.v
analyze -sv design/spi/rtl/spi_qchannel.v
analyze -sv design/spi/rtl/spi_shift.v
analyze -sv design/spi/rtl/spi_top.v
analyze -sv design/spi/rtl/timescale.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/spi/work/design_test.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/spi/work/wrapper.sv

elaborate -top wrapper

clock wb_clk_i
reset wb_rst_i -non_resettable_regs 0

# TODO: You can configure the changing rate of inputs.

assume -reset { qreqn == 1'b1 }

# TODO: Please add the formal interface constraints either here or in wrapper.sv.
assume -reset { pr_restore == 1'b0 }

# TODO: You can modify the expression part of this assertion.
assert -name output_equiv { @(posedge wb_clk_i) disable iff (wb_rst_i)
    ( (qacceptn == qacceptn_test) &&
    (qdeny == qdeny_test) ) &&
    ( !(qacceptn) ||
    ( (wb_int_o == wb_int_o_test) &&
    (wb_err_o == wb_err_o_test) &&
    (wb_dat_o == wb_dat_o_test) &&
    (mosi_pad_o == mosi_pad_o_test) &&
    (sclk_pad_o == sclk_pad_o_test) &&
    (wb_ack_o == wb_ack_o_test) &&
    (ss_pad_o == ss_pad_o_test) ) )
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

