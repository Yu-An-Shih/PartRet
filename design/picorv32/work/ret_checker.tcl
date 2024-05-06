# This is the Jasper script for the self composition check.
# This script would be used by the retention explorer tool, 
# so please only modify it as instructed (marked with "# TODO: ...") if you want to call the explorer.

analyze -sv design/picorv32/rtl/picorv32.v
analyze -sv design/picorv32/rtl/picorv32_qchannel.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/picorv32/work/design_test.v
analyze -sv /home/ys3146/Workspace/partial_retention/PartRet/design/picorv32/work/wrapper.sv

elaborate -top wrapper

clock clk
reset {~resetn} -non_resettable_regs 0

# TODO: You can configure the changing rate of inputs.

assume -reset { qreqn == 1'b1 }

# TODO: Please add the formal interface constraints either here or in wrapper.sv.
assume -reset { pr_restore == 1'b0 }

# TODO: You can modify the expression part of this assertion.
assert -name output_equiv { @(posedge clk)
    ( (qacceptn == qacceptn_test) &&
    (qdeny == qdeny_test) ) &&
    ( !(qacceptn) ||
    ( (mem_la_wdata == mem_la_wdata_test) &&
    (pcpi_rs2 == pcpi_rs2_test) &&
    (pcpi_valid == pcpi_valid_test) &&
    (pcpi_rs1 == pcpi_rs1_test) &&
    (eoi == eoi_test) &&
    (trap == trap_test) &&
    (mem_addr == mem_addr_test) &&
    (mem_la_wstrb == mem_la_wstrb_test) &&
    (mem_wdata == mem_wdata_test) &&
    (mem_instr == mem_instr_test) &&
    (mem_la_read == mem_la_read_test) &&
    (trace_data == trace_data_test) &&
    (mem_la_write == mem_la_write_test) &&
    (trace_valid == trace_valid_test) &&
    (mem_wstrb == mem_wstrb_test) &&
    (mem_valid == mem_valid_test) &&
    (mem_la_addr == mem_la_addr_test) &&
    (pcpi_insn == pcpi_insn_test) ) )
}

# Customized
#assert -name output_equiv { @(posedge clk)
#    ( (qacceptn == qacceptn_test) &&
#    (qdeny == qdeny_test) ) &&
#    ( !(qacceptn) ||
#    ( (mem_valid == mem_valid_test) &&
#    (mem_instr == mem_instr_test) &&
#    (mem_addr == mem_addr_test) &&
#    (mem_wdata == mem_wdata_test) &&
#    (mem_wstrb == mem_wstrb_test) &&
#    (mem_la_read == mem_la_read_test) &&
#    (mem_la_write == mem_la_write_test) &&
#    (mem_la_addr == mem_la_addr_test) &&
#    (mem_la_wdata == mem_la_wdata_test) &&
#    (mem_la_wstrb == mem_la_wstrb_test) ) )
#}

#assert -name output_equiv { @(posedge clk)
#    ( (qacceptn == qacceptn_test) &&
#    (qdeny == qdeny_test) ) &&
#    ( !(qacceptn) ||
#    ( (mem_valid == mem_valid_test) &&
#    (mem_instr == mem_instr_test) &&
#    (!mem_valid || (
#    (mem_addr == mem_addr_test) &&
#    (mem_wdata == mem_wdata_test) &&
#    (mem_wstrb == mem_wstrb_test) ) ) ) )
#}

# Naive
#assert -name output_equiv { @(posedge clk)
#    ( (qacceptn == qacceptn_test) &&
#    (qdeny == qdeny_test) &&
#    (mem_la_wdata == mem_la_wdata_test) &&
#    (pcpi_rs2 == pcpi_rs2_test) &&
#    (pcpi_valid == pcpi_valid_test) &&
#    (pcpi_rs1 == pcpi_rs1_test) &&
#    (eoi == eoi_test) &&
#    (trap == trap_test) &&
#    (mem_addr == mem_addr_test) &&
#    (mem_la_wstrb == mem_la_wstrb_test) &&
#    (mem_wdata == mem_wdata_test) &&
#    (mem_instr == mem_instr_test) &&
#    (mem_la_read == mem_la_read_test) &&
#    (trace_data == trace_data_test) &&
#    (mem_la_write == mem_la_write_test) &&
#    (trace_valid == trace_valid_test) &&
#    (mem_wstrb == mem_wstrb_test) &&
#    (mem_valid == mem_valid_test) &&
#    (mem_la_addr == mem_la_addr_test) &&
#    (pcpi_insn == pcpi_insn_test) )
#}

# TODO: You can modify the proof settings.
set_engine_mode {B Ht Mp}

set_prove_time_limit 1800s

prove -property output_equiv

get_property_info output_equiv -list status
get_property_info output_equiv -list time
get_property_info output_equiv -list engine
get_property_info output_equiv -list trace_length
get_property_info output_equiv -list proof_effort
get_property_info output_equiv -list min_length

