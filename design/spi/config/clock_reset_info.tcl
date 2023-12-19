# Clock and reset commands for the Jasper tool

clock wb_clk_i
reset -expression {wb_rst_i} -non_resettable_regs 0
#reset -formal {wb_rst_i} -bound 10
#reset -non_resettable_regs 0

# Interface constraints during reset - required for getting reset values
assume -reset { !wb_stb_i && !wb_cyc_i } -name Assume_WISHBONE_Rule_3_20
