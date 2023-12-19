property Rule_3_25;
    @(posedge wb_clk_i) wb_stb_i |-> wb_cyc_i;
endproperty

WISHBONE_Rule_3_25: assume property ( Rule_3_25 );

property Handshake_1;
    @(posedge wb_clk_i) $fell(wb_stb_i) |-> $past(wb_ack_o || wb_err_o);
endproperty

property Handshake_2;
    @(posedge wb_clk_i) $rose(wb_ack_o || wb_err_o) |=> $fell(wb_stb_i);
endproperty

WISHBONE_Handshake_1: assume property ( Handshake_1 );
WISHBONE_Handshake_2: assume property ( Handshake_2 );

property Rule_3_45;
    @(posedge wb_clk_i) !(wb_ack_o && wb_err_o);
endproperty

WISHBONE_Rule_3_45: assert property ( Rule_3_45 );

property Rule_3_50;
    @(posedge wb_clk_i) $rose(wb_stb_i) |-> ##[0:$] ($rose(wb_ack_o) || $rose(wb_err_o));
endproperty

property Rule_3_50_2;
    @(posedge wb_clk_i) $fell(wb_stb_i) |-> ##[0:$] ($fell(wb_ack_o) || $fell(wb_err_o));
endproperty

WISHBONE_Rule_3_50: assert property ( Rule_3_50 );
WISHBONE_Rule_3_50_2: assert property ( Rule_3_50_2 );

property Rule_3_60;
    @(posedge wb_clk_i) ($past(wb_stb_i) && wb_stb_i) |-> ($stable(wb_adr_i) && $stable(wb_dat_i) && $stable(wb_sel_i) && $stable(wb_we_i));
endproperty

WISHBONE_Rule_3_60: assume property ( Rule_3_60 );

property Implicit_1;
    @(posedge wb_clk_i) (wb_ack_o || wb_err_o) |-> wb_stb_i;
endproperty

WISHBONE_Implicit_1: assert property ( Implicit_1 );



property Handshake_rule_1;
    @(posedge wb_clk_i) $fell(qreqn) |-> $past(qacceptn && !qdeny);
endproperty

property Handshake_rule_2;
    @(posedge wb_clk_i) $rose(qreqn) |-> $past(qacceptn == qdeny);
endproperty

QChannel_Handshake_rule_1: assume property ( Handshake_rule_1 );
QChannel_Handshake_rule_2: assume property ( Handshake_rule_2 );

property Handshake_rule_3;
    @(posedge wb_clk_i) $fell(qacceptn) |-> $past(!qreqn && !qdeny);
endproperty

property Handshake_rule_4;
    @(posedge wb_clk_i) $rose(qacceptn) |-> $past(qreqn && !qdeny);
endproperty

property Handshake_rule_5;
    @(posedge wb_clk_i) $fell(qdeny) |-> $past(qreqn && qacceptn);
endproperty

property Handshake_rule_6;
    @(posedge wb_clk_i) $rose(qdeny) |-> $past(!qreqn && qacceptn);
endproperty

QChannel_Handshake_rule_3: assert property ( Handshake_rule_3 );
QChannel_Handshake_rule_4: assert property ( Handshake_rule_4 );
QChannel_Handshake_rule_5: assert property ( Handshake_rule_5 );
QChannel_Handshake_rule_6: assert property ( Handshake_rule_6 );