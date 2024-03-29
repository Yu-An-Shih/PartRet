// ================================================================
// NVDLA Open Source Project
// 
// Copyright(c) 2016 - 2017 NVIDIA Corporation.  Licensed under the
// NVDLA Open Hardware License; Check "LICENSE" which comes with 
// this distribution for more information.
// ================================================================

// File Name: NV_NVDLA_cmac.v

module NV_NVDLA_cmac (
   csb2cmac_a_req_pd             //|< i
  ,csb2cmac_a_req_pvld           //|< i
  
  ,nvdla_core_clk                //|< i
  ,nvdla_core_rstn               //|< i
  
  ,cmac_a2csb_resp_pd            //|> o
  ,cmac_a2csb_resp_valid         //|> o
  ,csb2cmac_a_req_prdy           //|> o

  // New inputs
  ,dp2reg_done_i

  // New outputs
  ,reg2dp_op_en_o
  ,reg2dp_conv_mode_o
  ,reg2dp_proc_precision_o
  ,slcg_op_en_o
  );
//
// NV_NVDLA_cmac_ports.v
//
input  nvdla_core_clk;
input  nvdla_core_rstn;

output        cmac_a2csb_resp_valid;  /* data valid */
output [33:0] cmac_a2csb_resp_pd;     /* pkt_id_width=1 pkt_widths=33,33  */

input         csb2cmac_a_req_pvld;  /* data valid */
output        csb2cmac_a_req_prdy;  /* data return handshake */
input  [62:0] csb2cmac_a_req_pd;

wire        dp2reg_done;
wire  [0:0] reg2dp_conv_mode;
wire  [0:0] reg2dp_op_en;
wire  [1:0] reg2dp_proc_precision;
wire [10:0] slcg_op_en;

// New inputs
input dp2reg_done_i;

assign dp2reg_done = dp2reg_done_i;

// New outputs
output reg2dp_op_en_o;
output reg2dp_conv_mode_o;
output [1:0] reg2dp_proc_precision_o;
output [10:0] slcg_op_en_o;

assign reg2dp_op_en_o = reg2dp_op_en[0];
assign reg2dp_conv_mode_o = reg2dp_conv_mode[0];
assign reg2dp_proc_precision_o = reg2dp_proc_precision[1:0];
assign slcg_op_en_o = slcg_op_en[10:0];

//==========================================================
// core
//==========================================================
/*NV_NVDLA_CMAC_core u_core (
   .nvdla_core_clk                (nvdla_core_clk)                //|< i
  ,.nvdla_core_rstn               (nvdla_core_rstn)               //|< i
  ,.sc2mac_dat_pvld               (sc2mac_dat_pvld)               //|< i
  ,.sc2mac_dat_mask               (sc2mac_dat_mask[127:0])        //|< i
  ,.sc2mac_dat_data0              (sc2mac_dat_data0[7:0])         //|< i
  ,.sc2mac_dat_data1              (sc2mac_dat_data1[7:0])         //|< i
  ,.sc2mac_dat_data2              (sc2mac_dat_data2[7:0])         //|< i
  ,.sc2mac_dat_data3              (sc2mac_dat_data3[7:0])         //|< i
  ,.sc2mac_dat_data4              (sc2mac_dat_data4[7:0])         //|< i
  ,.sc2mac_dat_data5              (sc2mac_dat_data5[7:0])         //|< i
  ,.sc2mac_dat_data6              (sc2mac_dat_data6[7:0])         //|< i
  ,.sc2mac_dat_data7              (sc2mac_dat_data7[7:0])         //|< i
  ,.sc2mac_dat_data8              (sc2mac_dat_data8[7:0])         //|< i
  ,.sc2mac_dat_data9              (sc2mac_dat_data9[7:0])         //|< i
  ,.sc2mac_dat_data10             (sc2mac_dat_data10[7:0])        //|< i
  ,.sc2mac_dat_data11             (sc2mac_dat_data11[7:0])        //|< i
  ,.sc2mac_dat_data12             (sc2mac_dat_data12[7:0])        //|< i
  ,.sc2mac_dat_data13             (sc2mac_dat_data13[7:0])        //|< i
  ,.sc2mac_dat_data14             (sc2mac_dat_data14[7:0])        //|< i
  ,.sc2mac_dat_data15             (sc2mac_dat_data15[7:0])        //|< i
  ,.sc2mac_dat_data16             (sc2mac_dat_data16[7:0])        //|< i
  ,.sc2mac_dat_data17             (sc2mac_dat_data17[7:0])        //|< i
  ,.sc2mac_dat_data18             (sc2mac_dat_data18[7:0])        //|< i
  ,.sc2mac_dat_data19             (sc2mac_dat_data19[7:0])        //|< i
  ,.sc2mac_dat_data20             (sc2mac_dat_data20[7:0])        //|< i
  ,.sc2mac_dat_data21             (sc2mac_dat_data21[7:0])        //|< i
  ,.sc2mac_dat_data22             (sc2mac_dat_data22[7:0])        //|< i
  ,.sc2mac_dat_data23             (sc2mac_dat_data23[7:0])        //|< i
  ,.sc2mac_dat_data24             (sc2mac_dat_data24[7:0])        //|< i
  ,.sc2mac_dat_data25             (sc2mac_dat_data25[7:0])        //|< i
  ,.sc2mac_dat_data26             (sc2mac_dat_data26[7:0])        //|< i
  ,.sc2mac_dat_data27             (sc2mac_dat_data27[7:0])        //|< i
  ,.sc2mac_dat_data28             (sc2mac_dat_data28[7:0])        //|< i
  ,.sc2mac_dat_data29             (sc2mac_dat_data29[7:0])        //|< i
  ,.sc2mac_dat_data30             (sc2mac_dat_data30[7:0])        //|< i
  ,.sc2mac_dat_data31             (sc2mac_dat_data31[7:0])        //|< i
  ,.sc2mac_dat_data32             (sc2mac_dat_data32[7:0])        //|< i
  ,.sc2mac_dat_data33             (sc2mac_dat_data33[7:0])        //|< i
  ,.sc2mac_dat_data34             (sc2mac_dat_data34[7:0])        //|< i
  ,.sc2mac_dat_data35             (sc2mac_dat_data35[7:0])        //|< i
  ,.sc2mac_dat_data36             (sc2mac_dat_data36[7:0])        //|< i
  ,.sc2mac_dat_data37             (sc2mac_dat_data37[7:0])        //|< i
  ,.sc2mac_dat_data38             (sc2mac_dat_data38[7:0])        //|< i
  ,.sc2mac_dat_data39             (sc2mac_dat_data39[7:0])        //|< i
  ,.sc2mac_dat_data40             (sc2mac_dat_data40[7:0])        //|< i
  ,.sc2mac_dat_data41             (sc2mac_dat_data41[7:0])        //|< i
  ,.sc2mac_dat_data42             (sc2mac_dat_data42[7:0])        //|< i
  ,.sc2mac_dat_data43             (sc2mac_dat_data43[7:0])        //|< i
  ,.sc2mac_dat_data44             (sc2mac_dat_data44[7:0])        //|< i
  ,.sc2mac_dat_data45             (sc2mac_dat_data45[7:0])        //|< i
  ,.sc2mac_dat_data46             (sc2mac_dat_data46[7:0])        //|< i
  ,.sc2mac_dat_data47             (sc2mac_dat_data47[7:0])        //|< i
  ,.sc2mac_dat_data48             (sc2mac_dat_data48[7:0])        //|< i
  ,.sc2mac_dat_data49             (sc2mac_dat_data49[7:0])        //|< i
  ,.sc2mac_dat_data50             (sc2mac_dat_data50[7:0])        //|< i
  ,.sc2mac_dat_data51             (sc2mac_dat_data51[7:0])        //|< i
  ,.sc2mac_dat_data52             (sc2mac_dat_data52[7:0])        //|< i
  ,.sc2mac_dat_data53             (sc2mac_dat_data53[7:0])        //|< i
  ,.sc2mac_dat_data54             (sc2mac_dat_data54[7:0])        //|< i
  ,.sc2mac_dat_data55             (sc2mac_dat_data55[7:0])        //|< i
  ,.sc2mac_dat_data56             (sc2mac_dat_data56[7:0])        //|< i
  ,.sc2mac_dat_data57             (sc2mac_dat_data57[7:0])        //|< i
  ,.sc2mac_dat_data58             (sc2mac_dat_data58[7:0])        //|< i
  ,.sc2mac_dat_data59             (sc2mac_dat_data59[7:0])        //|< i
  ,.sc2mac_dat_data60             (sc2mac_dat_data60[7:0])        //|< i
  ,.sc2mac_dat_data61             (sc2mac_dat_data61[7:0])        //|< i
  ,.sc2mac_dat_data62             (sc2mac_dat_data62[7:0])        //|< i
  ,.sc2mac_dat_data63             (sc2mac_dat_data63[7:0])        //|< i
  ,.sc2mac_dat_data64             (sc2mac_dat_data64[7:0])        //|< i
  ,.sc2mac_dat_data65             (sc2mac_dat_data65[7:0])        //|< i
  ,.sc2mac_dat_data66             (sc2mac_dat_data66[7:0])        //|< i
  ,.sc2mac_dat_data67             (sc2mac_dat_data67[7:0])        //|< i
  ,.sc2mac_dat_data68             (sc2mac_dat_data68[7:0])        //|< i
  ,.sc2mac_dat_data69             (sc2mac_dat_data69[7:0])        //|< i
  ,.sc2mac_dat_data70             (sc2mac_dat_data70[7:0])        //|< i
  ,.sc2mac_dat_data71             (sc2mac_dat_data71[7:0])        //|< i
  ,.sc2mac_dat_data72             (sc2mac_dat_data72[7:0])        //|< i
  ,.sc2mac_dat_data73             (sc2mac_dat_data73[7:0])        //|< i
  ,.sc2mac_dat_data74             (sc2mac_dat_data74[7:0])        //|< i
  ,.sc2mac_dat_data75             (sc2mac_dat_data75[7:0])        //|< i
  ,.sc2mac_dat_data76             (sc2mac_dat_data76[7:0])        //|< i
  ,.sc2mac_dat_data77             (sc2mac_dat_data77[7:0])        //|< i
  ,.sc2mac_dat_data78             (sc2mac_dat_data78[7:0])        //|< i
  ,.sc2mac_dat_data79             (sc2mac_dat_data79[7:0])        //|< i
  ,.sc2mac_dat_data80             (sc2mac_dat_data80[7:0])        //|< i
  ,.sc2mac_dat_data81             (sc2mac_dat_data81[7:0])        //|< i
  ,.sc2mac_dat_data82             (sc2mac_dat_data82[7:0])        //|< i
  ,.sc2mac_dat_data83             (sc2mac_dat_data83[7:0])        //|< i
  ,.sc2mac_dat_data84             (sc2mac_dat_data84[7:0])        //|< i
  ,.sc2mac_dat_data85             (sc2mac_dat_data85[7:0])        //|< i
  ,.sc2mac_dat_data86             (sc2mac_dat_data86[7:0])        //|< i
  ,.sc2mac_dat_data87             (sc2mac_dat_data87[7:0])        //|< i
  ,.sc2mac_dat_data88             (sc2mac_dat_data88[7:0])        //|< i
  ,.sc2mac_dat_data89             (sc2mac_dat_data89[7:0])        //|< i
  ,.sc2mac_dat_data90             (sc2mac_dat_data90[7:0])        //|< i
  ,.sc2mac_dat_data91             (sc2mac_dat_data91[7:0])        //|< i
  ,.sc2mac_dat_data92             (sc2mac_dat_data92[7:0])        //|< i
  ,.sc2mac_dat_data93             (sc2mac_dat_data93[7:0])        //|< i
  ,.sc2mac_dat_data94             (sc2mac_dat_data94[7:0])        //|< i
  ,.sc2mac_dat_data95             (sc2mac_dat_data95[7:0])        //|< i
  ,.sc2mac_dat_data96             (sc2mac_dat_data96[7:0])        //|< i
  ,.sc2mac_dat_data97             (sc2mac_dat_data97[7:0])        //|< i
  ,.sc2mac_dat_data98             (sc2mac_dat_data98[7:0])        //|< i
  ,.sc2mac_dat_data99             (sc2mac_dat_data99[7:0])        //|< i
  ,.sc2mac_dat_data100            (sc2mac_dat_data100[7:0])       //|< i
  ,.sc2mac_dat_data101            (sc2mac_dat_data101[7:0])       //|< i
  ,.sc2mac_dat_data102            (sc2mac_dat_data102[7:0])       //|< i
  ,.sc2mac_dat_data103            (sc2mac_dat_data103[7:0])       //|< i
  ,.sc2mac_dat_data104            (sc2mac_dat_data104[7:0])       //|< i
  ,.sc2mac_dat_data105            (sc2mac_dat_data105[7:0])       //|< i
  ,.sc2mac_dat_data106            (sc2mac_dat_data106[7:0])       //|< i
  ,.sc2mac_dat_data107            (sc2mac_dat_data107[7:0])       //|< i
  ,.sc2mac_dat_data108            (sc2mac_dat_data108[7:0])       //|< i
  ,.sc2mac_dat_data109            (sc2mac_dat_data109[7:0])       //|< i
  ,.sc2mac_dat_data110            (sc2mac_dat_data110[7:0])       //|< i
  ,.sc2mac_dat_data111            (sc2mac_dat_data111[7:0])       //|< i
  ,.sc2mac_dat_data112            (sc2mac_dat_data112[7:0])       //|< i
  ,.sc2mac_dat_data113            (sc2mac_dat_data113[7:0])       //|< i
  ,.sc2mac_dat_data114            (sc2mac_dat_data114[7:0])       //|< i
  ,.sc2mac_dat_data115            (sc2mac_dat_data115[7:0])       //|< i
  ,.sc2mac_dat_data116            (sc2mac_dat_data116[7:0])       //|< i
  ,.sc2mac_dat_data117            (sc2mac_dat_data117[7:0])       //|< i
  ,.sc2mac_dat_data118            (sc2mac_dat_data118[7:0])       //|< i
  ,.sc2mac_dat_data119            (sc2mac_dat_data119[7:0])       //|< i
  ,.sc2mac_dat_data120            (sc2mac_dat_data120[7:0])       //|< i
  ,.sc2mac_dat_data121            (sc2mac_dat_data121[7:0])       //|< i
  ,.sc2mac_dat_data122            (sc2mac_dat_data122[7:0])       //|< i
  ,.sc2mac_dat_data123            (sc2mac_dat_data123[7:0])       //|< i
  ,.sc2mac_dat_data124            (sc2mac_dat_data124[7:0])       //|< i
  ,.sc2mac_dat_data125            (sc2mac_dat_data125[7:0])       //|< i
  ,.sc2mac_dat_data126            (sc2mac_dat_data126[7:0])       //|< i
  ,.sc2mac_dat_data127            (sc2mac_dat_data127[7:0])       //|< i
  ,.sc2mac_dat_pd                 (sc2mac_dat_pd[8:0])            //|< i
  ,.sc2mac_wt_pvld                (sc2mac_wt_pvld)                //|< i
  ,.sc2mac_wt_mask                (sc2mac_wt_mask[127:0])         //|< i
  ,.sc2mac_wt_data0               (sc2mac_wt_data0[7:0])          //|< i
  ,.sc2mac_wt_data1               (sc2mac_wt_data1[7:0])          //|< i
  ,.sc2mac_wt_data2               (sc2mac_wt_data2[7:0])          //|< i
  ,.sc2mac_wt_data3               (sc2mac_wt_data3[7:0])          //|< i
  ,.sc2mac_wt_data4               (sc2mac_wt_data4[7:0])          //|< i
  ,.sc2mac_wt_data5               (sc2mac_wt_data5[7:0])          //|< i
  ,.sc2mac_wt_data6               (sc2mac_wt_data6[7:0])          //|< i
  ,.sc2mac_wt_data7               (sc2mac_wt_data7[7:0])          //|< i
  ,.sc2mac_wt_data8               (sc2mac_wt_data8[7:0])          //|< i
  ,.sc2mac_wt_data9               (sc2mac_wt_data9[7:0])          //|< i
  ,.sc2mac_wt_data10              (sc2mac_wt_data10[7:0])         //|< i
  ,.sc2mac_wt_data11              (sc2mac_wt_data11[7:0])         //|< i
  ,.sc2mac_wt_data12              (sc2mac_wt_data12[7:0])         //|< i
  ,.sc2mac_wt_data13              (sc2mac_wt_data13[7:0])         //|< i
  ,.sc2mac_wt_data14              (sc2mac_wt_data14[7:0])         //|< i
  ,.sc2mac_wt_data15              (sc2mac_wt_data15[7:0])         //|< i
  ,.sc2mac_wt_data16              (sc2mac_wt_data16[7:0])         //|< i
  ,.sc2mac_wt_data17              (sc2mac_wt_data17[7:0])         //|< i
  ,.sc2mac_wt_data18              (sc2mac_wt_data18[7:0])         //|< i
  ,.sc2mac_wt_data19              (sc2mac_wt_data19[7:0])         //|< i
  ,.sc2mac_wt_data20              (sc2mac_wt_data20[7:0])         //|< i
  ,.sc2mac_wt_data21              (sc2mac_wt_data21[7:0])         //|< i
  ,.sc2mac_wt_data22              (sc2mac_wt_data22[7:0])         //|< i
  ,.sc2mac_wt_data23              (sc2mac_wt_data23[7:0])         //|< i
  ,.sc2mac_wt_data24              (sc2mac_wt_data24[7:0])         //|< i
  ,.sc2mac_wt_data25              (sc2mac_wt_data25[7:0])         //|< i
  ,.sc2mac_wt_data26              (sc2mac_wt_data26[7:0])         //|< i
  ,.sc2mac_wt_data27              (sc2mac_wt_data27[7:0])         //|< i
  ,.sc2mac_wt_data28              (sc2mac_wt_data28[7:0])         //|< i
  ,.sc2mac_wt_data29              (sc2mac_wt_data29[7:0])         //|< i
  ,.sc2mac_wt_data30              (sc2mac_wt_data30[7:0])         //|< i
  ,.sc2mac_wt_data31              (sc2mac_wt_data31[7:0])         //|< i
  ,.sc2mac_wt_data32              (sc2mac_wt_data32[7:0])         //|< i
  ,.sc2mac_wt_data33              (sc2mac_wt_data33[7:0])         //|< i
  ,.sc2mac_wt_data34              (sc2mac_wt_data34[7:0])         //|< i
  ,.sc2mac_wt_data35              (sc2mac_wt_data35[7:0])         //|< i
  ,.sc2mac_wt_data36              (sc2mac_wt_data36[7:0])         //|< i
  ,.sc2mac_wt_data37              (sc2mac_wt_data37[7:0])         //|< i
  ,.sc2mac_wt_data38              (sc2mac_wt_data38[7:0])         //|< i
  ,.sc2mac_wt_data39              (sc2mac_wt_data39[7:0])         //|< i
  ,.sc2mac_wt_data40              (sc2mac_wt_data40[7:0])         //|< i
  ,.sc2mac_wt_data41              (sc2mac_wt_data41[7:0])         //|< i
  ,.sc2mac_wt_data42              (sc2mac_wt_data42[7:0])         //|< i
  ,.sc2mac_wt_data43              (sc2mac_wt_data43[7:0])         //|< i
  ,.sc2mac_wt_data44              (sc2mac_wt_data44[7:0])         //|< i
  ,.sc2mac_wt_data45              (sc2mac_wt_data45[7:0])         //|< i
  ,.sc2mac_wt_data46              (sc2mac_wt_data46[7:0])         //|< i
  ,.sc2mac_wt_data47              (sc2mac_wt_data47[7:0])         //|< i
  ,.sc2mac_wt_data48              (sc2mac_wt_data48[7:0])         //|< i
  ,.sc2mac_wt_data49              (sc2mac_wt_data49[7:0])         //|< i
  ,.sc2mac_wt_data50              (sc2mac_wt_data50[7:0])         //|< i
  ,.sc2mac_wt_data51              (sc2mac_wt_data51[7:0])         //|< i
  ,.sc2mac_wt_data52              (sc2mac_wt_data52[7:0])         //|< i
  ,.sc2mac_wt_data53              (sc2mac_wt_data53[7:0])         //|< i
  ,.sc2mac_wt_data54              (sc2mac_wt_data54[7:0])         //|< i
  ,.sc2mac_wt_data55              (sc2mac_wt_data55[7:0])         //|< i
  ,.sc2mac_wt_data56              (sc2mac_wt_data56[7:0])         //|< i
  ,.sc2mac_wt_data57              (sc2mac_wt_data57[7:0])         //|< i
  ,.sc2mac_wt_data58              (sc2mac_wt_data58[7:0])         //|< i
  ,.sc2mac_wt_data59              (sc2mac_wt_data59[7:0])         //|< i
  ,.sc2mac_wt_data60              (sc2mac_wt_data60[7:0])         //|< i
  ,.sc2mac_wt_data61              (sc2mac_wt_data61[7:0])         //|< i
  ,.sc2mac_wt_data62              (sc2mac_wt_data62[7:0])         //|< i
  ,.sc2mac_wt_data63              (sc2mac_wt_data63[7:0])         //|< i
  ,.sc2mac_wt_data64              (sc2mac_wt_data64[7:0])         //|< i
  ,.sc2mac_wt_data65              (sc2mac_wt_data65[7:0])         //|< i
  ,.sc2mac_wt_data66              (sc2mac_wt_data66[7:0])         //|< i
  ,.sc2mac_wt_data67              (sc2mac_wt_data67[7:0])         //|< i
  ,.sc2mac_wt_data68              (sc2mac_wt_data68[7:0])         //|< i
  ,.sc2mac_wt_data69              (sc2mac_wt_data69[7:0])         //|< i
  ,.sc2mac_wt_data70              (sc2mac_wt_data70[7:0])         //|< i
  ,.sc2mac_wt_data71              (sc2mac_wt_data71[7:0])         //|< i
  ,.sc2mac_wt_data72              (sc2mac_wt_data72[7:0])         //|< i
  ,.sc2mac_wt_data73              (sc2mac_wt_data73[7:0])         //|< i
  ,.sc2mac_wt_data74              (sc2mac_wt_data74[7:0])         //|< i
  ,.sc2mac_wt_data75              (sc2mac_wt_data75[7:0])         //|< i
  ,.sc2mac_wt_data76              (sc2mac_wt_data76[7:0])         //|< i
  ,.sc2mac_wt_data77              (sc2mac_wt_data77[7:0])         //|< i
  ,.sc2mac_wt_data78              (sc2mac_wt_data78[7:0])         //|< i
  ,.sc2mac_wt_data79              (sc2mac_wt_data79[7:0])         //|< i
  ,.sc2mac_wt_data80              (sc2mac_wt_data80[7:0])         //|< i
  ,.sc2mac_wt_data81              (sc2mac_wt_data81[7:0])         //|< i
  ,.sc2mac_wt_data82              (sc2mac_wt_data82[7:0])         //|< i
  ,.sc2mac_wt_data83              (sc2mac_wt_data83[7:0])         //|< i
  ,.sc2mac_wt_data84              (sc2mac_wt_data84[7:0])         //|< i
  ,.sc2mac_wt_data85              (sc2mac_wt_data85[7:0])         //|< i
  ,.sc2mac_wt_data86              (sc2mac_wt_data86[7:0])         //|< i
  ,.sc2mac_wt_data87              (sc2mac_wt_data87[7:0])         //|< i
  ,.sc2mac_wt_data88              (sc2mac_wt_data88[7:0])         //|< i
  ,.sc2mac_wt_data89              (sc2mac_wt_data89[7:0])         //|< i
  ,.sc2mac_wt_data90              (sc2mac_wt_data90[7:0])         //|< i
  ,.sc2mac_wt_data91              (sc2mac_wt_data91[7:0])         //|< i
  ,.sc2mac_wt_data92              (sc2mac_wt_data92[7:0])         //|< i
  ,.sc2mac_wt_data93              (sc2mac_wt_data93[7:0])         //|< i
  ,.sc2mac_wt_data94              (sc2mac_wt_data94[7:0])         //|< i
  ,.sc2mac_wt_data95              (sc2mac_wt_data95[7:0])         //|< i
  ,.sc2mac_wt_data96              (sc2mac_wt_data96[7:0])         //|< i
  ,.sc2mac_wt_data97              (sc2mac_wt_data97[7:0])         //|< i
  ,.sc2mac_wt_data98              (sc2mac_wt_data98[7:0])         //|< i
  ,.sc2mac_wt_data99              (sc2mac_wt_data99[7:0])         //|< i
  ,.sc2mac_wt_data100             (sc2mac_wt_data100[7:0])        //|< i
  ,.sc2mac_wt_data101             (sc2mac_wt_data101[7:0])        //|< i
  ,.sc2mac_wt_data102             (sc2mac_wt_data102[7:0])        //|< i
  ,.sc2mac_wt_data103             (sc2mac_wt_data103[7:0])        //|< i
  ,.sc2mac_wt_data104             (sc2mac_wt_data104[7:0])        //|< i
  ,.sc2mac_wt_data105             (sc2mac_wt_data105[7:0])        //|< i
  ,.sc2mac_wt_data106             (sc2mac_wt_data106[7:0])        //|< i
  ,.sc2mac_wt_data107             (sc2mac_wt_data107[7:0])        //|< i
  ,.sc2mac_wt_data108             (sc2mac_wt_data108[7:0])        //|< i
  ,.sc2mac_wt_data109             (sc2mac_wt_data109[7:0])        //|< i
  ,.sc2mac_wt_data110             (sc2mac_wt_data110[7:0])        //|< i
  ,.sc2mac_wt_data111             (sc2mac_wt_data111[7:0])        //|< i
  ,.sc2mac_wt_data112             (sc2mac_wt_data112[7:0])        //|< i
  ,.sc2mac_wt_data113             (sc2mac_wt_data113[7:0])        //|< i
  ,.sc2mac_wt_data114             (sc2mac_wt_data114[7:0])        //|< i
  ,.sc2mac_wt_data115             (sc2mac_wt_data115[7:0])        //|< i
  ,.sc2mac_wt_data116             (sc2mac_wt_data116[7:0])        //|< i
  ,.sc2mac_wt_data117             (sc2mac_wt_data117[7:0])        //|< i
  ,.sc2mac_wt_data118             (sc2mac_wt_data118[7:0])        //|< i
  ,.sc2mac_wt_data119             (sc2mac_wt_data119[7:0])        //|< i
  ,.sc2mac_wt_data120             (sc2mac_wt_data120[7:0])        //|< i
  ,.sc2mac_wt_data121             (sc2mac_wt_data121[7:0])        //|< i
  ,.sc2mac_wt_data122             (sc2mac_wt_data122[7:0])        //|< i
  ,.sc2mac_wt_data123             (sc2mac_wt_data123[7:0])        //|< i
  ,.sc2mac_wt_data124             (sc2mac_wt_data124[7:0])        //|< i
  ,.sc2mac_wt_data125             (sc2mac_wt_data125[7:0])        //|< i
  ,.sc2mac_wt_data126             (sc2mac_wt_data126[7:0])        //|< i
  ,.sc2mac_wt_data127             (sc2mac_wt_data127[7:0])        //|< i
  ,.sc2mac_wt_sel                 (sc2mac_wt_sel[7:0])            //|< i
  ,.mac2accu_pvld                 (mac2accu_pvld)                 //|> o
  ,.mac2accu_mask                 (mac2accu_mask[7:0])            //|> o
  ,.mac2accu_mode                 (mac2accu_mode[7:0])            //|> o
  ,.mac2accu_data0                (mac2accu_data0[175:0])         //|> o
  ,.mac2accu_data1                (mac2accu_data1[175:0])         //|> o
  ,.mac2accu_data2                (mac2accu_data2[175:0])         //|> o
  ,.mac2accu_data3                (mac2accu_data3[175:0])         //|> o
  ,.mac2accu_data4                (mac2accu_data4[175:0])         //|> o
  ,.mac2accu_data5                (mac2accu_data5[175:0])         //|> o
  ,.mac2accu_data6                (mac2accu_data6[175:0])         //|> o
  ,.mac2accu_data7                (mac2accu_data7[175:0])         //|> o
  ,.mac2accu_pd                   (mac2accu_pd[8:0])              //|> o
  ,.reg2dp_op_en                  (reg2dp_op_en[0])               //|< w
  ,.reg2dp_conv_mode              (reg2dp_conv_mode[0])           //|< w
  ,.reg2dp_proc_precision         (reg2dp_proc_precision[1:0])    //|< w
  ,.dp2reg_done                   (dp2reg_done)                   //|> w
  ,.dla_clk_ovr_on_sync           (dla_clk_ovr_on_sync)           //|< i
  ,.global_clk_ovr_on_sync        (global_clk_ovr_on_sync)        //|< i
  ,.tmc2slcg_disable_clock_gating (tmc2slcg_disable_clock_gating) //|< i
  ,.slcg_op_en                    (slcg_op_en[10:0])              //|< w
  );
*/
//==========================================================
// reg
//==========================================================
NV_NVDLA_CMAC_reg u_reg (
   .nvdla_core_clk                (nvdla_core_clk)                //|< i
  ,.nvdla_core_rstn               (nvdla_core_rstn)               //|< i
  ,.csb2cmac_a_req_pd             (csb2cmac_a_req_pd[62:0])       //|< i
  ,.csb2cmac_a_req_pvld           (csb2cmac_a_req_pvld)           //|< i
  ,.dp2reg_done                   (dp2reg_done)                   //|< w
  ,.cmac_a2csb_resp_pd            (cmac_a2csb_resp_pd[33:0])      //|> o
  ,.cmac_a2csb_resp_valid         (cmac_a2csb_resp_valid)         //|> o
  ,.csb2cmac_a_req_prdy           (csb2cmac_a_req_prdy)           //|> o
  ,.reg2dp_conv_mode              (reg2dp_conv_mode)              //|> w
  ,.reg2dp_op_en                  (reg2dp_op_en)                  //|> w
  ,.reg2dp_proc_precision         (reg2dp_proc_precision[1:0])    //|> w
  ,.slcg_op_en                    (slcg_op_en[10:0])              //|> w
  );


endmodule // NV_NVDLA_cmac

