// ================================================================
// NVDLA Open Source Project
// 
// Copyright(c) 2016 - 2017 NVIDIA Corporation.  Licensed under the
// NVDLA Open Hardware License; Check "LICENSE" which comes with 
// this distribution for more information.
// ================================================================

// File Name: NV_NVDLA_CACC_slcg.v

module NV_NVDLA_CACC_slcg (
   dla_clk_ovr_on_sync
  ,global_clk_ovr_on_sync
  ,nvdla_core_clk
  ,nvdla_core_rstn
  ,slcg_en_src_0
  ,slcg_en_src_1
  ,tmc2slcg_disable_clock_gating
  ,nvdla_core_gated_clk
  );

input   dla_clk_ovr_on_sync;
input   global_clk_ovr_on_sync;
input   nvdla_core_clk;
input   nvdla_core_rstn;
input   slcg_en_src_0;
input   slcg_en_src_1;
input   tmc2slcg_disable_clock_gating;
output  nvdla_core_gated_clk;
wire    enable;

//assign nvdla_core_gated_clk = 1'b0;
assign nvdla_core_gated_clk = nvdla_core_clk;
//assign nvdla_core_gated_clk = (slcg_en_src_0 & slcg_en_src_1) ? nvdla_core_clk : 1'b0;

endmodule // NV_NVDLA_CACC_slcg

