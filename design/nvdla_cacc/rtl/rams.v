// Note: This file contains simple memory units designed by Yu-An Shih to simplify the RAM design.
//       The purpose of this is to avoid complicated issues when using the JasperGold tool.

`timescale 1ns / 10ps

module nv_ram_rws_32x512 (
        clk,
        ra,
        re,
        dout,
        wa,
        we,
        di,
        pwrbus_ram_pd
);

// port list
input           clk;
input  [4:0]    ra;
input           re;
output [511:0]  dout;
input  [4:0]    wa;
input           we;
input  [511:0]  di;
input  [31:0]   pwrbus_ram_pd;

reg [511:0] ram [0:31];
reg [511:0] dout_r;

assign dout = dout_r;

always @(posedge clk) begin
    if (re) begin
        dout_r <= ram[ra];
    end
    if (we) begin
        ram[wa] <= di;
    end
end

endmodule

module nv_ram_rws_32x544 (
        clk,
        ra,
        re,
        dout,
        wa,
        we,
        di,
        pwrbus_ram_pd
);

// port list
input           clk;
input  [4:0]    ra;
input           re;
output [543:0]  dout;
input  [4:0]    wa;
input           we;
input  [543:0]  di;
input  [31:0]   pwrbus_ram_pd;

reg [543:0] ram [0:31];
reg [543:0] dout_r;

assign dout = dout_r;

always @(posedge clk) begin
    if (re) begin
        dout_r <= ram[ra];
    end
    if (we) begin
        ram[wa] <= di;
    end
end

endmodule

module nv_ram_rws_32x768 (
        clk,
        ra,
        re,
        dout,
        wa,
        we,
        di,
        pwrbus_ram_pd
);

// port list
input           clk;
input  [4:0]    ra;
input           re;
output [767:0]  dout;
input  [4:0]    wa;
input           we;
input  [767:0]  di;
input  [31:0]   pwrbus_ram_pd;

reg [767:0] ram [0:31];
reg [767:0] dout_r;

assign dout = dout_r;

always @(posedge clk) begin
    if (re) begin
        dout_r <= ram[ra];
    end
    if (we) begin
        ram[wa] <= di;
    end
end

endmodule
