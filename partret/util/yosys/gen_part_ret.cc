/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

/*#include "kernel/register.h"
#include "kernel/ffinit.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
//#include "libs/sha1/sha1.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>*/

#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include <regex>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN


struct GenPartRetWorker
{	
	RTLIL::Module *module_;
	dict<std::string, RTLIL::Const> reg_reset_map_;

	void parse_reset_vals_file(std::string reset_vals_file)
	{
		//log("Parsing reset values file: %s\n", reset_vals_file.c_str());
		
		reg_reset_map_.clear();
		
		std::ifstream file(reset_vals_file);
		if (!file.is_open())
			log_error("Can't open file %s\n", reset_vals_file.c_str());
		
		std::string reg, reset;
		while (std::getline(file, reg) && std::getline(file, reset))	// reg: register name, reset: reset value in binary format (e.g., 8'b0)
		{
			// Reset value
			size_t pos = reset.find("'b");
			int reset_width = std::stoi(reset.substr(0, pos));
			std::string reset_val = reset.substr(pos + 2);

			if (reset_val.size() < (size_t)reset_width)		// e.g., 8'b0 -> 8'b00000000
				reset_val = std::string(reset_width - reset_val.size(), '0') + reset_val;

			//log("reg: %s, width, %d, reset_val: %s\n", reg.c_str(), reset_width, reset_val.c_str());

			reg_reset_map_[reg] = RTLIL::Const::from_string(reset_val);
		}
		
		file.close();
	}

	RTLIL::Wire *addRestoreInput()
	{
		RTLIL::Wire *restore = module_->addWire(RTLIL::IdString("\\pr_restore"), 1);
		restore->port_input = true;

		module_->fixup_ports();

		return restore;
	}

	GenPartRetWorker(RTLIL::Module *module, std::string reset_vals_file)
		: module_(module)
	{
		parse_reset_vals_file(reset_vals_file);

		RTLIL::Wire* restore = addRestoreInput();

		// Find and record all the register (flip-flop) cells
		// 		ISSUE: Are there any other types of registers?
		CellTypes ct;
		ct.setup_type(ID($dff), {ID::CLK, ID::D}, {ID::Q});
		ct.setup_type(ID($adff), {ID::CLK, ID::ARST, ID::D}, {ID::Q});
		ct.setup_type(ID($sdff), {ID::CLK, ID::SRST, ID::D}, {ID::Q});

		std::vector<RTLIL::Cell*> reg_cells;
		reg_cells.reserve(module_->cells_.size());
		for (auto &it : module_->cells_) {
			if (ct.cell_known(it.second->type))
				reg_cells.push_back(it.second);
		}

		for (auto reg_cell : reg_cells)
		{
			int width = reg_cell->getParam(ID::WIDTH).as_int();
			RTLIL::SigChunk reg_chunk = reg_cell->getPort(ID::Q).as_chunk();	//	ISSUE: Assumes the output port of the register cell is a SigChunk - What if it is a combination of multiple registers?
			
			std::string reg_name = reg_chunk.wire->name.str();
			reg_name = RTLIL::unescape_id(reg_name);
			if (reg_reset_map_.count(reg_name))
			{
				// Get the reset value for the register
				RTLIL::Const reset_val_full = reg_reset_map_.at(reg_name);
				RTLIL::Const reset_val = reset_val_full.extract(reg_chunk.offset, reg_chunk.width);

				//log("Register: %s, width: %d, reset_val: %s\n", reg_name.c_str(), width, reset_val.as_string().c_str());

				// Get or create required wires
				RTLIL::Wire *mux_out = module_->addWire(NEW_ID, width);
				
				// Create a MUX - restore ? reset_val : D
				RTLIL::SigSpec mux_a = reg_cell->getPort(ID::D);
				RTLIL::SigSpec mux_b = RTLIL::SigSpec(reset_val);
				RTLIL::SigSpec mux_s = RTLIL::SigSpec(restore);
				RTLIL::SigSpec mux_y = RTLIL::SigSpec(mux_out);
				module_->addMux(NEW_ID, mux_a, mux_b, mux_s, mux_y);

				// Modify the input port of the register
				reg_cell->setPort(ID::D, RTLIL::SigSpec(mux_out));

				// TODO: other ways for $adff and $sdff
			}

			// TODO: How to make sure all registers specified in the reset_vals file are handled?
		}
	}
};


struct GenPartRetPass : public Pass {
	GenPartRetPass() : Pass("gen_part_ret", "") { }
	/*void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_merge [options] [selection]\n");
		log("\n");
		log("This pass identifies cells with identical type and input signals. Such cells\n");
		log("are then merged to one cell.\n");
		log("\n");
		log("    -nomux\n");
		log("        Do not merge MUX cells.\n");
		log("\n");
		log("    -share_all\n");
		log("        Operate on all cell types, not just built-in types.\n");
		log("\n");
		log("    -keepdc\n");
		log("        Do not merge flipflops with don't-care bits in their initial value.\n");
		log("\n");
	}*/
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Generate a partial retention design such that the non-retention registers get reset during power-collapse.\n");

		// arguments: file for reset register values
		std::string reset_vals_file;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-reset_vals" && argidx+1 < args.size()) {
				reset_vals_file = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Assert that the design is flattened
		log_assert(design->modules().size() == 1);

		// Call the worker
		GenPartRetWorker worker(design->top_module(), reset_vals_file);

	}
} GenPartRetPass;

PRIVATE_NAMESPACE_END
