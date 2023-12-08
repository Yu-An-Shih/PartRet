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

struct MakePowerCollapsibleWorker
{
	RTLIL::Module *module_;
	dict<std::string, RTLIL::Const> reg_reset_map_;

	void parse_reset_vals_file(std::string reset_vals_file)
	{
		reg_reset_map_.clear();
		
		std::ifstream file(reset_vals_file);
		if (!file.is_open())
			log_error("Can't open file %s\n", reset_vals_file.c_str());
		
		std::string reg, reset;
		std::regex dot_or_left_bracket("[\\.\\[]");	// '.' or '['
		std::regex right_bracket("\\]");
		while (std::getline(file, reg) && std::getline(file, reset))	// reg: register name, reset: reset value in binary format (e.g., 8'b0)
		{
			// Rename register to match its flattened name
			reg = std::regex_replace(reg, dot_or_left_bracket, "__");
			reg = std::regex_replace(reg, right_bracket, "");
			reg = "\\" + reg;
			
			// Reset value
			size_t pos = reset.find("'b");
			int reset_width = std::stoi(reset.substr(0, pos));
			std::string reset_val = reset.substr(pos + 2);

			if (reset_val.size() < (size_t)reset_width)		// e.g., 8'b0 -> 8'b00000000
				reset_val = std::string(reset_width - reset_val.size(), '0') + reset_val;

			//log("reg: %s, width, %d, reset_val: %s\n", reg.c_str(), reset_width, reset_val.c_str());

			// Store reset_val as a vector of boolean values
			vector<bool> reset_val_vec;
			for (auto rit = reset_val.rbegin(); rit != reset_val.rend(); ++rit)
			{
				if (*rit == '0')
					reset_val_vec.push_back(false);
				else if (*rit == '1')
					reset_val_vec.push_back(true);
				else
					log_error("Invalid reset value: %s\n", reset_val.c_str());
			}
			
			reg_reset_map_[reg] = RTLIL::Const(reset_val_vec);
		}
		
		file.close();
	}

	RTLIL::Wire *addInput(RTLIL::IdString name, int width = 1)
	{
		RTLIL::Wire *wire = module_->addWire(name, width);
		wire->port_input = true;
		return wire;
	}

	void addStandbyAndRetentionInputs()
	{
		// Add the standby condition as an input wire
		addInput(IdString("\\standby_cond"), 1);

		// Add the retention selection signal for each register as an input wire
		for (auto &it : reg_reset_map_)
			addInput(IdString(it.first + "_ret"), 1);

		module_->fixup_ports();
	}

	MakePowerCollapsibleWorker(RTLIL::Module *module, std::string reset_vals_file)
		: module_(module)
	{
		parse_reset_vals_file(reset_vals_file);

		addStandbyAndRetentionInputs();

		// Find and record all the register (flip-flop) cells
		// 		ISSUE: Are there any other types of registers?
		CellTypes ct;
		ct.setup_type(ID($dff), {ID::CLK, ID::D}, {ID::Q});
		ct.setup_type(ID($adff), {ID::CLK, ID::ARST, ID::D}, {ID::Q});
		//ct.setup_type(ID($sdff), {ID::CLK, ID::SRST, ID::D}, {ID::Q});

		std::vector<RTLIL::Cell*> reg_cells;
		reg_cells.reserve(module_->cells_.size());
		for (auto &it : module_->cells_) {
			if (ct.cell_known(it.second->type))
				reg_cells.push_back(it.second);
		}
		
		RTLIL::Wire *standby_cond = module_->wire("\\standby_cond");
		for (auto reg_cell : reg_cells)
		{
			int width = reg_cell->getParam(ID::WIDTH).as_int();
			RTLIL::SigChunk reg_chunk = reg_cell->getPort(ID::Q).as_chunk();	//	ISSUE: Assumes the output port of the register cell is a SigChunk - What if it is a combination of multiple registers?
			
			if (reg_chunk.wire->name.str()[0] == '$')
			{
				log("Warning: Skipping internal register cell: %s\n", reg_chunk.wire->name.c_str());
				continue;
			}
			//log("Register cell: %s, width: %d\n", reg_chunk.wire->name.c_str(), width);

			/* Method 1 */
			// Get or create required wires
			RTLIL::Wire *ret_sel = module_->wire(reg_chunk.wire->name.str() + "_ret");

			RTLIL::Wire *ret_mux_out = module_->addWire(NEW_ID, width);
			RTLIL::Wire *standby_mux_out = module_->addWire(NEW_ID, width);

			// Get the reset value for the register
			RTLIL::Const reset_val_full = reg_reset_map_.at(reg_chunk.wire->name.str());
			RTLIL::Const reset_val = reset_val_full.extract(reg_chunk.offset, reg_chunk.width);

			// Create a mux for the retention condition
			//RTLIL::SigSpec ret_a = RTLIL::SigSpec(RTLIL::State::Sx, width);
			RTLIL::SigSpec ret_a = RTLIL::SigSpec(reset_val);
			RTLIL::SigSpec ret_b = reg_cell->getPort(ID::Q);
			RTLIL::SigSpec ret_s = RTLIL::SigSpec(ret_sel);
			RTLIL::SigSpec ret_y = RTLIL::SigSpec(ret_mux_out);
			module_->addMux(NEW_ID, ret_a, ret_b, ret_s, ret_y);		// \A, \B, \S, \Y

			// Create a mux for the standby condition
			RTLIL::SigSpec standby_a = reg_cell->getPort(ID::D);
			RTLIL::SigSpec standby_b = RTLIL::SigSpec(ret_mux_out);
			RTLIL::SigSpec standby_s = RTLIL::SigSpec(standby_cond);
			RTLIL::SigSpec standby_y = RTLIL::SigSpec(standby_mux_out);
			module_->addMux(NEW_ID, standby_a, standby_b, standby_s, standby_y);		// \A, \B, \S, \Y

			// Modify the input port of the register
			reg_cell->setPort(ID::D, RTLIL::SigSpec(standby_mux_out));

			/* Method 2 */
			// Get or create required wires
			/*RTLIL::Wire *ret_sel = module_->wire(reg_chunk.wire->name.str() + "_ret");

			RTLIL::Wire *not_ret = module_->addWire(NEW_ID, 1);
			RTLIL::Wire *standby_and_not_ret = module_->addWire(NEW_ID, 1);

			RTLIL::Wire *mux_out = module_->addWire(NEW_ID, width);

			// Get the reset value for the register
			RTLIL::Const reset_val_full = reg_reset_map_.at(reg_chunk.wire->name.str());
			RTLIL::Const reset_val = reset_val_full.extract(reg_chunk.offset, reg_chunk.width);

			// Create a NOT - (!ret_sel)
			RTLIL::SigSpec not_a = RTLIL::SigSpec(ret_sel);
			RTLIL::SigSpec not_y = RTLIL::SigSpec(not_ret);
			module_->addNot(NEW_ID, not_a, not_y);

			// Create an AND - (standby_cond & !ret_sel)
			RTLIL::SigSpec and_a = RTLIL::SigSpec(standby_cond);
			RTLIL::SigSpec and_b = RTLIL::SigSpec(not_ret);
			RTLIL::SigSpec and_y = RTLIL::SigSpec(standby_and_not_ret);
			module_->addAnd(NEW_ID, and_a, and_b, and_y);

			// Create a MUX - (standby_cond & !ret_sel) ? D : reset_val
			RTLIL::SigSpec mux_a = reg_cell->getPort(ID::D);
			RTLIL::SigSpec mux_b = RTLIL::SigSpec(reset_val);
			RTLIL::SigSpec mux_s = RTLIL::SigSpec(standby_and_not_ret);
			RTLIL::SigSpec mux_y = RTLIL::SigSpec(mux_out);
			module_->addMux(NEW_ID, mux_a, mux_b, mux_s, mux_y);

			// Modify the input port of the register
			reg_cell->setPort(ID::D, RTLIL::SigSpec(mux_out));*/

		}
	}
};


// Rename improperly-named wires
// 	Note: all public wires should only contain alphanumeric characters and underscores
// 1. Flattened wires: replace '.' with '__'
//		E.g. \top.sub1.sub2 -> \top__sub1__sub2
// 2. Registers converted from memories: replace '[' and ']' with '__'
//		E.g. \top.mem[0] -> \top__mem__0
void rename_wires(RTLIL::Module *module)
{
	std::vector<RTLIL::Wire*> improper_wires;
	improper_wires.reserve(module->wires_.size());
	for (auto &it : module->wires_)
	{
		std::string name = it.first.str();
		RTLIL::Wire *wire = it.second;
		if (name[0] == '\\' && (name.find('.') != std::string::npos || name.find('[') != std::string::npos))
			improper_wires.push_back(wire);
	}
	
	std::regex dot_or_left_bracket("[\\.\\[]");	// '.' or '['
	std::regex right_bracket("\\]");
	for (auto wire : improper_wires)
	{
		std::string name = wire->name.str();
		std::string name_new = std::regex_replace(name, dot_or_left_bracket, "__");
		name_new = std::regex_replace(name_new, right_bracket, "");
		//log("wire: %s\n", wire->name.c_str());
		//log("new name: %s\n", name_new.c_str());
		
		module->rename(wire, RTLIL::IdString(name_new));
	}
}

struct MakePowerCollapsiblePass : public Pass {
	MakePowerCollapsiblePass() : Pass("make_power_collapsible", "") { }
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
		log_header(design, "Annotate the design to mimic the behavior of a power-collapsible design.\n");

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
		RTLIL::Module *module = design->top_module();
		
		// Rename improperly-named wires
		rename_wires(module);

		/*std::vector<RTLIL::Wire*> flattened_wires;
		flattened_wires.reserve(module->wires_.size());
		for (auto &it : module->wires_)
		{
			std::string name = it.first.str();
			RTLIL::Wire *wire = it.second;
			if (name[0] == '\\' && name.find('.') != std::string::npos)
				flattened_wires.push_back(wire);
		}
		
		std::regex dot("\\.");
		for (auto wire : flattened_wires)
		{
			std::string name = wire->name.str();
			std::string name_new = std::regex_replace(name, dot, "__");
			//log("wire: %s\n", wire->name.c_str());
			//log("new name: %s\n", name_new.c_str());
			
			module->rename(wire, RTLIL::IdString(name_new));
		}*/

		// Call the worker
		MakePowerCollapsibleWorker worker(module, reset_vals_file);

	}
} MakePowerCollapsiblePass;

PRIVATE_NAMESPACE_END
