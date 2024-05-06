# Automatic Verification and Identification of Partial Retention Register Sets for Low Power Designs

## Reproducing the results

### 1. Set up the verification framework

```
python partret.py <config_file> --setup [-w <work_dir>] [-o <log_file>]
```
For example: `python partret.py design/spi/config/config.json --setup -w design/spi/work/ -o design/spi/work/setup.log`

This command parses design information from `<config_file>` to set up the verification framework. The following files will be generated in `<work_dir>`:
- `design_test.v`: The partial retention design with respect to the retention set specified in `<config_file>`.
- `wrapper.sv`: The top-level SystemVerilog testbench for the verification framework which wraps up the full and partial retention designs.
- `ret_checker.tcl`: Jasper proof script.

In `wrapper.sv` and `ret_checker.tcl`, the user can find instructions for adding interface constraints, customizing functional equivalence properties, etc. To let users reproduce our results, we provide a work directory with our own customized `wrapper.sv` and `ret_checker.tcl` for each design.

### 2. Retention set exploration (with CEX-guided approach)

```
python partret.py <config_file> --optimize combine [-w <work_dir>] [-o <log_file>]
```
For example: `python partret.py design/spi/config/config.json --optimize combine -w design/spi/work/ -o design/spi/work/set_explore.log`

This command executes the retention set exploration algorithm. To reproduce our results, please keep the provided `wrapper.sv` and `ret_checker.tcl` files in `<work_dir>`. Information such as runtime will be recorded in `<log_file>`. The identified partial retention set can be found in a solution file in `<work_dir>`. By default, the file is named `solution.json`.

### 3. CEX-guided retention register search

```
python partret.py <config_file> --optimize cex-guided [-w <work_dir>] [-o <log_file>]
```
For example: `python partret.py design/spi/config/config.json --optimize cex-guided -w design/spi/work/ -o design/spi/work/cex_guided.log`

This command executes the CEX-guided retention register search algorithm. To reproduce our results, please keep the provided `wrapper.sv` and `ret_checker.tcl` files in `<work_dir>`. Information such as runtime will be recorded in `<log_file>`. The identified partial retention set can be found in a solution file in `<work_dir>`. By default, the file is named `solution.json`.

## Software dependencies
