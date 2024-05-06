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

### Retention set exploration

### CEX-guided retention register search

## Software dependencies
