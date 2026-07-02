#loc = loc("counter.hw.mlir":2:67)
"builtin.module"() ({
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input rst : i1, input en : i1, output count : i8>, parameters = [], result_locs = [#loc], sym_name = "counter"}> ({
  ^bb0(%arg0: i1, %arg1: i1, %arg2: i1):
    %0 = "hw.constant"() <{value = true}> : () -> i1
    %1 = "hw.constant"() <{value = 1 : i8}> : () -> i8
    %2 = "hw.constant"() <{value = 0 : i8}> : () -> i8
    %3 = "comb.add"(%10, %1) : (i8, i8) -> i8
    %4 = "comb.xor"(%arg1, %0) : (i1, i1) -> i1
    %5 = "comb.and"(%arg2, %4) : (i1, i1) -> i1
    %6 = "comb.mux"(%5, %3, %2) : (i1, i8, i8) -> i8
    %7 = "seq.to_clock"(%arg0) : (i1) -> !seq.clock
    %8 = "comb.or"(%arg1, %arg2) : (i1, i1) -> i1
    %9 = "comb.mux"(%8, %6, %10) <{twoState}> : (i1, i8, i8) -> i8
    %10 = "seq.firreg"(%9, %7) <{name = "count_q"}> : (i8, !seq.clock) -> i8
    "hw.output"(%10) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

