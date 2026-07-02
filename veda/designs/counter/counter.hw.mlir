module {
  hw.module @counter(in %clk : i1, in %rst : i1, in %en : i1, out count : i8) {
    %true = hw.constant true
    %c1_i8 = hw.constant 1 : i8
    %c0_i8 = hw.constant 0 : i8
    %0 = comb.add %count_q, %c1_i8 : i8
    %1 = comb.xor %rst, %true : i1
    %2 = comb.and %en, %1 : i1
    %3 = comb.mux %2, %0, %c0_i8 : i8
    %4 = seq.to_clock %clk
    %5 = comb.or %rst, %en : i1
    %6 = comb.mux bin %5, %3, %count_q : i8
    %count_q = seq.firreg %6 clock %4 : i8
    hw.output %count_q : i8
  }
}
