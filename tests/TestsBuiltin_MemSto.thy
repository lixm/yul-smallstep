(******
Tests for builtin functions of Yul language for memory and storage access
Copyright (C) 2020  Ning Han

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Library General Public
License as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Library General Public License for more details.
******)

chapter \<open>the tests of formal Yul language about memory and storage built-in function\<close>

theory "TestsBuiltin_MemSto" 

imports 
  Main "../Syntax" "../Typing" "../SmallStep" "../utils/Keccak" Common_defs

begin 
(*M1 ---
  {  mstore(0x01, 11289525020298692601998108039226097635691122580326809888208074282503241728)
    x := mload(0x01)   
  }
*)
(*
value "multi_step tre0_ex1 gstk_M1 1 20"
value "multi_step tre0_ex1 gstk_M1 2 20"
value "multi_step tre0_ex1 gstk_M1 3 20"
value "multi_step tre0_ex1 gstk_M1 4 20"
value "multi_step tre0_ex1 gstk_M1 5 20"
value "multi_step tre0_ex1 gstk_M1 6 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_M1 5 20)
  [(x_id, (NL 11289525020298692601998108039226097635691122580326809888208074282503241728) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_M1 6 20) (3000000-3-3-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_M1 6 20)"


(*M2 ---
     mstore8(0x01,0x11)
    x := mload(0x01)  
*)
(*
value "multi_step tre0_ex1 gstk_M2 1 20"
value "multi_step tre0_ex1 gstk_M2 2 20"
value "multi_step tre0_ex1 gstk_M2 3 20"
value "multi_step tre0_ex1 gstk_M2 4 20"
value "multi_step tre0_ex1 gstk_M2 5 20"
value "multi_step tre0_ex1 gstk_M2 6 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_M2 5 20)
  [(x_id, 
    (NL 7691092201792325725438170817979025252018668099114851189875736584839327973633) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_M2 6 20) (3000000-3-3-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_M2 6 20)"


(*M3 ---
     sstore(0x01,0x11)
    x := sload(0x01)  
*)
(*
value "multi_step tre0_ex1 gstk_M3 1 20"
value "multi_step tre0_ex1 gstk_M3 2 20"
value "multi_step tre0_ex1 gstk_M3 3 20"
value "multi_step tre0_ex1 gstk_M3 4 20"
value "multi_step tre0_ex1 gstk_M3 5 20"
value "multi_step tre0_ex1 gstk_M3 6 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_M3 5 20) [(x_id, (NL 17) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_M3 6 20) (3000000-20000-200-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_M3 6 20)"


(*M4 ---
  {
    a1 := msize()
  }
*)
(*
value "multi_step tre0_ex1 gstk_M4 1 20"
value "multi_step tre0_ex1 gstk_M4 2 20"
value "multi_step tre0_ex1 gstk_M4 3 20"
value "multi_step tre0_ex1 gstk_M4 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_M4 3 20) [(a1_id, (NL 96) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_M4 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_M4 4 20)"


(*M5 --- (xx=0) \<rightarrow>* (xx=9)
  let xx
  if f3() {
    mstore(0x01, f2(exp(2,2),5))
    xx := mload(0x01)
  }
*)
(*
value "multi_step tre0_ex1 gstk_M5 1 20"
value "multi_step tre0_ex1 gstk_M5 2 20"
value "multi_step tre0_ex1 gstk_M5 3 20"
value "multi_step tre0_ex1 gstk_M5 4 20"
value "multi_step tre0_ex1 gstk_M5 5 20"
value "multi_step tre0_ex1 gstk_M5 6 20"
value "multi_step tre0_ex1 gstk_M5 7 20"
value "multi_step tre0_ex1 gstk_M5 8 20"
value "multi_step tre0_ex1 gstk_M5 9 20"
value "multi_step tre0_ex1 gstk_M5 10 20"
value "multi_step tre0_ex1 gstk_M5 11 20"
value "multi_step tre0_ex1 gstk_M5 12 20"
value "multi_step tre0_ex1 gstk_M5 13 20"
value "multi_step tre0_ex1 gstk_M5 14 20"
value "multi_step tre0_ex1 gstk_M5 15 20"
value "multi_step tre0_ex1 gstk_M5 16 20"
value "multi_step tre0_ex1 gstk_M5 17 20"
value "multi_step tre0_ex1 gstk_M5 18 20"
value "multi_step tre0_ex1 gstk_M5 19 20"
value "multi_step tre0_ex1 gstk_M5 20 20"
value "multi_step tre0_ex1 gstk_M5 21 20"
value "multi_step tre0_ex1 gstk_M5 22 20"
value "multi_step tre0_ex1 gstk_M5 23 20"
value "multi_step tre0_ex1 gstk_M5 24 20"
value "multi_step tre0_ex1 gstk_M5 25 20"
value "multi_step tre0_ex1 gstk_M5 26 20"
value "multi_step tre0_ex1 gstk_M5 27 20"
value "multi_step tre0_ex1 gstk_M5 28 20"
value "multi_step tre0_ex1 gstk_M5 29 20"
value "multi_step tre0_ex1 gstk_M5 30 20"
value "multi_step tre0_ex1 gstk_M5 31 20"
value "multi_step tre0_ex1 gstk_M5 32 20"
value "multi_step tre0_ex1 gstk_M5 33 20"
value "multi_step tre0_ex1 gstk_M5 34 20"
value "multi_step tre0_ex1 gstk_M5 35 20"
value "multi_step tre0_ex1 gstk_M5 36 20"
value "multi_step tre0_ex1 gstk_M5 37 20"
value "multi_step tre0_ex1 gstk_M5 38 20"
value "multi_step tre0_ex1 gstk_M5 39 20"
value "multi_step tre0_ex1 gstk_M5 40 20"
value "multi_step tre0_ex1 gstk_M5 41 20"
value "multi_step tre0_ex1 gstk_M5 42 20"
value "multi_step tre0_ex1 gstk_M5 43 20"
value "multi_step tre0_ex1 gstk_M5 44 20"
value "multi_step tre0_ex1 gstk_M5 45 20"
value "multi_step tre0_ex1 gstk_M5 46 20"
value "multi_step tre0_ex1 gstk_M5 47 20"
value "multi_step tre0_ex1 gstk_M5 48 20"
value "multi_step tre0_ex1 gstk_M5 49 20"
value "multi_step tre0_ex1 gstk_M5 50 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_M5 49 20) [(xx_id, (NL 20) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_M5 50 20) (3000000-183)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_M5 50 20)"


(*M6 --- same code as M5, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_M6 1 20"
value "multi_step tre0_ex1 gstk_M6 2 20"
value "multi_step tre0_ex1 gstk_M6 3 20"
value "multi_step tre0_ex1 gstk_M6 4 20"
value "multi_step tre0_ex1 gstk_M6 5 20"
value "multi_step tre0_ex1 gstk_M6 6 20"
value "multi_step tre0_ex1 gstk_M6 7 20"
value "multi_step tre0_ex1 gstk_M6 8 20"
value "multi_step tre0_ex1 gstk_M6 9 20"
value "multi_step tre0_ex1 gstk_M6 10 20"
value "multi_step tre0_ex1 gstk_M6 11 20"
value "multi_step tre0_ex1 gstk_M6 12 20"
value "multi_step tre0_ex1 gstk_M6 13 20"
value "multi_step tre0_ex1 gstk_M6 14 20"
value "multi_step tre0_ex1 gstk_M6 15 20"
value "multi_step tre0_ex1 gstk_M6 16 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_M6 16 20)"


(*M7 --- same code as M5, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_M7 1 20"
value "multi_step tre0_ex1 gstk_M7 2 20"
value "multi_step tre0_ex1 gstk_M7 3 20"
value "multi_step tre0_ex1 gstk_M7 4 20"
value "multi_step tre0_ex1 gstk_M7 5 20"
value "multi_step tre0_ex1 gstk_M7 6 20"
value "multi_step tre0_ex1 gstk_M7 7 20"
value "multi_step tre0_ex1 gstk_M7 8 20"
value "multi_step tre0_ex1 gstk_M7 9 20"
value "multi_step tre0_ex1 gstk_M7 10 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_M7 10 20)"


end