(******
Tests for builtin functions of Yul language for query of blockchain state
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

chapter \<open>the tests of formal Yul language about state queries built-in function and others\<close>

theory "TestsBuiltin_SttQue" 

imports 
  Main "../Syntax" "../Typing" "../SmallStep" "../utils/Keccak" Common_defs

begin 
(*S1 --- (a1=0) \<rightarrow>* (a1=65524)
    {
      a1 := balance(a1)
    }
*)
(*
value "multi_step tre0_ex1 gstk_S1 1 20"
value "multi_step tre0_ex1 gstk_S1 2 20"
value "multi_step tre0_ex1 gstk_S1 3 20"
value "multi_step tre0_ex1 gstk_S1 4 20"
value "multi_step tre0_ex1 gstk_S1 5 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S1 4 20) [(a1_id, (NL 65524) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S1 5 20) (3000000-3-400-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S1 5 20)"


(*S2 --- (a1=0) \<rightarrow>* (a1=1154414090619811796818182302139415280051214250812)
    {
      a1 := caller()
    }
*)
(*
value "multi_step tre0_ex1 gstk_S2 1 20"
value "multi_step tre0_ex1 gstk_S2 2 20"
value "multi_step tre0_ex1 gstk_S2 3 20"
value "multi_step tre0_ex1 gstk_S2 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S2 3 20)
  [(a1_id, (NL 1154414090619811796818182302139415280051214250812) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S2 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S2 4 20)"


(*S3 --- (a1=0) \<rightarrow>* (a1=65535)
    {
      a1 := callvalue()
    }
*)
(*
value "multi_step tre0_ex1 gstk_S3 1 20"
value "multi_step tre0_ex1 gstk_S3 2 20" 
value "multi_step tre0_ex1 gstk_S3 3 20"
value "multi_step tre0_ex1 gstk_S3 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S3 3 20)
  [(a1_id, (NL 65535) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S3 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S3 4 20)"


(*S4 --- (x=0) \<rightarrow>* (x=8198059952630154640245901447353345481032286063759317239499370173610174971904)
    x := calldataload(0x1)
*)
(*
value "multi_step tre0_ex1 gstk_S4 1 20"
value "multi_step tre0_ex1 gstk_S4 2 20"
value "multi_step tre0_ex1 gstk_S4 3 20"
value "multi_step tre0_ex1 gstk_S4 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S4 3 20)
  [(x_id, 
    (NL 8198059952630154640245901447353345481032286063759317239499370173610174971904) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S4 4 20) (3000000-3-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S4 4 20)"


(*S5 --- (x=0) \<rightarrow>* (x=78792666924179831118215123113636620175678209199)
   x := address()
*)
(*
value "multi_step tre0_ex1 gstk_S5 1 20"
value "multi_step tre0_ex1 gstk_S5 2 20"
value "multi_step tre0_ex1 gstk_S5 3 20"
value "multi_step tre0_ex1 gstk_S5 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S5 3 20)
  [(x_id, (NL 78792666924179831118215123113636620175678209199) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S5 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S5 4 20)"


(*S6 --- (x=0) \<rightarrow>* (x=4)
    calldatacopy(0, 54, 33)
   x := calldatasize()
*)
(*
value "multi_step tre0_ex1 gstk_S6 1 20"
value "multi_step tre0_ex1 gstk_S6 2 20"
value "multi_step tre0_ex1 gstk_S6 3 20"
value "multi_step tre0_ex1 gstk_S6 4 20"
value "multi_step tre0_ex1 gstk_S6 5 20"
value "multi_step tre0_ex1 gstk_S6 6 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S6 5 20)
  [(x_id, (NL 4) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S6 6 20) (3000000-18)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S6 6 20)"


(*S7 --- (x=0) \<rightarrow>* (x=3000000)
   x := gas()
*)
(*
value "multi_step tre0_ex1 gstk_S7 1 20"
value "multi_step tre0_ex1 gstk_S7 2 20"
value "multi_step tre0_ex1 gstk_S7 3 20"
value "multi_step tre0_ex1 gstk_S7 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S7 3 20)
  [(x_id, (NL 3000000) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S7 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S7 4 20)"


(*S8 --- (x=0) \<rightarrow>* (x=1154414090619811796818182302139415280051214250812)
   x := origin()
*)
(*
value "multi_step tre0_ex1 gstk_S8 1 20"
value "multi_step tre0_ex1 gstk_S8 2 20"
value "multi_step tre0_ex1 gstk_S8 3 20"
value "multi_step tre0_ex1 gstk_S8 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S8 3 20)
  [(x_id, (NL 1154414090619811796818182302139415280051214250812) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S8 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S8 4 20)"


(*S9 --- (x=0) \<rightarrow>* (x=162)
   x := gasprice()
*)
(*
value "multi_step tre0_ex1 gstk_S9 1 20"
value "multi_step tre0_ex1 gstk_S9 2 20"
value "multi_step tre0_ex1 gstk_S9 3 20"
value "multi_step tre0_ex1 gstk_S9 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S9 3 20)
  [(x_id, (NL 162) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S9 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S9 4 20)"


(*S10 --- (x=0) \<rightarrow>* (x=83193096625216431431754650297512140349873303674)
   x := coinbase()
*)
(*
value "multi_step tre0_ex1 gstk_S10 1 20"
value "multi_step tre0_ex1 gstk_S10 2 20"
value "multi_step tre0_ex1 gstk_S10 3 20"
value "multi_step tre0_ex1 gstk_S10 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S10 3 20)
  [(x_id, (NL 83193096625216431431754650297512140349873303674) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S10 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S10 4 20)"


(*S11 --- (x=0) \<rightarrow>* (x=16)
   x := number()
*)
(*
value "multi_step tre0_ex1 gstk_S11 1 20"
value "multi_step tre0_ex1 gstk_S11 2 20"
value "multi_step tre0_ex1 gstk_S11 3 20"
value "multi_step tre0_ex1 gstk_S11 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S11 3 20) [(x_id, (NL 16) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S11 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S11 4 20)"


(*S12 --- (x=0) \<rightarrow>* (x=10)
   x := difficulty()
*)
(*
value "multi_step tre0_ex1 gstk_S12 1 20"
value "multi_step tre0_ex1 gstk_S12 2 20"
value "multi_step tre0_ex1 gstk_S12 3 20"
value "multi_step tre0_ex1 gstk_S12 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S12 3 20)
  [(x_id, (NL 10) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S12 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S12 4 20)"


(*S13 --- (x=0) \<rightarrow>* (x=32)
   x := timestamp()
*)
(*
value "multi_step tre0_ex1 gstk_S13 1 20"
value "multi_step tre0_ex1 gstk_S13 2 20"
value "multi_step tre0_ex1 gstk_S13 3 20"
value "multi_step tre0_ex1 gstk_S13 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S13 3 20)
  [(x_id, (NL 32) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S13 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S13 4 20)"


(*S14 --- (x=0) \<rightarrow>* (x=4096)
   x := gaslimit()
*)
(*
value "multi_step tre0_ex1 gstk_S14 1 20"
value "multi_step tre0_ex1 gstk_S14 2 20"
value "multi_step tre0_ex1 gstk_S14 3 20"
value "multi_step tre0_ex1 gstk_S14 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S14 3 20)
  [(x_id, (NL 4096) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S14 4 20) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S14 4 20)"


(*S15 --- (x=0) \<rightarrow>* (x=18569430475105882587588266137607568536673111973893317399460219858819262702947)
  { 
    x := keccak256(0, 32)
  }
*)
(*
value "multi_step tre0_ex1 gstk_S15 1 20"
value "multi_step tre0_ex1 gstk_S15 2 20"
value "multi_step tre0_ex1 gstk_S15 3 20"
value "multi_step tre0_ex1 gstk_S15 4 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S15 3 20)
  [(x_id, 
    (NL 18569430475105882587588266137607568536673111973893317399460219858819262702947) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S15 4 20) (3000000-(3+30+6*1)-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S15 4 20)"


(*S16 ---
  let xx
  xx := f1(balance(0), callvalue()) 
*)
(*
value "multi_step tre0_ex1 gstk_S16 1 20"
value "multi_step tre0_ex1 gstk_S16 2 20"
value "multi_step tre0_ex1 gstk_S16 3 20"
value "multi_step tre0_ex1 gstk_S16 4 20"
value "multi_step tre0_ex1 gstk_S16 5 20"
value "multi_step tre0_ex1 gstk_S16 6 20"
value "multi_step tre0_ex1 gstk_S16 7 20"
value "multi_step tre0_ex1 gstk_S16 8 20"
value "multi_step tre0_ex1 gstk_S16 9 20"
value "multi_step tre0_ex1 gstk_S16 10 20"
value "multi_step tre0_ex1 gstk_S16 11 20"
value "multi_step tre0_ex1 gstk_S16 12 20"
value "multi_step tre0_ex1 gstk_S16 13 20"
value "multi_step tre0_ex1 gstk_S16 14 20"
value "multi_step tre0_ex1 gstk_S16 15 20"
value "multi_step tre0_ex1 gstk_S16 16 20"
value "multi_step tre0_ex1 gstk_S16 17 20"
value "multi_step tre0_ex1 gstk_S16 18 20"
value "multi_step tre0_ex1 gstk_S16 19 20"
value "multi_step tre0_ex1 gstk_S16 20 20"
value "multi_step tre0_ex1 gstk_S16 21 20"
value "multi_step tre0_ex1 gstk_S16 22 20"
value "multi_step tre0_ex1 gstk_S16 23 20"
value "multi_step tre0_ex1 gstk_S16 24 20"
value "multi_step tre0_ex1 gstk_S16 25 20"
value "multi_step tre0_ex1 gstk_S16 26 20"
value "multi_step tre0_ex1 gstk_S16 27 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S16 26 20)
  [(xx_id, (NL 131059) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S16 27 20) (3000000-478)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S16 27 20)"


(*S17 --- same code as S16, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_S17 1 20"
value "multi_step tre0_ex1 gstk_S17 2 20"
value "multi_step tre0_ex1 gstk_S17 3 20"
value "multi_step tre0_ex1 gstk_S17 4 20"
value "multi_step tre0_ex1 gstk_S17 5 20"
value "multi_step tre0_ex1 gstk_S17 6 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_S17 6 20)"


(*S18 --- same code as S16, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_S18 1 20"
value "multi_step tre0_ex1 gstk_S18 2 20"
value "multi_step tre0_ex1 gstk_S18 3 20"
value "multi_step tre0_ex1 gstk_S18 4 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_S18 4 20)"


end