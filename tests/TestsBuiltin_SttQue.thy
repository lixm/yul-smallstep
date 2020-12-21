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
value "multi_step tre0_ex1 gstk_S1 1"
value "multi_step tre0_ex1 gstk_S1 2"
value "multi_step tre0_ex1 gstk_S1 3"
value "multi_step tre0_ex1 gstk_S1 4"
value "multi_step tre0_ex1 gstk_S1 5"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S1 4) [(a1_id, (NL 65524) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S1 5) (3000000-3-400-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S1 5)"


(*S2 --- (a1=0) \<rightarrow>* (a1=1154414090619811796818182302139415280051214250812)
    {
      a1 := caller()
    }
*)
(*
value "multi_step tre0_ex1 gstk_S2 1"
value "multi_step tre0_ex1 gstk_S2 2"
value "multi_step tre0_ex1 gstk_S2 3"
value "multi_step tre0_ex1 gstk_S2 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S2 3)
  [(a1_id, (NL 1154414090619811796818182302139415280051214250812) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S2 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S2 4)"


(*S3 --- (a1=0) \<rightarrow>* (a1=65535)
    {
      a1 := callvalue()
    }
*)
(*
value "multi_step tre0_ex1 gstk_S3 1"
value "multi_step tre0_ex1 gstk_S3 2" 
value "multi_step tre0_ex1 gstk_S3 3"
value "multi_step tre0_ex1 gstk_S3 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S3 3)
  [(a1_id, (NL 65535) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S3 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S3 4)"


(*S4 --- (x=0) \<rightarrow>* (x=8198059952630154640245901447353345481032286063759317239499370173610174971904)
    x := calldataload(0x1)
*)
(*
value "multi_step tre0_ex1 gstk_S4 1"
value "multi_step tre0_ex1 gstk_S4 2"
value "multi_step tre0_ex1 gstk_S4 3"
value "multi_step tre0_ex1 gstk_S4 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S4 3)
  [(x_id, 
    (NL 8198059952630154640245901447353345481032286063759317239499370173610174971904) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S4 4) (3000000-3-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S4 4)"


(*S5 --- (x=0) \<rightarrow>* (x=78792666924179831118215123113636620175678209199)
   x := address()
*)
(*
value "multi_step tre0_ex1 gstk_S5 1"
value "multi_step tre0_ex1 gstk_S5 2"
value "multi_step tre0_ex1 gstk_S5 3"
value "multi_step tre0_ex1 gstk_S5 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S5 3)
  [(x_id, (NL 78792666924179831118215123113636620175678209199) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S5 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S5 4)"


(*S6 --- (x=0) \<rightarrow>* (x=4)
    calldatacopy(0, 54, 33)
   x := calldatasize()
*)
(*
value "multi_step tre0_ex1 gstk_S6 1"
value "multi_step tre0_ex1 gstk_S6 2"
value "multi_step tre0_ex1 gstk_S6 3"
value "multi_step tre0_ex1 gstk_S6 4"
value "multi_step tre0_ex1 gstk_S6 5"
value "multi_step tre0_ex1 gstk_S6 6"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S6 5)
  [(x_id, (NL 4) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S6 6) (3000000-18)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S6 6)"


(*S7 --- (x=0) \<rightarrow>* (x=3000000)
   x := gas()
*)
(*
value "multi_step tre0_ex1 gstk_S7 1"
value "multi_step tre0_ex1 gstk_S7 2"
value "multi_step tre0_ex1 gstk_S7 3"
value "multi_step tre0_ex1 gstk_S7 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S7 3)
  [(x_id, (NL 3000000) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S7 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S7 4)"


(*S8 --- (x=0) \<rightarrow>* (x=1154414090619811796818182302139415280051214250812)
   x := origin()
*)
(*
value "multi_step tre0_ex1 gstk_S8 1"
value "multi_step tre0_ex1 gstk_S8 2"
value "multi_step tre0_ex1 gstk_S8 3"
value "multi_step tre0_ex1 gstk_S8 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S8 3)
  [(x_id, (NL 1154414090619811796818182302139415280051214250812) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S8 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S8 4)"


(*S9 --- (x=0) \<rightarrow>* (x=162)
   x := gasprice()
*)
(*
value "multi_step tre0_ex1 gstk_S9 1"
value "multi_step tre0_ex1 gstk_S9 2"
value "multi_step tre0_ex1 gstk_S9 3"
value "multi_step tre0_ex1 gstk_S9 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S9 3)
  [(x_id, (NL 162) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S9 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S9 4)"


(*S10 --- (x=0) \<rightarrow>* (x=83193096625216431431754650297512140349873303674)
   x := coinbase()
*)
(*
value "multi_step tre0_ex1 gstk_S10 1"
value "multi_step tre0_ex1 gstk_S10 2"
value "multi_step tre0_ex1 gstk_S10 3"
value "multi_step tre0_ex1 gstk_S10 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S10 3)
  [(x_id, (NL 83193096625216431431754650297512140349873303674) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S10 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S10 4)"


(*S11 --- (x=0) \<rightarrow>* (x=16)
   x := number()
*)
(*
value "multi_step tre0_ex1 gstk_S11 1"
value "multi_step tre0_ex1 gstk_S11 2"
value "multi_step tre0_ex1 gstk_S11 3"
value "multi_step tre0_ex1 gstk_S11 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S11 3) [(x_id, (NL 16) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S11 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S11 4)"


(*S12 --- (x=0) \<rightarrow>* (x=10)
   x := difficulty()
*)
(*
value "multi_step tre0_ex1 gstk_S12 1"
value "multi_step tre0_ex1 gstk_S12 2"
value "multi_step tre0_ex1 gstk_S12 3"
value "multi_step tre0_ex1 gstk_S12 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S12 3)
  [(x_id, (NL 10) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S12 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S12 4)"


(*S13 --- (x=0) \<rightarrow>* (x=32)
   x := timestamp()
*)
(*
value "multi_step tre0_ex1 gstk_S13 1"
value "multi_step tre0_ex1 gstk_S13 2"
value "multi_step tre0_ex1 gstk_S13 3"
value "multi_step tre0_ex1 gstk_S13 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S13 3)
  [(x_id, (NL 32) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S13 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S13 4)"


(*S14 --- (x=0) \<rightarrow>* (x=4096)
   x := gaslimit()
*)
(*
value "multi_step tre0_ex1 gstk_S14 1"
value "multi_step tre0_ex1 gstk_S14 2"
value "multi_step tre0_ex1 gstk_S14 3"
value "multi_step tre0_ex1 gstk_S14 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S14 3)
  [(x_id, (NL 4096) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S14 4) (3000000-2-5-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S14 4)"


(*S15 --- (x=0) \<rightarrow>* (x=18569430475105882587588266137607568536673111973893317399460219858819262702947)
  { 
    x := keccak256(0, 32)
  }
*)
(*
value "multi_step tre0_ex1 gstk_S15 1"
value "multi_step tre0_ex1 gstk_S15 2"
value "multi_step tre0_ex1 gstk_S15 3"
value "multi_step tre0_ex1 gstk_S15 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S15 3)
  [(x_id, 
    (NL 18569430475105882587588266137607568536673111973893317399460219858819262702947) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S15 4) (3000000-(3+30+6*1)-2)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S15 4)"


(*S16 ---
  let xx
  xx := f1(balance(0), callvalue()) 
*)
(*
value "multi_step tre0_ex1 gstk_S16 1"
value "multi_step tre0_ex1 gstk_S16 2"
value "multi_step tre0_ex1 gstk_S16 3"
value "multi_step tre0_ex1 gstk_S16 4"
value "multi_step tre0_ex1 gstk_S16 5"
value "multi_step tre0_ex1 gstk_S16 6"
value "multi_step tre0_ex1 gstk_S16 7"
value "multi_step tre0_ex1 gstk_S16 8"
value "multi_step tre0_ex1 gstk_S16 9"
value "multi_step tre0_ex1 gstk_S16 10"
value "multi_step tre0_ex1 gstk_S16 11"
value "multi_step tre0_ex1 gstk_S16 12"
value "multi_step tre0_ex1 gstk_S16 13"
value "multi_step tre0_ex1 gstk_S16 14"
value "multi_step tre0_ex1 gstk_S16 15"
value "multi_step tre0_ex1 gstk_S16 16"
value "multi_step tre0_ex1 gstk_S16 17"
value "multi_step tre0_ex1 gstk_S16 18"
value "multi_step tre0_ex1 gstk_S16 19"
value "multi_step tre0_ex1 gstk_S16 20"
value "multi_step tre0_ex1 gstk_S16 21"
value "multi_step tre0_ex1 gstk_S16 22"
value "multi_step tre0_ex1 gstk_S16 23"
value "multi_step tre0_ex1 gstk_S16 24"
value "multi_step tre0_ex1 gstk_S16 25"
value "multi_step tre0_ex1 gstk_S16 26"
value "multi_step tre0_ex1 gstk_S16 27"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_S16 26)
  [(xx_id, (NL 131059) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_S16 27) (3000000-478)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_S16 27)"


(*S17 --- same code as S16, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_S17 1"
value "multi_step tre0_ex1 gstk_S17 2"
value "multi_step tre0_ex1 gstk_S17 3"
value "multi_step tre0_ex1 gstk_S17 4"
value "multi_step tre0_ex1 gstk_S17 5"
value "multi_step tre0_ex1 gstk_S17 6"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_S17 6)"


(*S18 --- same code as S16, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_S18 1"
value "multi_step tre0_ex1 gstk_S18 2"
value "multi_step tre0_ex1 gstk_S18 3"
value "multi_step tre0_ex1 gstk_S18 4"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_S18 4)"


end
