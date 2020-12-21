(******
Tests for builtin functions of Yul language for logical operations
Copyright (C) 2020  Ning Han, Ximeng Li

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Library General Public
License as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Library General Public License for more details.
******)

chapter \<open>the tests of formal Yul language about logic built-in function\<close>

theory "TestsBuiltin_Logic" 

imports 
  Main "../Syntax" "../Typing" "../SmallStep" "../utils/Keccak" Common_defs
 
begin 
(*L1 ---  (b=false, a=0) \<rightarrow>* (h=true)
      h := lor(b, eq(a,mul(0,3)))*)
(*
value "multi_step tre0_ex1 gstk_L1 1"
value "multi_step tre0_ex1 gstk_L1 2"
value "multi_step tre0_ex1 gstk_L1 3"
value "multi_step tre0_ex1 gstk_L1 4"
value "multi_step tre0_ex1 gstk_L1 5"
value "multi_step tre0_ex1 gstk_L1 6"
value "multi_step tre0_ex1 gstk_L1 7"
value "multi_step tre0_ex1 gstk_L1 8"
value "multi_step tre0_ex1 gstk_L1 9"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_L1 9) [(h_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_L1 9) (3000000-3-3-5-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_L1 9)"


(*L2 --- (b=false, a=0) \<rightarrow>* (h=false)
    h := land(b, lt(a,3))*)
(*
value "multi_step tre0_ex1 gstk_L2 1"
value "multi_step tre0_ex1 gstk_L2 2"
value "multi_step tre0_ex1 gstk_L2 3"
value "multi_step tre0_ex1 gstk_L2 4"
value "multi_step tre0_ex1 gstk_L2 5"
value "multi_step tre0_ex1 gstk_L2 6"
value "multi_step tre0_ex1 gstk_L2 7"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_L2 7) [(h_id, FL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_L2 7) (3000000-3-3-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_L2 7)"


(*L3 --- (b=false, x=0) \<rightarrow>* (h=false)
       h := lxor(b,gt(x,2))*)
(*
value "multi_step tre0_ex1 gstk_L3 1"
value "multi_step tre0_ex1 gstk_L3 2"
value "multi_step tre0_ex1 gstk_L3 3"
value "multi_step tre0_ex1 gstk_L3 4"
value "multi_step tre0_ex1 gstk_L3 5"   
value "multi_step tre0_ex1 gstk_L3 6"
value "multi_step tre0_ex1 gstk_L3 7"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_L3 7) [(h_id, FL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_L3 7) (3000000-3-3-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_L3 7)"


(*L4 --- (b=false) \<rightarrow>* (h=true)
      h := lnot(b)*)
(*
value "multi_step tre0_ex1 gstk_L4 1"
value "multi_step tre0_ex1 gstk_L4 2"
value "multi_step tre0_ex1 gstk_L4 3"
value "multi_step tre0_ex1 gstk_L4 4"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_L4 4) [(h_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_L4 4) (3000000-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_L4 4)"


(*L5 --- (b=false) \<rightarrow>* (b=true)
  let b
  b := lor(f3(), b)
*)
(*
value "multi_step tre0_ex1 gstk_L5 1"
value "multi_step tre0_ex1 gstk_L5 2"
value "multi_step tre0_ex1 gstk_L5 3"
value "multi_step tre0_ex1 gstk_L5 4"
value "multi_step tre0_ex1 gstk_L5 5"
value "multi_step tre0_ex1 gstk_L5 6"
value "multi_step tre0_ex1 gstk_L5 7"
value "multi_step tre0_ex1 gstk_L5 8"
value "multi_step tre0_ex1 gstk_L5 9"
value "multi_step tre0_ex1 gstk_L5 10"
value "multi_step tre0_ex1 gstk_L5 11"
value "multi_step tre0_ex1 gstk_L5 12"
value "multi_step tre0_ex1 gstk_L5 13"
value "multi_step tre0_ex1 gstk_L5 14"
value "multi_step tre0_ex1 gstk_L5 15"
value "multi_step tre0_ex1 gstk_L5 16"
value "multi_step tre0_ex1 gstk_L5 17"
value "multi_step tre0_ex1 gstk_L5 18"
value "multi_step tre0_ex1 gstk_L5 19"
value "multi_step tre0_ex1 gstk_L5 20"
value "multi_step tre0_ex1 gstk_L5 21"
value "multi_step tre0_ex1 gstk_L5 22"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_L5 21) [(b_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_L5 22) (3000000-72)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_L5 22)"


(*L6 --- same code as L5, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_L6 1"
value "multi_step tre0_ex1 gstk_L6 2"
value "multi_step tre0_ex1 gstk_L6 3"
value "multi_step tre0_ex1 gstk_L6 4"
value "multi_step tre0_ex1 gstk_L6 5"
value "multi_step tre0_ex1 gstk_L6 6"
value "multi_step tre0_ex1 gstk_L6 7"
value "multi_step tre0_ex1 gstk_L6 8"
value "multi_step tre0_ex1 gstk_L6 9"
value "multi_step tre0_ex1 gstk_L6 10"
value "multi_step tre0_ex1 gstk_L6 11"
value "multi_step tre0_ex1 gstk_L6 12"
value "multi_step tre0_ex1 gstk_L6 13"
value "multi_step tre0_ex1 gstk_L6 14"
value "multi_step tre0_ex1 gstk_L6 15"
value "multi_step tre0_ex1 gstk_L6 16"
value "multi_step tre0_ex1 gstk_L6 17"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_L6 17)"


(*L7 --- same code as L5, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_L7 1"
value "multi_step tre0_ex1 gstk_L7 2"
value "multi_step tre0_ex1 gstk_L7 3"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_L7 3)"


(*L8 --- (b=false) \<rightarrow>* (b=true)
  let b
  b := lxor(f3(), not(f3()))
*)
(*
value "multi_step tre0_ex1 gstk_L8 1"
value "multi_step tre0_ex1 gstk_L8 2"
value "multi_step tre0_ex1 gstk_L8 3"
value "multi_step tre0_ex1 gstk_L8 4"
value "multi_step tre0_ex1 gstk_L8 5"
value "multi_step tre0_ex1 gstk_L8 6"
value "multi_step tre0_ex1 gstk_L8 7"
value "multi_step tre0_ex1 gstk_L8 8"
value "multi_step tre0_ex1 gstk_L8 9"
value "multi_step tre0_ex1 gstk_L8 10"
value "multi_step tre0_ex1 gstk_L8 11"
value "multi_step tre0_ex1 gstk_L8 12"
value "multi_step tre0_ex1 gstk_L8 13"
value "multi_step tre0_ex1 gstk_L8 14"
value "multi_step tre0_ex1 gstk_L8 15"
value "multi_step tre0_ex1 gstk_L8 16"
value "multi_step tre0_ex1 gstk_L8 17"
value "multi_step tre0_ex1 gstk_L8 18"
value "multi_step tre0_ex1 gstk_L8 19"
value "multi_step tre0_ex1 gstk_L8 20"
value "multi_step tre0_ex1 gstk_L8 21"
value "multi_step tre0_ex1 gstk_L8 22"
value "multi_step tre0_ex1 gstk_L8 23"
value "multi_step tre0_ex1 gstk_L8 24"
value "multi_step tre0_ex1 gstk_L8 25"
value "multi_step tre0_ex1 gstk_L8 26"
value "multi_step tre0_ex1 gstk_L8 27"
value "multi_step tre0_ex1 gstk_L8 28"
value "multi_step tre0_ex1 gstk_L8 29"
value "multi_step tre0_ex1 gstk_L8 30"
value "multi_step tre0_ex1 gstk_L8 31"
value "multi_step tre0_ex1 gstk_L8 32"
value "multi_step tre0_ex1 gstk_L8 33"
value "multi_step tre0_ex1 gstk_L8 34"
value "multi_step tre0_ex1 gstk_L8 35"
value "multi_step tre0_ex1 gstk_L8 36"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_L8 35) [(b_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_L8 36) (3000000-116)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_L8 36)"


(*L9 --- same code as L8, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_L9 1"
value "multi_step tre0_ex1 gstk_L9 2"
value "multi_step tre0_ex1 gstk_L9 3"
value "multi_step tre0_ex1 gstk_L9 4"
value "multi_step tre0_ex1 gstk_L9 5"
value "multi_step tre0_ex1 gstk_L9 6"
value "multi_step tre0_ex1 gstk_L9 7"
value "multi_step tre0_ex1 gstk_L9 8"
value "multi_step tre0_ex1 gstk_L9 9"
value "multi_step tre0_ex1 gstk_L9 10"
value "multi_step tre0_ex1 gstk_L9 11"
value "multi_step tre0_ex1 gstk_L9 12"
value "multi_step tre0_ex1 gstk_L9 13"
value "multi_step tre0_ex1 gstk_L9 14"
value "multi_step tre0_ex1 gstk_L9 15"
value "multi_step tre0_ex1 gstk_L9 16"
value "multi_step tre0_ex1 gstk_L9 17"
value "multi_step tre0_ex1 gstk_L9 18"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_L9 18)"


(*L10 --- same code as L8, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_L10 1"
value "multi_step tre0_ex1 gstk_L10 2"
value "multi_step tre0_ex1 gstk_L10 3"
value "multi_step tre0_ex1 gstk_L10 4"
value "multi_step tre0_ex1 gstk_L10 5"
value "multi_step tre0_ex1 gstk_L10 6"
value "multi_step tre0_ex1 gstk_L10 7"
value "multi_step tre0_ex1 gstk_L10 8"
value "multi_step tre0_ex1 gstk_L10 9"
value "multi_step tre0_ex1 gstk_L10 10"
value "multi_step tre0_ex1 gstk_L10 11"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_L10 11)"


end
