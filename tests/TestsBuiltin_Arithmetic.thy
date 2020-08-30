(******
Tests for builtin functions of Yul language for arithmetic operations
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

chapter \<open>the tests of formal Yul language about arithmetic built-in function\<close>

theory "TestsBuiltin_Arithmetic" 

imports 
  Main "../Syntax" "../Typing" "../SmallStep" "../utils/Keccak" Common_defs

begin 
(*A1: (x=20) \<rightarrow>* (x=25)
      arithmetic -- x := add(x,add(3,2))
*)
(*
value "multi_step tre0_ex1 gstk_A1 1 10"
value "multi_step tre0_ex1 gstk_A1 2 10"
value "multi_step tre0_ex1 gstk_A1 3 10"
value "multi_step tre0_ex1 gstk_A1 4 10"
value "multi_step tre0_ex1 gstk_A1 5 10"
value "multi_step tre0_ex1 gstk_A1 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A1 6 10) [(x_id, (NL 25) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A1 6 10) (3000000-3-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A1 6 10)"


(*A2 --- (x=20) \<rightarrow>* (x=19)
       x := sub(x,sub(3,2)) *)
(*
value "multi_step tre0_ex1 gstk_A2 1 10"
value "multi_step tre0_ex1 gstk_A2 2 10"
value "multi_step tre0_ex1 gstk_A2 3 10"
value "multi_step tre0_ex1 gstk_A2 4 10"
value "multi_step tre0_ex1 gstk_A2 5 10"
value "multi_step tre0_ex1 gstk_A2 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A2 6 10) [(x_id, (NL 19) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A2 6 10) (3000000-3-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A2 6 10)"


(*A3 ---  (x=20) \<rightarrow>* (x=120)
      mul(x,mul(3,2))*)
(*
value "multi_step tre0_ex1 gstk_A3 1 10"
value "multi_step tre0_ex1 gstk_A3 2 10"
value "multi_step tre0_ex1 gstk_A3 3 10"
value "multi_step tre0_ex1 gstk_A3 4 10"
value "multi_step tre0_ex1 gstk_A3 5 10"
value "multi_step tre0_ex1 gstk_A3 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A3 6 10) [(x_id, (NL 120) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A3 6 10) (3000000-3-5-5-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A3 6 10)"


(*A4 : (x=20) \<rightarrow>* (aa=-10) 
      arithmetic --- aa := sdiv(x,-2) *)
(*
value "multi_step tre0_ex1 gstk_A4 1 10"
value "multi_step tre0_ex1 gstk_A4 2 10"
value "multi_step tre0_ex1 gstk_A4 3 10"
value "multi_step tre0_ex1 gstk_A4 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A4 4 10) [(aa_id, ((NL (-10)):L S256))]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A4 4 10) (3000000-3-5-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A4 4 10)"


(*A5 : (x=20) \<rightarrow>* (x=20)
      arithmetic --- x := div(x,div(2,2)) *)
(*
value "multi_step tre0_ex1 gstk_A5 1 10"
value "multi_step tre0_ex1 gstk_A5 2 10"
value "multi_step tre0_ex1 gstk_A5 3 10"
value "multi_step tre0_ex1 gstk_A5 4 10"
value "multi_step tre0_ex1 gstk_A5 5 10"
value "multi_step tre0_ex1 gstk_A5 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A5 6 10) [(x_id, (NL 20) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A5 6 10) (3000000-3-5-5-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A5 6 10)"


(*A6 ---  (x=20) \<rightarrow>* (x=2) 
      x := mod(x,3)*)
(*
value "multi_step tre0_ex1 gstk_A6 1 10"
value "multi_step tre0_ex1 gstk_A6 2 10"
value "multi_step tre0_ex1 gstk_A6 3 10"
value "multi_step tre0_ex1 gstk_A6 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A6 4 10) [(x_id, (NL 2) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A6 4 10) (3000000-3-5-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A6 4 10)"


(*A7 ---  (x=20) \<rightarrow>* (s=-1)
      s := smod(x,-3)*)
(*
value "multi_step tre0_ex1 gstk_A7 1 10"
value "multi_step tre0_ex1 gstk_A7 2 10"
value "multi_step tre0_ex1 gstk_A7 3 10"
value "multi_step tre0_ex1 gstk_A7 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A7 4 10) [(s_id, (NL (-1)):L S256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A7 4 10) (3000000-3-5-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A7 4 10)"


(*A8 --- (x=20) \<rightarrow>* (x=400)
    x := exp(x,2) *)
(*
value "multi_step tre0_ex1 gstk_A8 1 10"
value "multi_step tre0_ex1 gstk_A8 2 10"
value "multi_step tre0_ex1 gstk_A8 3 10"  
value "multi_step tre0_ex1 gstk_A8 4 10"
value "multi_step tre0_ex1 gstk_A8 5 10"
value "multi_step tre0_ex1 gstk_A8 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A8 6 10) [(x_id, (NL 400) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A8 6 10) (3000000-3-20-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A8 6 10)"


(*A9 --- (x=20, a=0) \<rightarrow>* (x=2)
      addmod -- x := addmod(x,a,3) *)
(*
value "multi_step tre0_ex1 gstk_A9 1 10"
value "multi_step tre0_ex1 gstk_A9 2 10"
value "multi_step tre0_ex1 gstk_A9 3 10"
value "multi_step tre0_ex1 gstk_A9 4 10"
value "multi_step tre0_ex1 gstk_A9 5 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A9 5 10) [(x_id, (NL 2) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A9 5 10) (3000000-3-3-8-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A9 5 10)"


(*A10 --- (x=20, a=0) \<rightarrow>* (x=0)
      x := mulmod(x,a,3)*)
(*
value "multi_step tre0_ex1 gstk_A10 1 10"
value "multi_step tre0_ex1 gstk_A10 2 10"
value "multi_step tre0_ex1 gstk_A10 3 10"
value "multi_step tre0_ex1 gstk_A10 4 10"
value "multi_step tre0_ex1 gstk_A10 5 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A10 5 10) [(x_id, (NL 0) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A10 5 10) (3000000-3-3-8-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A10 5 10)"


(*A11 :   (x=0) \<rightarrow>* (h=false)
    comparison -- h := gt(x,sub(6,4))*)
(* 
value "multi_step tre0_ex1 gstk_A11 1 10"   
value "multi_step tre0_ex1 gstk_A11 2 10"
value "multi_step tre0_ex1 gstk_A11 3 10"
value "multi_step tre0_ex1 gstk_A11 4 10"
value "multi_step tre0_ex1 gstk_A11 5 10"
value "multi_step tre0_ex1 gstk_A11 6 10" 
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A11 6 10) [(h_id, FL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A11 6 10) (3000000-3-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A11 6 10)"


(*A12 --- (s=0) \<rightarrow>* (h=true)
      h := sgt(s,-2*)
(*
value "multi_step tre0_ex1 gstk_A12 1 10"
value "multi_step tre0_ex1 gstk_A12 2 10"
value "multi_step tre0_ex1 gstk_A12 3 10"
value "multi_step tre0_ex1 gstk_A12 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A12 4 10) [(h_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A12 4 10) (3000000-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A12 4 10)"


(*A13 --- (a=0) \<rightarrow>* (h=true)
       h := lt(a,3)*)
(*
value "multi_step tre0_ex1 gstk_A13 1 10"
value "multi_step tre0_ex1 gstk_A13 2 10"
value "multi_step tre0_ex1 gstk_A13 3 10"
value "multi_step tre0_ex1 gstk_A13 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A13 4 10) [(h_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A13 4 10) (3000000-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A13 4 10)"


(*A14 --- (a=0) \<rightarrow>* (h=false)
       h := slt(a,-3)*)
(*
value "multi_step tre0_ex1 gstk_A14 1 10"
value "multi_step tre0_ex1 gstk_A14 2 10"
value "multi_step tre0_ex1 gstk_A14 3 10"
value "multi_step tre0_ex1 gstk_A14 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A14 4 10) [(h_id, FL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A14 4 10) (3000000-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A14 4 10)"


(*A15 --- (a=0) \<rightarrow>* (h=true)
       h := eq(a,mul(0,3))*)
(*
value "multi_step tre0_ex1 gstk_A15 1 10"
value "multi_step tre0_ex1 gstk_A15 2 10"
value "multi_step tre0_ex1 gstk_A15 3 10"
value "multi_step tre0_ex1 gstk_A15 4 10"
value "multi_step tre0_ex1 gstk_A15 5 10"
value "multi_step tre0_ex1 gstk_A15 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A15 6 10) [(h_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A15 6 10) (3000000-3-5-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A15 6 10)"


(*A16 --- (x=20) \<rightarrow>* (x=4)
       x := and(x,add(3,4))*)
(*
value "multi_step tre0_ex1 gstk_A16 1 10"    
value "multi_step tre0_ex1 gstk_A16 2 10"
value "multi_step tre0_ex1 gstk_A16 3 10"
value "multi_step tre0_ex1 gstk_A16 4 10"
value "multi_step tre0_ex1 gstk_A16 5 10"
value "multi_step tre0_ex1 gstk_A16 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A16 6 10) [(x_id, (NL 4) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A16 6 10) (3000000-3-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A16 6 10)"


(*A17 --- (a=6) \<rightarrow>* (x=115792089237316195423570985008687907853269984665640564039457584007913129639929)
       x := not(a)*)
(*
value "multi_step tre0_ex1 gstk_A17 1 10"
value "multi_step tre0_ex1 gstk_A17 2 10"
value "multi_step tre0_ex1 gstk_A17 3 10"
value "multi_step tre0_ex1 gstk_A17 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A17 4 10) 
        [(x_id, 
          (NL 115792089237316195423570985008687907853269984665640564039457584007913129639929) 
            :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A17 4 10) (3000000-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A17 4 10)"


(*A18 --- (x=0) \<rightarrow>* (h=true)
      iszero -- h := iszero(x) *)
(*
value "multi_step tre0_ex1 gstk_A18 1 10"
value "multi_step tre0_ex1 gstk_A18 2 10"
value "multi_step tre0_ex1 gstk_A18 3 10"
value "multi_step tre0_ex1 gstk_A18 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A18 4 10) [(h_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A18 4 10) (3000000-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A18 4 10)"


(*A19 --- (a=6) \<rightarrow>* (x=192)
      x := shl(a,div(3,1))*)
(*
value "multi_step tre0_ex1 gstk_A19 1 10" 
value "multi_step tre0_ex1 gstk_A19 2 10"
value "multi_step tre0_ex1 gstk_A19 3 10"
value "multi_step tre0_ex1 gstk_A19 4 10"
value "multi_step tre0_ex1 gstk_A19 5 10"
value "multi_step tre0_ex1 gstk_A19 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A19 6 10) [(x_id, (NL 192) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A19 6 10) (3000000-3-5-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A19 6 10)"


(*A20 ---  (a=6) \<rightarrow>* (x=0)
      x := shr(a,2)*)
(*
value "multi_step tre0_ex1 gstk_A20 1 10"
value "multi_step tre0_ex1 gstk_A20 2 10"
value "multi_step tre0_ex1 gstk_A20 3 10"
value "multi_step tre0_ex1 gstk_A20 4 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A20 4 10) [(x_id, (NL 0) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A20 4 10) (3000000-3-3-5)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A20 4 10)"


(*A21 ---  x \<rightarrow> (x=115792089237316195423570985008687907853269984665640564039457584007913129639932)
      x := sar(2,-16)*)
(*
value "multi_step tre0_ex1 gstk_A21 1 10" 
value "multi_step tre0_ex1 gstk_A21 2 10"
value "multi_step tre0_ex1 gstk_A21 3 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A21 3 10) 
[(x_id, (NL 115792089237316195423570985008687907853269984665640564039457584007913129639932) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A21 3 10) (3000000-3)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A21 3 10)"


(*A22 --- x \<rightarrow> (x=4095)
      let x := or(0xfff,0xf0f)*)
(*
value "multi_step tre0_ex1 gstk_A22 1 10"
value "multi_step tre0_ex1 gstk_A22 2 10"
value "multi_step tre0_ex1 gstk_A22 3 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A22 3 10) [(x_id, (NL (4095)) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A22 3 10) (3000000-3)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A22 3 10)"


(*A23 --- x \<rightarrow> (x=240) 
      let x := xor(0xfff,0xf0f)*)
(*
value "multi_step tre0_ex1 gstk_A23 1 10"
value "multi_step tre0_ex1 gstk_A23 2 10"
value "multi_step tre0_ex1 gstk_A23 3 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A23 3 10) [(x_id, (NL (240)) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A23 3 10) (3000000-3)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A23 3 10)"


(*A24 --- (b=false) \<rightarrow>* (b=true)
  let b
  b := gt(f1(3, 9), f4(2))
*)
(*
value "multi_step tre0_ex1 gstk_A24 1 20"
value "multi_step tre0_ex1 gstk_A24 2 20"
value "multi_step tre0_ex1 gstk_A24 3 20"
value "multi_step tre0_ex1 gstk_A24 4 20"
value "multi_step tre0_ex1 gstk_A24 5 20"
value "multi_step tre0_ex1 gstk_A24 6 20"
value "multi_step tre0_ex1 gstk_A24 7 20"
value "multi_step tre0_ex1 gstk_A24 8 20"
value "multi_step tre0_ex1 gstk_A24 9 20"
value "multi_step tre0_ex1 gstk_A24 10 20"
value "multi_step tre0_ex1 gstk_A24 11 20"
value "multi_step tre0_ex1 gstk_A24 12 20"
value "multi_step tre0_ex1 gstk_A24 13 20"
value "multi_step tre0_ex1 gstk_A24 14 20"
value "multi_step tre0_ex1 gstk_A24 15 20"
value "multi_step tre0_ex1 gstk_A24 16 20"
value "multi_step tre0_ex1 gstk_A24 17 20"
value "multi_step tre0_ex1 gstk_A24 18 20"
value "multi_step tre0_ex1 gstk_A24 19 20"
value "multi_step tre0_ex1 gstk_A24 20 20"
value "multi_step tre0_ex1 gstk_A24 21 20"
value "multi_step tre0_ex1 gstk_A24 22 20"
value "multi_step tre0_ex1 gstk_A24 23 20"
value "multi_step tre0_ex1 gstk_A24 24 20"
value "multi_step tre0_ex1 gstk_A24 25 20"
value "multi_step tre0_ex1 gstk_A24 26 20"
value "multi_step tre0_ex1 gstk_A24 27 20"
value "multi_step tre0_ex1 gstk_A24 28 20"
value "multi_step tre0_ex1 gstk_A24 29 20"
value "multi_step tre0_ex1 gstk_A24 30 20"
value "multi_step tre0_ex1 gstk_A24 31 20"
value "multi_step tre0_ex1 gstk_A24 32 20"
value "multi_step tre0_ex1 gstk_A24 33 20"
value "multi_step tre0_ex1 gstk_A24 34 20"
value "multi_step tre0_ex1 gstk_A24 35 20"
value "multi_step tre0_ex1 gstk_A24 36 20"
value "multi_step tre0_ex1 gstk_A24 37 20"
value "multi_step tre0_ex1 gstk_A24 38 20"
value "multi_step tre0_ex1 gstk_A24 39 20"
value "multi_step tre0_ex1 gstk_A24 40 20"
value "multi_step tre0_ex1 gstk_A24 41 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_A24 40 20) [(b_id, TL :L Bool)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_A24 41 20) (3000000-148)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_A24 41 20)"


(*A25 --- same code as A24, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_A25 1 20"
value "multi_step tre0_ex1 gstk_A25 2 20"
value "multi_step tre0_ex1 gstk_A25 3 20"
value "multi_step tre0_ex1 gstk_A25 4 20"
value "multi_step tre0_ex1 gstk_A25 5 20"
value "multi_step tre0_ex1 gstk_A25 6 20"
value "multi_step tre0_ex1 gstk_A25 7 20"
value "multi_step tre0_ex1 gstk_A25 8 20"
value "multi_step tre0_ex1 gstk_A25 9 20"
value "multi_step tre0_ex1 gstk_A25 10 20"
value "multi_step tre0_ex1 gstk_A25 11 20"
value "multi_step tre0_ex1 gstk_A25 12 20"
value "multi_step tre0_ex1 gstk_A25 13 20"
value "multi_step tre0_ex1 gstk_A25 14 20"
value "multi_step tre0_ex1 gstk_A25 15 20"
value "multi_step tre0_ex1 gstk_A25 16 20"
value "multi_step tre0_ex1 gstk_A25 17 20"
value "multi_step tre0_ex1 gstk_A25 18 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_A25 18 20)"


(*A26 --- same code as A24, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_A26 1 20"
value "multi_step tre0_ex1 gstk_A26 2 20"
value "multi_step tre0_ex1 gstk_A26 3 20"
value "multi_step tre0_ex1 gstk_A26 4 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_A26 4 20)"


end