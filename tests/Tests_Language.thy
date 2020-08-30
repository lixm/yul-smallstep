(******
Tests for features of Yul language
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

chapter \<open>the tests of formal Yul language \<close>

theory "Tests_Language" 
 
imports 
  Main "../Syntax" "../Typing" "../SmallStep" "../utils/Keccak" Common_defs

begin 

\<comment> \<open>Expression Statement\<close>
(*E1 --- assign : u256 x=99  *)
(*
value "multi_step tre0_ex1 gstk_E1 1 20" 
value "multi_step tre0_ex1 gstk_E1 2 20" 
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E1 2 20) [(x_id, ((NL 99) :L U256))]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E1 2 20) (3000000-8)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E1 2 20)"


(* 
 E2 ---  if true {}     
*)
(*
value "multi_step tre0_ex1 gstk_E2 1 20" 
value "multi_step tre0_ex1 gstk_E2 2 20" 
value "multi_step tre0_ex1 gstk_E2 3 20" 
value "multi_step tre0_ex1 gstk_E2 4 20" 
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E2 4 20) [(x_id, ((NL 0) :L U256))]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E2 4 20) (3000000-17)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E2 4 20)"

(* (x=0) if false {x := 99}*)
(*
value "multi_step tre0_ex1 gstk_E2_false 1 10"
value "multi_step tre0_ex1 gstk_E2_false 2 10"
value "multi_step tre0_ex1 gstk_E2_false 3 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E2_false 3 10) [(x_id, ((NL 0) :L U256))]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E2_false 3 10) (3000000-17)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E2_false 3 20)"


(*
  E3 ---  (a=0,x=20)
           if lt(a,3) {
            if gt(x,0) {x := 99}
          }
*)
(*
value "multi_step tre0_ex1 gstk_E3 1 20"
value "multi_step tre0_ex1 gstk_E3 2 20"
value "multi_step tre0_ex1 gstk_E3 3 20"
value "multi_step tre0_ex1 gstk_E3 4 20"
value "multi_step tre0_ex1 gstk_E3 5 20"
value "multi_step tre0_ex1 gstk_E3 6 20"
value "multi_step tre0_ex1 gstk_E3 7 20"
value "multi_step tre0_ex1 gstk_E3 8 20"
value "multi_step tre0_ex1 gstk_E3 9 20"
value "multi_step tre0_ex1 gstk_E3 10 20"
value "multi_step tre0_ex1 gstk_E3 11 20"
value "multi_step tre0_ex1 gstk_E3 12 20"
value "multi_step tre0_ex1 gstk_E3 13 20" 
value "multi_step tre0_ex1 gstk_E3 14 20"
value "multi_step tre0_ex1 gstk_E3 15 20"
*)

value "check_var_val_stp 
        (multi_step tre0_ex1 gstk_E3 15 20) [(x_id, ((NL 99):LU256)), (a_id, ((NL 0):LU256))]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E3 15 20) (3000000-51)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E3 15 20)"


(*E4 --- (x=20, a=0)
     for {a := 1} gt(x, a) { a := 21 }
             {x := 10}              
            
*)
(*
value "multi_step tre0_ex1 gstk_E4 1 20"
value "multi_step tre0_ex1 gstk_E4 2 20"
value "multi_step tre0_ex1 gstk_E4 3 20"
value "multi_step tre0_ex1 gstk_E4 4 20"
value "multi_step tre0_ex1 gstk_E4 5 20"
value "multi_step tre0_ex1 gstk_E4 6 20"
value "multi_step tre0_ex1 gstk_E4 7 20"
value "multi_step tre0_ex1 gstk_E4 8 20"
value "multi_step tre0_ex1 gstk_E4 9 20"
value "multi_step tre0_ex1 gstk_E4 10 20"
value "multi_step tre0_ex1 gstk_E4 11 20"
value "multi_step tre0_ex1 gstk_E4 12 20"
value "multi_step tre0_ex1 gstk_E4 13 20"
value "multi_step tre0_ex1 gstk_E4 14 20"
value "multi_step tre0_ex1 gstk_E4 15 20"
value "multi_step tre0_ex1 gstk_E4 16 20"
value "multi_step tre0_ex1 gstk_E4 17 20"
value "multi_step tre0_ex1 gstk_E4 18 20"
value "multi_step tre0_ex1 gstk_E4 19 20"
value "multi_step tre0_ex1 gstk_E4 20 20"
value "multi_step tre0_ex1 gstk_E4 21 20"
value "multi_step tre0_ex1 gstk_E4 22 20"
value "multi_step tre0_ex1 gstk_E4 23 20"
*)

value "check_var_val_stp 
        (multi_step tre0_ex1 gstk_E4 23 20) [(x_id, ((NL 10) :L U256)), (a_id, ((NL 21) :L U256))]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E4 23 20) (3000000-79)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E4 23 20)"


(*E5 --- (x=0)  switch x   
           case 0 {r := add(x,10)}
           case 1 {x := 99}
           default{
                r := 1
            } 
*)
(*
value "multi_step tre0_ex1 gstk_E5 1 20"
value "multi_step tre0_ex1 gstk_E5 2 20"
value "multi_step tre0_ex1 gstk_E5 3 20"
value "multi_step tre0_ex1 gstk_E5 4 20"
value "multi_step tre0_ex1 gstk_E5 5 20"
value "multi_step tre0_ex1 gstk_E5 6 20"
value "multi_step tre0_ex1 gstk_E5 7 20"
value "multi_step tre0_ex1 gstk_E5 8 20"
value "multi_step tre0_ex1 gstk_E5 9 20"
value "multi_step tre0_ex1 gstk_E5 10 20"
value "multi_step tre0_ex1 gstk_E5 11 20"
value "multi_step tre0_ex1 gstk_E5 12 20"
*)

value "check_var_val_stp 
        (multi_step tre0_ex1 gstk_E5 12 20) [(x_id, ((NL 0) :L U256)), (r_id, ((NL 10) :L U256))]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E5 12 20) (3000000-51)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E5 12 20)"


(*E6  --- (x=0) id: x *)
value "check_var_val_stp (step tre0_ex1 gstk_E6 10) [(x_id, ((NL 0) :L U256))]" 

value "check_gs_gas_stp (step tre0_ex1 gstk_E6 10) (3000000-3)"

value "\<not> check_gstk_exc_stp (step tre0_ex1 gstk_E6 10)"


(*E7--- VarDecl: {let z, r} *)
value "check_var_val_stp 
        (multi_step tre0_ex1 gstk_E7 1 10) [(z_id, ((NL 0) :L U256)), (r_id, ((NL 0) :L U256))]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E7 1 10) (3000000-6)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E7 1 10)"


(*E8--- EFunDef and EFunCall:
   {  let r,b := f()
      f() \<rightarrow> a,x {
        a := add(1,2)
        x := add(2,2)
      }
   }
*)
(*
value "multi_step tre0_ex1 gstk_E8 1 10"
value "multi_step tre0_ex1 gstk_E8 2 10"
value "multi_step tre0_ex1 gstk_E8 3 10"
value "multi_step tre0_ex1 gstk_E8 4 10"
value "multi_step tre0_ex1 gstk_E8 5 10"
value "multi_step tre0_ex1 gstk_E8 6 10"
value "multi_step tre0_ex1 gstk_E8 7 10"
value "multi_step tre0_ex1 gstk_E8 8 10"
value "multi_step tre0_ex1 gstk_E8 9 10"
value "multi_step tre0_ex1 gstk_E8 10 10"
value "multi_step tre0_ex1 gstk_E8 11 10"
value "multi_step tre0_ex1 gstk_E8 12 10"
value "multi_step tre0_ex1 gstk_E8 13 10"
value "multi_step tre0_ex1 gstk_E8 14 10"
value "multi_step tre0_ex1 gstk_E8 15 10"
value "multi_step tre0_ex1 gstk_E8 16 10"
value "multi_step tre0_ex1 gstk_E8 17 10"
value "multi_step tre0_ex1 gstk_E8 18 10" 
value "multi_step tre0_ex1 gstk_E8 19 10"
value "multi_step tre0_ex1 gstk_E8 20 10"
value "multi_step tre0_ex1 gstk_E8 21 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E8 20 10) 
          [(r_id, (NL 3) :L U256), (b_id, (NL 4) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E8 21 10) (3000000-68)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E8 21 10)"


(*E9 --- EFunDef and EFunCall:
        let a := g(1)
        function g(x) -> y {
           y := add(x, 4)
        }
*)
(*
value "multi_step tre0_ex1 gstk_E9 1 20"
value "multi_step tre0_ex1 gstk_E9 2 20"
value "multi_step tre0_ex1 gstk_E9 3 20"
value "multi_step tre0_ex1 gstk_E9 4 20"
value "multi_step tre0_ex1 gstk_E9 5 20"
value "multi_step tre0_ex1 gstk_E9 6 20"
value "multi_step tre0_ex1 gstk_E9 7 20"
value "multi_step tre0_ex1 gstk_E9 8 20"
value "multi_step tre0_ex1 gstk_E9 9 20"
value "multi_step tre0_ex1 gstk_E9 10 20"
value "multi_step tre0_ex1 gstk_E9 11 20"
value "multi_step tre0_ex1 gstk_E9 12 20"
value "multi_step tre0_ex1 gstk_E9 13 20"
value "multi_step tre0_ex1 gstk_E9 14 20"
value "multi_step tre0_ex1 gstk_E9 15 20"
value "multi_step tre0_ex1 gstk_E9 16 20"
value "multi_step tre0_ex1 gstk_E9 17 20"
value "multi_step tre0_ex1 gstk_E9 18 20"
value "multi_step tre0_ex1 gstk_E9 19 20"
value "multi_step tre0_ex1 gstk_E9 20 20"
value "multi_step tre0_ex1 gstk_E9 21 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E9 20 20)
  [(a_id, (NL 5) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E9 21 20) (3000000-71)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E9 20 20)"


(*E10 --- EFunDef and EFunCall:
{
	   let xx := 1
     let a1 := f1(1,f1(2,3))
     xx := f2(2,3)
     
     function f1(b,c) -> y {                           
        y := add(b, c)
      }
      
  function f2(b,c) -> y {                           
    y := mul(b, c)
}
*)
(*
value "multi_step tre0_ex1 gstk_E10 1 20"
value "multi_step tre0_ex1 gstk_E10 2 20"
value "multi_step tre0_ex1 gstk_E10 3 20"
value "multi_step tre0_ex1 gstk_E10 4 20"
value "multi_step tre0_ex1 gstk_E10 5 20"
value "multi_step tre0_ex1 gstk_E10 6 20"
value "multi_step tre0_ex1 gstk_E10 7 20"
value "multi_step tre0_ex1 gstk_E10 8 20"
value "multi_step tre0_ex1 gstk_E10 9 20"
value "multi_step tre0_ex1 gstk_E10 10 20"
value "multi_step tre0_ex1 gstk_E10 11 20"
value "multi_step tre0_ex1 gstk_E10 12 20"
value "multi_step tre0_ex1 gstk_E10 13 20"
value "multi_step tre0_ex1 gstk_E10 14 20"
value "multi_step tre0_ex1 gstk_E10 15 20"
value "multi_step tre0_ex1 gstk_E10 16 20"
value "multi_step tre0_ex1 gstk_E10 17 20"
value "multi_step tre0_ex1 gstk_E10 18 20"
value "multi_step tre0_ex1 gstk_E10 19 20"
value "multi_step tre0_ex1 gstk_E10 20 20"
value "multi_step tre0_ex1 gstk_E10 21 20"
value "multi_step tre0_ex1 gstk_E10 22 20"
value "multi_step tre0_ex1 gstk_E10 23 20"
value "multi_step tre0_ex1 gstk_E10 24 20"
value "multi_step tre0_ex1 gstk_E10 25 20"
value "multi_step tre0_ex1 gstk_E10 26 20"
value "multi_step tre0_ex1 gstk_E10 27 20"
value "multi_step tre0_ex1 gstk_E10 28 20"
value "multi_step tre0_ex1 gstk_E10 29 20"
value "multi_step tre0_ex1 gstk_E10 30 20" 
value "multi_step tre0_ex1 gstk_E10 31 20"
value "multi_step tre0_ex1 gstk_E10 32 20"
value "multi_step tre0_ex1 gstk_E10 33 20"
value "multi_step tre0_ex1 gstk_E10 34 20"
value "multi_step tre0_ex1 gstk_E10 35 20"
value "multi_step tre0_ex1 gstk_E10 36 20"
value "multi_step tre0_ex1 gstk_E10 37 20"
value "multi_step tre0_ex1 gstk_E10 38 20"
value "multi_step tre0_ex1 gstk_E10 39 20"
value "multi_step tre0_ex1 gstk_E10 40 20"
value "multi_step tre0_ex1 gstk_E10 41 20" 
value "multi_step tre0_ex1 gstk_E10 42 20"
value "multi_step tre0_ex1 gstk_E10 43 20"
value "multi_step tre0_ex1 gstk_E10 44 20"
value "multi_step tre0_ex1 gstk_E10 45 20"
value "multi_step tre0_ex1 gstk_E10 46 20"
value "multi_step tre0_ex1 gstk_E10 47 20"
value "multi_step tre0_ex1 gstk_E10 48 20"
value "multi_step tre0_ex1 gstk_E10 49 20"
value "multi_step tre0_ex1 gstk_E10 50 20" 
value "multi_step tre0_ex1 gstk_E10 51 20"
value "multi_step tre0_ex1 gstk_E10 52 20"
value "multi_step tre0_ex1 gstk_E10 53 20"
value "multi_step tre0_ex1 gstk_E10 54 20"
value "multi_step tre0_ex1 gstk_E10 55 20"
value "multi_step tre0_ex1 gstk_E10 56 20"
value "multi_step tre0_ex1 gstk_E10 57 20"
value "multi_step tre0_ex1 gstk_E10 58 20"
value "multi_step tre0_ex1 gstk_E10 59 20"
value "multi_step tre0_ex1 gstk_E10 60 20"
value "multi_step tre0_ex1 gstk_E10 61 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E10 60 20)
  [(xx_id, (NL 6) :L U256), (a1_id, (NL 6) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E10 61 20) (3000000-194)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E10 61 20)"


(*E11
  function f3() -> h {                           
    h := lt(1, 2)
  }
  
  if f3() then { x := 1 }
*)
(*
value "multi_step tre0_ex1 gstk_E11 1 20" 
value "multi_step tre0_ex1 gstk_E11 2 20" 
value "multi_step tre0_ex1 gstk_E11 3 20" 
value "multi_step tre0_ex1 gstk_E11 4 20" 
value "multi_step tre0_ex1 gstk_E11 5 20" 
value "multi_step tre0_ex1 gstk_E11 6 20"  
value "multi_step tre0_ex1 gstk_E11 7 20" 
value "multi_step tre0_ex1 gstk_E11 8 20" 
value "multi_step tre0_ex1 gstk_E11 9 20" 
value "multi_step tre0_ex1 gstk_E11 10 20" 
value "multi_step tre0_ex1 gstk_E11 11 20" 
value "multi_step tre0_ex1 gstk_E11 12 20" 
value "multi_step tre0_ex1 gstk_E11 13 20" 
value "multi_step tre0_ex1 gstk_E11 14 20" 
value "multi_step tre0_ex1 gstk_E11 15 20" 
value "multi_step tre0_ex1 gstk_E11 16 20" 
value "multi_step tre0_ex1 gstk_E11 17 20" 
value "multi_step tre0_ex1 gstk_E11 18 20" 
value "multi_step tre0_ex1 gstk_E11 19 20" 
value "multi_step tre0_ex1 gstk_E11 20 20" 
value "multi_step tre0_ex1 gstk_E11 21 20" 
value "multi_step tre0_ex1 gstk_E11 22 20" 
value "multi_step tre0_ex1 gstk_E11 23 20" 
value "multi_step tre0_ex1 gstk_E11 24 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E11 23 20) [(x_id, (NL 1) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E11 24 20) (3000000-86)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E11 24 20)"


(*E12 --- same code as E11, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E12 1 20" 
value "multi_step tre0_ex1 gstk_E12 2 20" 
value "multi_step tre0_ex1 gstk_E12 3 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E12 3 20)"


(*E13 --- same code as E11, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_E13 1 20" 
value "multi_step tre0_ex1 gstk_E13 2 20" 
value "multi_step tre0_ex1 gstk_E13 3 20" 
value "multi_step tre0_ex1 gstk_E13 4 20" 
value "multi_step tre0_ex1 gstk_E13 5 20" 
value "multi_step tre0_ex1 gstk_E13 6 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E13 6 20)"


(*E14 ---(r=0, x=20) \<rightarrow>* (r=400)
  {   
      let r
      switch x
      case 0 {r := and(x,4)}
      default
      {
          r := f4(x)
      }
      
      function f4(a) -> y{
          y := exp(a,2)
  }
*)
(*
value "multi_step tre0_ex1 gstk_E14 1 20"
value "multi_step tre0_ex1 gstk_E14 2 20"
value "multi_step tre0_ex1 gstk_E14 3 20"
value "multi_step tre0_ex1 gstk_E14 4 20"
value "multi_step tre0_ex1 gstk_E14 5 20"
value "multi_step tre0_ex1 gstk_E14 6 20"
value "multi_step tre0_ex1 gstk_E14 7 20"
value "multi_step tre0_ex1 gstk_E14 8 20"
value "multi_step tre0_ex1 gstk_E14 9 20"
value "multi_step tre0_ex1 gstk_E14 10 20"
value "multi_step tre0_ex1 gstk_E14 11 20"
value "multi_step tre0_ex1 gstk_E14 12 20"
value "multi_step tre0_ex1 gstk_E14 13 20"
value "multi_step tre0_ex1 gstk_E14 14 20"
value "multi_step tre0_ex1 gstk_E14 15 20"
value "multi_step tre0_ex1 gstk_E14 16 20"
value "multi_step tre0_ex1 gstk_E14 17 20"
value "multi_step tre0_ex1 gstk_E14 18 20"
value "multi_step tre0_ex1 gstk_E14 19 20"
value "multi_step tre0_ex1 gstk_E14 20 20"
value "multi_step tre0_ex1 gstk_E14 21 20"
value "multi_step tre0_ex1 gstk_E14 22 20"
value "multi_step tre0_ex1 gstk_E14 23 20"
value "multi_step tre0_ex1 gstk_E14 24 20"
value "multi_step tre0_ex1 gstk_E14 25 20"
value "multi_step tre0_ex1 gstk_E14 26 20"
value "multi_step tre0_ex1 gstk_E14 27 20"
value "multi_step tre0_ex1 gstk_E14 28 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E14 27 20) [(r_id, (NL 400) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E14 28 20) (3000000-129)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E14 28 20)"


(*E15 --- same code as E14, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E15 1 20" 
value "multi_step tre0_ex1 gstk_E15 2 20" 
value "multi_step tre0_ex1 gstk_E15 3 20" 
value "multi_step tre0_ex1 gstk_E15 4 20" 
value "multi_step tre0_ex1 gstk_E15 5 20" 
value "multi_step tre0_ex1 gstk_E15 6 20" 
value "multi_step tre0_ex1 gstk_E15 7 20"
value "multi_step tre0_ex1 gstk_E15 8 20"
value "multi_step tre0_ex1 gstk_E15 9 20"
value "multi_step tre0_ex1 gstk_E15 10 20"
value "multi_step tre0_ex1 gstk_E15 11 20"
value "multi_step tre0_ex1 gstk_E15 12 20"
value "multi_step tre0_ex1 gstk_E15 13 20"
value "multi_step tre0_ex1 gstk_E15 14 20"
value "multi_step tre0_ex1 gstk_E15 15 20"
value "multi_step tre0_ex1 gstk_E15 16 20"
value "multi_step tre0_ex1 gstk_E15 17 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E15 17 20)"


(*E16 --- (1+3)^2 \<rightarrow>* (xx=16)
  let xx := f4(f1(1,3))
*)
(*
value "multi_step tre0_ex1 gstk_E16 1 20" 
value "multi_step tre0_ex1 gstk_E16 2 20" 
value "multi_step tre0_ex1 gstk_E16 3 20" 
value "multi_step tre0_ex1 gstk_E16 4 20" 
value "multi_step tre0_ex1 gstk_E16 5 20" 
value "multi_step tre0_ex1 gstk_E16 6 20" 
value "multi_step tre0_ex1 gstk_E16 7 20"
value "multi_step tre0_ex1 gstk_E16 8 20"
value "multi_step tre0_ex1 gstk_E16 9 20"
value "multi_step tre0_ex1 gstk_E16 10 20"
value "multi_step tre0_ex1 gstk_E16 11 20"
value "multi_step tre0_ex1 gstk_E16 12 20"
value "multi_step tre0_ex1 gstk_E16 13 20"
value "multi_step tre0_ex1 gstk_E16 14 20"
value "multi_step tre0_ex1 gstk_E16 15 20"
value "multi_step tre0_ex1 gstk_E16 16 20"
value "multi_step tre0_ex1 gstk_E16 17 20"
value "multi_step tre0_ex1 gstk_E16 18 20"
value "multi_step tre0_ex1 gstk_E16 19 20"
value "multi_step tre0_ex1 gstk_E16 20 20"
value "multi_step tre0_ex1 gstk_E16 21 20"
value "multi_step tre0_ex1 gstk_E16 22 20"
value "multi_step tre0_ex1 gstk_E16 23 20"
value "multi_step tre0_ex1 gstk_E16 24 20"
value "multi_step tre0_ex1 gstk_E16 25 20"
value "multi_step tre0_ex1 gstk_E16 26 20"
value "multi_step tre0_ex1 gstk_E16 27 20"
value "multi_step tre0_ex1 gstk_E16 28 20"
value "multi_step tre0_ex1 gstk_E16 29 20"
value "multi_step tre0_ex1 gstk_E16 30 20" 
value "multi_step tre0_ex1 gstk_E16 31 20"
value "multi_step tre0_ex1 gstk_E16 32 20"
value "multi_step tre0_ex1 gstk_E16 33 20"
value "multi_step tre0_ex1 gstk_E16 34 20"
value "multi_step tre0_ex1 gstk_E16 35 20"
value "multi_step tre0_ex1 gstk_E16 36 20"
value "multi_step tre0_ex1 gstk_E16 37 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E16 36 20) [(xx_id, (NL 16) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E16 37 20) (3000000-134)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E16 37 20)"


(*E17 --- same code as E16, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E17 1 20" 
value "multi_step tre0_ex1 gstk_E17 2 20" 
value "multi_step tre0_ex1 gstk_E17 3 20" 
value "multi_step tre0_ex1 gstk_E17 4 20" 
value "multi_step tre0_ex1 gstk_E17 5 20" 
value "multi_step tre0_ex1 gstk_E17 6 20" 
value "multi_step tre0_ex1 gstk_E17 7 20"
value "multi_step tre0_ex1 gstk_E17 8 20"
value "multi_step tre0_ex1 gstk_E17 9 20"
value "multi_step tre0_ex1 gstk_E17 10 20"
value "multi_step tre0_ex1 gstk_E17 11 20"
value "multi_step tre0_ex1 gstk_E17 12 20"
value "multi_step tre0_ex1 gstk_E17 13 20"
value "multi_step tre0_ex1 gstk_E17 14 20"
value "multi_step tre0_ex1 gstk_E17 15 20"
value "multi_step tre0_ex1 gstk_E17 16 20"
value "multi_step tre0_ex1 gstk_E17 17 20"
value "multi_step tre0_ex1 gstk_E17 18 20"
value "multi_step tre0_ex1 gstk_E17 19 20"
value "multi_step tre0_ex1 gstk_E17 20 20"
value "multi_step tre0_ex1 gstk_E17 21 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E17 21 20)"


(*E18 --- (xx=3) \<rightarrow> * (xx=6)
    let xx := 3
    xx := f2(xx, sub(3,1))
*)
(*
value "multi_step tre0_ex1 gstk_E18 1 20" 
value "multi_step tre0_ex1 gstk_E18 2 20" 
value "multi_step tre0_ex1 gstk_E18 3 20" 
value "multi_step tre0_ex1 gstk_E18 4 20" 
value "multi_step tre0_ex1 gstk_E18 5 20" 
value "multi_step tre0_ex1 gstk_E18 6 20" 
value "multi_step tre0_ex1 gstk_E18 7 20"
value "multi_step tre0_ex1 gstk_E18 8 20"
value "multi_step tre0_ex1 gstk_E18 9 20"
value "multi_step tre0_ex1 gstk_E18 10 20"
value "multi_step tre0_ex1 gstk_E18 11 20"
value "multi_step tre0_ex1 gstk_E18 12 20"
value "multi_step tre0_ex1 gstk_E18 13 20"
value "multi_step tre0_ex1 gstk_E18 14 20"
value "multi_step tre0_ex1 gstk_E18 15 20"
value "multi_step tre0_ex1 gstk_E18 16 20"
value "multi_step tre0_ex1 gstk_E18 17 20"
value "multi_step tre0_ex1 gstk_E18 18 20"
value "multi_step tre0_ex1 gstk_E18 19 20"
value "multi_step tre0_ex1 gstk_E18 20 20"
value "multi_step tre0_ex1 gstk_E18 21 20"
value "multi_step tre0_ex1 gstk_E18 22 20"
value "multi_step tre0_ex1 gstk_E18 23 20"
value "multi_step tre0_ex1 gstk_E18 24 20"
value "multi_step tre0_ex1 gstk_E18 25 20"
value "multi_step tre0_ex1 gstk_E18 26 20"
value "multi_step tre0_ex1 gstk_E18 27 20"
value "multi_step tre0_ex1 gstk_E18 28 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E18 27 20) [(xx_id, (NL 6) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E18 28 20) (3000000-87)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E18 28 20)"


(*E19 --- same code as E18, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E19 1 20" 
value "multi_step tre0_ex1 gstk_E19 2 20" 
value "multi_step tre0_ex1 gstk_E19 3 20" 
value "multi_step tre0_ex1 gstk_E19 4 20" 
value "multi_step tre0_ex1 gstk_E19 5 20" 
value "multi_step tre0_ex1 gstk_E19 6 20" 
value "multi_step tre0_ex1 gstk_E19 7 20"
value "multi_step tre0_ex1 gstk_E19 8 20"
value "multi_step tre0_ex1 gstk_E19 9 20"
value "multi_step tre0_ex1 gstk_E19 10 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E19 10 20)"


(*E20 --- (xx=3) \<rightarrow>* (xx=20)
     let xx := 3 
     if f3() {
          xx := f2(4,5)
      }
*)
(*
value "multi_step tre0_ex1 gstk_E20 1 20" 
value "multi_step tre0_ex1 gstk_E20 2 20" 
value "multi_step tre0_ex1 gstk_E20 3 20" 
value "multi_step tre0_ex1 gstk_E20 4 20" 
value "multi_step tre0_ex1 gstk_E20 5 20" 
value "multi_step tre0_ex1 gstk_E20 6 20" 
value "multi_step tre0_ex1 gstk_E20 7 20" 
value "multi_step tre0_ex1 gstk_E20 8 20" 
value "multi_step tre0_ex1 gstk_E20 9 20" 
value "multi_step tre0_ex1 gstk_E20 10 20" 
value "multi_step tre0_ex1 gstk_E20 11 20" 
value "multi_step tre0_ex1 gstk_E20 12 20" 
value "multi_step tre0_ex1 gstk_E20 13 20" 
value "multi_step tre0_ex1 gstk_E20 14 20" 
value "multi_step tre0_ex1 gstk_E20 15 20" 
value "multi_step tre0_ex1 gstk_E20 16 20" 
value "multi_step tre0_ex1 gstk_E20 17 20" 
value "multi_step tre0_ex1 gstk_E20 18 20" 
value "multi_step tre0_ex1 gstk_E20 19 20" 
value "multi_step tre0_ex1 gstk_E20 20 20" 
value "multi_step tre0_ex1 gstk_E20 21 20" 
value "multi_step tre0_ex1 gstk_E20 22 20" 
value "multi_step tre0_ex1 gstk_E20 23 20" 
value "multi_step tre0_ex1 gstk_E20 24 20"
value "multi_step tre0_ex1 gstk_E20 25 20"
value "multi_step tre0_ex1 gstk_E20 26 20"
value "multi_step tre0_ex1 gstk_E20 27 20"
value "multi_step tre0_ex1 gstk_E20 28 20"
value "multi_step tre0_ex1 gstk_E20 29 20"
value "multi_step tre0_ex1 gstk_E20 30 20"
value "multi_step tre0_ex1 gstk_E20 31 20"
value "multi_step tre0_ex1 gstk_E20 32 20"
value "multi_step tre0_ex1 gstk_E20 33 20"
value "multi_step tre0_ex1 gstk_E20 34 20"
value "multi_step tre0_ex1 gstk_E20 35 20"
value "multi_step tre0_ex1 gstk_E20 36 20"
value "multi_step tre0_ex1 gstk_E20 37 20"
value "multi_step tre0_ex1 gstk_E20 38 20"
value "multi_step tre0_ex1 gstk_E20 39 20"
value "multi_step tre0_ex1 gstk_E20 40 20"
value "multi_step tre0_ex1 gstk_E20 41 20"
value "multi_step tre0_ex1 gstk_E20 42 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E20 41 20) [(xx_id, (NL 20) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E20 42 20) (3000000-142)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E20 42 20)"


(*E21 --- same code as E20, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E21 1 20" 
value "multi_step tre0_ex1 gstk_E21 2 20" 
value "multi_step tre0_ex1 gstk_E21 3 20" 
value "multi_step tre0_ex1 gstk_E21 4 20" 
value "multi_step tre0_ex1 gstk_E21 5 20" 
value "multi_step tre0_ex1 gstk_E21 6 20" 
value "multi_step tre0_ex1 gstk_E21 7 20" 
value "multi_step tre0_ex1 gstk_E21 8 20" 
value "multi_step tre0_ex1 gstk_E21 9 20" 
value "multi_step tre0_ex1 gstk_E21 10 20" 
value "multi_step tre0_ex1 gstk_E21 11 20" 
value "multi_step tre0_ex1 gstk_E21 12 20" 
value "multi_step tre0_ex1 gstk_E21 13 20" 
value "multi_step tre0_ex1 gstk_E21 14 20" 
value "multi_step tre0_ex1 gstk_E21 15 20" 
value "multi_step tre0_ex1 gstk_E21 16 20" 
value "multi_step tre0_ex1 gstk_E21 17 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E21 17 20)"


(*E22 --- same code as E20, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_E22 1 20" 
value "multi_step tre0_ex1 gstk_E22 2 20" 
value "multi_step tre0_ex1 gstk_E22 3 20" 
value "multi_step tre0_ex1 gstk_E22 4 20" 
value "multi_step tre0_ex1 gstk_E22 5 20" 
value "multi_step tre0_ex1 gstk_E22 6 20" 
value "multi_step tre0_ex1 gstk_E22 7 20" 
value "multi_step tre0_ex1 gstk_E22 8 20"
value "multi_step tre0_ex1 gstk_E22 9 20" 
value "multi_step tre0_ex1 gstk_E22 10 20" 
value "multi_step tre0_ex1 gstk_E22 11 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E22 11 20)"


(*E23 --- (r=0) \<rightarrow>* (r=7)
   let xx := 3
   let r
   for {let k:=1} gt(xx,k) {k:=add(k,1)}
    {
        r:= add(xx, f4(k))
    }
*)
(*
value "multi_step tre0_ex1 gstk_E23 1 20" 
value "multi_step tre0_ex1 gstk_E23 2 20" 
value "multi_step tre0_ex1 gstk_E23 3 20" 
value "multi_step tre0_ex1 gstk_E23 4 20" 
value "multi_step tre0_ex1 gstk_E23 5 20" 
value "multi_step tre0_ex1 gstk_E23 6 20" 
value "multi_step tre0_ex1 gstk_E23 7 20" 
value "multi_step tre0_ex1 gstk_E23 8 20" 
value "multi_step tre0_ex1 gstk_E23 9 20" 
value "multi_step tre0_ex1 gstk_E23 10 20" 
value "multi_step tre0_ex1 gstk_E23 11 20" 
value "multi_step tre0_ex1 gstk_E23 12 20" 
value "multi_step tre0_ex1 gstk_E23 13 20" 
value "multi_step tre0_ex1 gstk_E23 14 20" 
value "multi_step tre0_ex1 gstk_E23 15 20" 
value "multi_step tre0_ex1 gstk_E23 16 20" 
value "multi_step tre0_ex1 gstk_E23 17 20" 
value "multi_step tre0_ex1 gstk_E23 18 20" 
value "multi_step tre0_ex1 gstk_E23 19 20" 
value "multi_step tre0_ex1 gstk_E23 20 20" 
value "multi_step tre0_ex1 gstk_E23 21 20" 
value "multi_step tre0_ex1 gstk_E23 22 20" 
value "multi_step tre0_ex1 gstk_E23 23 20" 
value "multi_step tre0_ex1 gstk_E23 24 20"
value "multi_step tre0_ex1 gstk_E23 25 20"
value "multi_step tre0_ex1 gstk_E23 26 20"
value "multi_step tre0_ex1 gstk_E23 27 20"
value "multi_step tre0_ex1 gstk_E23 28 20"
value "multi_step tre0_ex1 gstk_E23 29 20"
value "multi_step tre0_ex1 gstk_E23 30 20"
value "multi_step tre0_ex1 gstk_E23 31 20"
value "multi_step tre0_ex1 gstk_E23 32 20"
value "multi_step tre0_ex1 gstk_E23 33 20"
value "multi_step tre0_ex1 gstk_E23 34 20"
value "multi_step tre0_ex1 gstk_E23 35 20"
value "multi_step tre0_ex1 gstk_E23 36 20"
value "multi_step tre0_ex1 gstk_E23 37 20"
value "multi_step tre0_ex1 gstk_E23 38 20"
value "multi_step tre0_ex1 gstk_E23 39 20"
value "multi_step tre0_ex1 gstk_E23 40 20"
value "multi_step tre0_ex1 gstk_E23 41 20"
value "multi_step tre0_ex1 gstk_E23 42 20"
value "multi_step tre0_ex1 gstk_E23 43 20"
value "multi_step tre0_ex1 gstk_E23 44 20"
value "multi_step tre0_ex1 gstk_E23 45 20"
value "multi_step tre0_ex1 gstk_E23 46 20"
value "multi_step tre0_ex1 gstk_E23 47 20"
value "multi_step tre0_ex1 gstk_E23 48 20"
value "multi_step tre0_ex1 gstk_E23 49 20"
value "multi_step tre0_ex1 gstk_E23 50 20"
value "multi_step tre0_ex1 gstk_E23 51 20"
value "multi_step tre0_ex1 gstk_E23 52 20"
value "multi_step tre0_ex1 gstk_E23 53 20"
value "multi_step tre0_ex1 gstk_E23 54 20"
value "multi_step tre0_ex1 gstk_E23 55 20"
value "multi_step tre0_ex1 gstk_E23 56 20"
value "multi_step tre0_ex1 gstk_E23 57 20"
value "multi_step tre0_ex1 gstk_E23 58 20"
value "multi_step tre0_ex1 gstk_E23 59 20"
value "multi_step tre0_ex1 gstk_E23 60 20"
value "multi_step tre0_ex1 gstk_E23 61 20"
value "multi_step tre0_ex1 gstk_E23 62 20"
value "multi_step tre0_ex1 gstk_E23 63 20"
value "multi_step tre0_ex1 gstk_E23 64 20"
value "multi_step tre0_ex1 gstk_E23 65 20"
value "multi_step tre0_ex1 gstk_E23 66 20"
value "multi_step tre0_ex1 gstk_E23 67 20"
value "multi_step tre0_ex1 gstk_E23 68 20"
value "multi_step tre0_ex1 gstk_E23 69 20"
value "multi_step tre0_ex1 gstk_E23 70 20"
value "multi_step tre0_ex1 gstk_E23 71 20"
value "multi_step tre0_ex1 gstk_E23 72 20"
value "multi_step tre0_ex1 gstk_E23 73 20"
value "multi_step tre0_ex1 gstk_E23 74 20"
value "multi_step tre0_ex1 gstk_E23 75 20"
value "multi_step tre0_ex1 gstk_E23 76 20"
value "multi_step tre0_ex1 gstk_E23 77 20"
value "multi_step tre0_ex1 gstk_E23 78 20"
value "multi_step tre0_ex1 gstk_E23 79 20"
value "multi_step tre0_ex1 gstk_E23 80 20"
value "multi_step tre0_ex1 gstk_E23 81 20"
value "multi_step tre0_ex1 gstk_E23 82 20"
value "multi_step tre0_ex1 gstk_E23 83 20"
value "multi_step tre0_ex1 gstk_E23 84 20"
value "multi_step tre0_ex1 gstk_E23 85 20"
value "multi_step tre0_ex1 gstk_E23 86 20"
value "multi_step tre0_ex1 gstk_E23 87 20"
value "multi_step tre0_ex1 gstk_E23 88 20"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E23 87 20) [(r_id, (NL 7) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E23 88 20) (3000000-310)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E23 88 20)"


(*E24 ---same code as E23, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E24 1 20" 
value "multi_step tre0_ex1 gstk_E24 2 20" 
value "multi_step tre0_ex1 gstk_E24 3 20" 
value "multi_step tre0_ex1 gstk_E24 4 20" 
value "multi_step tre0_ex1 gstk_E24 5 20" 
value "multi_step tre0_ex1 gstk_E24 6 20" 
value "multi_step tre0_ex1 gstk_E24 7 20" 
value "multi_step tre0_ex1 gstk_E24 8 20" 
value "multi_step tre0_ex1 gstk_E24 9 20" 
value "multi_step tre0_ex1 gstk_E24 10 20" 
value "multi_step tre0_ex1 gstk_E24 11 20" 
value "multi_step tre0_ex1 gstk_E24 12 20" 
value "multi_step tre0_ex1 gstk_E24 13 20" 
value "multi_step tre0_ex1 gstk_E24 14 20" 
value "multi_step tre0_ex1 gstk_E24 15 20" 
value "multi_step tre0_ex1 gstk_E24 16 20" 
value "multi_step tre0_ex1 gstk_E24 17 20" 
value "multi_step tre0_ex1 gstk_E24 18 20" 
value "multi_step tre0_ex1 gstk_E24 19 20" 
value "multi_step tre0_ex1 gstk_E24 20 20" 
value "multi_step tre0_ex1 gstk_E24 21 20" 
value "multi_step tre0_ex1 gstk_E24 22 20" 
value "multi_step tre0_ex1 gstk_E24 23 20" 
value "multi_step tre0_ex1 gstk_E24 24 20"
value "multi_step tre0_ex1 gstk_E24 25 20"
value "multi_step tre0_ex1 gstk_E24 26 20"
value "multi_step tre0_ex1 gstk_E24 27 20"
value "multi_step tre0_ex1 gstk_E24 28 20"
value "multi_step tre0_ex1 gstk_E24 29 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E24 29 20)"


(*E25 --- same code as E23, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_E25 1 20" 
value "multi_step tre0_ex1 gstk_E25 2 20" 
value "multi_step tre0_ex1 gstk_E25 3 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E25 3 20)"


(*E26 --- (r=0) \<rightarrow>* (r=16)
    let xx,r
    switch xx
    case 0 {
        if f3() {
         mstore(xx, exp(2,4))
         r := mload(xx)
        }
    }
    default
    {
        r := f4(xx)
    }
*)
(*
value "multi_step tre0_ex1 gstk_E26 1 20" 
value "multi_step tre0_ex1 gstk_E26 2 20" 
value "multi_step tre0_ex1 gstk_E26 3 20" 
value "multi_step tre0_ex1 gstk_E26 4 20" 
value "multi_step tre0_ex1 gstk_E26 5 20" 
value "multi_step tre0_ex1 gstk_E26 6 20" 
value "multi_step tre0_ex1 gstk_E26 7 20" 
value "multi_step tre0_ex1 gstk_E26 8 20" 
value "multi_step tre0_ex1 gstk_E26 9 20" 
value "multi_step tre0_ex1 gstk_E26 10 20" 
value "multi_step tre0_ex1 gstk_E26 11 20" 
value "multi_step tre0_ex1 gstk_E26 12 20" 
value "multi_step tre0_ex1 gstk_E26 13 20" 
value "multi_step tre0_ex1 gstk_E26 14 20" 
value "multi_step tre0_ex1 gstk_E26 15 20" 
value "multi_step tre0_ex1 gstk_E26 16 20" 
value "multi_step tre0_ex1 gstk_E26 17 20" 
value "multi_step tre0_ex1 gstk_E26 18 20" 
value "multi_step tre0_ex1 gstk_E26 19 20" 
value "multi_step tre0_ex1 gstk_E26 20 20" 
value "multi_step tre0_ex1 gstk_E26 21 20" 
value "multi_step tre0_ex1 gstk_E26 22 20" 
value "multi_step tre0_ex1 gstk_E26 23 20" 
value "multi_step tre0_ex1 gstk_E26 24 20"
value "multi_step tre0_ex1 gstk_E26 25 20"
value "multi_step tre0_ex1 gstk_E26 26 20"
value "multi_step tre0_ex1 gstk_E26 27 20"
value "multi_step tre0_ex1 gstk_E26 28 20"
value "multi_step tre0_ex1 gstk_E26 29 20"
value "multi_step tre0_ex1 gstk_E26 30 20"
value "multi_step tre0_ex1 gstk_E26 31 20" 
value "multi_step tre0_ex1 gstk_E26 32 20" 
value "multi_step tre0_ex1 gstk_E26 33 20" 
value "multi_step tre0_ex1 gstk_E26 34 20" 
value "multi_step tre0_ex1 gstk_E26 35 20" 
value "multi_step tre0_ex1 gstk_E26 36 20" 
value "multi_step tre0_ex1 gstk_E26 37 20" 
value "multi_step tre0_ex1 gstk_E26 38 20" 
value "multi_step tre0_ex1 gstk_E26 39 20" 
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E26 38 20) [(r_id, (NL 16) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E26 39 20) (3000000-158)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E26 39 20)"


(*E27 --- same code as E26, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E27 1 20" 
value "multi_step tre0_ex1 gstk_E27 2 20" 
value "multi_step tre0_ex1 gstk_E27 3 20" 
value "multi_step tre0_ex1 gstk_E27 4 20" 
value "multi_step tre0_ex1 gstk_E27 5 20" 
value "multi_step tre0_ex1 gstk_E27 6 20" 
value "multi_step tre0_ex1 gstk_E27 7 20" 
value "multi_step tre0_ex1 gstk_E27 8 20" 
value "multi_step tre0_ex1 gstk_E27 9 20" 
value "multi_step tre0_ex1 gstk_E27 10 20" 
value "multi_step tre0_ex1 gstk_E27 11 20" 
value "multi_step tre0_ex1 gstk_E27 12 20" 
value "multi_step tre0_ex1 gstk_E27 13 20" 
value "multi_step tre0_ex1 gstk_E27 14 20" 
value "multi_step tre0_ex1 gstk_E27 15 20" 
value "multi_step tre0_ex1 gstk_E27 16 20" 
value "multi_step tre0_ex1 gstk_E27 17 20" 
value "multi_step tre0_ex1 gstk_E27 18 20" 
value "multi_step tre0_ex1 gstk_E27 19 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E27 19 20)"


(*E28 --- same code as E26, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_E28 1 20" 
value "multi_step tre0_ex1 gstk_E28 2 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E28 2 20)"


(*E29 --- (r=0) \<rightarrow>* (r=2)
  let xx := 1
  let r := xx
  switch xx
    case 1 {
        if f3() {
            for {let k:=0} gt(xx,k) {k:=add(k,1)}
            {
                r:= add(r, f1(k, 1))
            }
        }
    }
    default
    {
        r := 0
    }
*)
(*
value "multi_step tre0_ex1 gstk_E29 1 20" 
value "multi_step tre0_ex1 gstk_E29 2 20" 
value "multi_step tre0_ex1 gstk_E29 3 20" 
value "multi_step tre0_ex1 gstk_E29 4 20" 
value "multi_step tre0_ex1 gstk_E29 5 20" 
value "multi_step tre0_ex1 gstk_E29 6 20" 
value "multi_step tre0_ex1 gstk_E29 7 20" 
value "multi_step tre0_ex1 gstk_E29 8 20" 
value "multi_step tre0_ex1 gstk_E29 9 20" 
value "multi_step tre0_ex1 gstk_E29 10 20" 
value "multi_step tre0_ex1 gstk_E29 11 20" 
value "multi_step tre0_ex1 gstk_E29 12 20" 
value "multi_step tre0_ex1 gstk_E29 13 20" 
value "multi_step tre0_ex1 gstk_E29 14 20" 
value "multi_step tre0_ex1 gstk_E29 15 20" 
value "multi_step tre0_ex1 gstk_E29 16 20" 
value "multi_step tre0_ex1 gstk_E29 17 20" 
value "multi_step tre0_ex1 gstk_E29 18 20" 
value "multi_step tre0_ex1 gstk_E29 19 20" 
value "multi_step tre0_ex1 gstk_E29 20 20" 
value "multi_step tre0_ex1 gstk_E29 21 20" 
value "multi_step tre0_ex1 gstk_E29 22 20" 
value "multi_step tre0_ex1 gstk_E29 23 20" 
value "multi_step tre0_ex1 gstk_E29 24 20" 
value "multi_step tre0_ex1 gstk_E29 25 20" 
value "multi_step tre0_ex1 gstk_E29 26 20" 
value "multi_step tre0_ex1 gstk_E29 27 20" 
value "multi_step tre0_ex1 gstk_E29 28 20" 
value "multi_step tre0_ex1 gstk_E29 29 20" 
value "multi_step tre0_ex1 gstk_E29 30 20" 
value "multi_step tre0_ex1 gstk_E29 31 20" 
value "multi_step tre0_ex1 gstk_E29 32 20" 
value "multi_step tre0_ex1 gstk_E29 33 20" 
value "multi_step tre0_ex1 gstk_E29 34 20" 
value "multi_step tre0_ex1 gstk_E29 35 20" 
value "multi_step tre0_ex1 gstk_E29 36 20" 
value "multi_step tre0_ex1 gstk_E29 37 20" 
value "multi_step tre0_ex1 gstk_E29 38 20" 
value "multi_step tre0_ex1 gstk_E29 39 20" 
value "multi_step tre0_ex1 gstk_E29 40 20" 
value "multi_step tre0_ex1 gstk_E29 41 20" 
value "multi_step tre0_ex1 gstk_E29 42 20" 
value "multi_step tre0_ex1 gstk_E29 43 20" 
value "multi_step tre0_ex1 gstk_E29 44 20" 
value "multi_step tre0_ex1 gstk_E29 45 20" 
value "multi_step tre0_ex1 gstk_E29 46 20" 
value "multi_step tre0_ex1 gstk_E29 47 20" 
value "multi_step tre0_ex1 gstk_E29 48 20" 
value "multi_step tre0_ex1 gstk_E29 49 20" 
value "multi_step tre0_ex1 gstk_E29 50 20"
value "multi_step tre0_ex1 gstk_E29 51 20" 
value "multi_step tre0_ex1 gstk_E29 52 20" 
value "multi_step tre0_ex1 gstk_E29 53 20" 
value "multi_step tre0_ex1 gstk_E29 54 20" 
value "multi_step tre0_ex1 gstk_E29 55 20" 
value "multi_step tre0_ex1 gstk_E29 56 20" 
value "multi_step tre0_ex1 gstk_E29 57 20" 
value "multi_step tre0_ex1 gstk_E29 58 20" 
value "multi_step tre0_ex1 gstk_E29 59 20" 
value "multi_step tre0_ex1 gstk_E29 60 20" 
value "multi_step tre0_ex1 gstk_E29 61 20" 
value "multi_step tre0_ex1 gstk_E29 62 20" 
value "multi_step tre0_ex1 gstk_E29 63 20" 
value "multi_step tre0_ex1 gstk_E29 64 20" 
value "multi_step tre0_ex1 gstk_E29 65 20" 
value "multi_step tre0_ex1 gstk_E29 66 20" 
value "multi_step tre0_ex1 gstk_E29 67 20" 
value "multi_step tre0_ex1 gstk_E29 68 20" 
value "multi_step tre0_ex1 gstk_E29 69 20" 
value "multi_step tre0_ex1 gstk_E29 70 20" 
value "multi_step tre0_ex1 gstk_E29 71 20" 
value "multi_step tre0_ex1 gstk_E29 72 20" 
value "multi_step tre0_ex1 gstk_E29 73 20" 
value "multi_step tre0_ex1 gstk_E29 74 20" 
value "multi_step tre0_ex1 gstk_E29 75 20" 
value "multi_step tre0_ex1 gstk_E29 76 20" 
value "multi_step tre0_ex1 gstk_E29 77 20" 
value "multi_step tre0_ex1 gstk_E29 78 20" 
value "multi_step tre0_ex1 gstk_E29 79 20" 
value "multi_step tre0_ex1 gstk_E29 80 20" 
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E29 79 20) [(r_id, (NL 2) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E29 80 20) (3000000-263)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E29 80 20)"


(*E30 --- same code as E29, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E30 1 20" 
value "multi_step tre0_ex1 gstk_E30 2 20" 
value "multi_step tre0_ex1 gstk_E30 3 20" 
value "multi_step tre0_ex1 gstk_E30 4 20" 
value "multi_step tre0_ex1 gstk_E30 5 20" 
value "multi_step tre0_ex1 gstk_E30 6 20" 
value "multi_step tre0_ex1 gstk_E30 7 20" 
value "multi_step tre0_ex1 gstk_E30 8 20" 
value "multi_step tre0_ex1 gstk_E30 9 20" 
value "multi_step tre0_ex1 gstk_E30 10 20" 
value "multi_step tre0_ex1 gstk_E30 11 20" 
value "multi_step tre0_ex1 gstk_E30 12 20" 
value "multi_step tre0_ex1 gstk_E30 13 20" 
value "multi_step tre0_ex1 gstk_E30 14 20" 
value "multi_step tre0_ex1 gstk_E30 15 20" 
value "multi_step tre0_ex1 gstk_E30 16 20" 
value "multi_step tre0_ex1 gstk_E30 17 20" 
value "multi_step tre0_ex1 gstk_E30 18 20" 
value "multi_step tre0_ex1 gstk_E30 19 20" 
value "multi_step tre0_ex1 gstk_E30 20 20"
value "multi_step tre0_ex1 gstk_E30 21 20" 
value "multi_step tre0_ex1 gstk_E30 22 20" 
value "multi_step tre0_ex1 gstk_E30 23 20" 
value "multi_step tre0_ex1 gstk_E30 24 20" 
value "multi_step tre0_ex1 gstk_E30 25 20" 
value "multi_step tre0_ex1 gstk_E30 26 20" 
value "multi_step tre0_ex1 gstk_E30 27 20" 
value "multi_step tre0_ex1 gstk_E30 28 20" 
value "multi_step tre0_ex1 gstk_E30 29 20" 
value "multi_step tre0_ex1 gstk_E30 30 20"
value "multi_step tre0_ex1 gstk_E30 31 20" 
value "multi_step tre0_ex1 gstk_E30 32 20" 
value "multi_step tre0_ex1 gstk_E30 33 20" 
value "multi_step tre0_ex1 gstk_E30 34 20" 
value "multi_step tre0_ex1 gstk_E30 35 20" 
value "multi_step tre0_ex1 gstk_E30 36 20" 
value "multi_step tre0_ex1 gstk_E30 37 20" 
value "multi_step tre0_ex1 gstk_E30 38 20" 
value "multi_step tre0_ex1 gstk_E30 39 20" 
value "multi_step tre0_ex1 gstk_E30 40 20"
value "multi_step tre0_ex1 gstk_E30 41 20" 
value "multi_step tre0_ex1 gstk_E30 42 20" 
value "multi_step tre0_ex1 gstk_E30 43 20" 
value "multi_step tre0_ex1 gstk_E30 44 20" 
value "multi_step tre0_ex1 gstk_E30 45 20" 
value "multi_step tre0_ex1 gstk_E30 46 20" 
value "multi_step tre0_ex1 gstk_E30 47 20" 
value "multi_step tre0_ex1 gstk_E30 48 20" 
value "multi_step tre0_ex1 gstk_E30 49 20" 
value "multi_step tre0_ex1 gstk_E30 50 20"
value "multi_step tre0_ex1 gstk_E30 51 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E30 51 20)"


(*E31 --- same code as E29, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_E31 1 20" 
value "multi_step tre0_ex1 gstk_E31 2 20" 
value "multi_step tre0_ex1 gstk_E31 3 20" 
value "multi_step tre0_ex1 gstk_E31 4 20" 
value "multi_step tre0_ex1 gstk_E31 5 20" 
value "multi_step tre0_ex1 gstk_E31 6 20" 
value "multi_step tre0_ex1 gstk_E31 7 20" 
value "multi_step tre0_ex1 gstk_E31 8 20" 
value "multi_step tre0_ex1 gstk_E31 9 20" 
value "multi_step tre0_ex1 gstk_E31 10 20"
value "multi_step tre0_ex1 gstk_E31 11 20" 
value "multi_step tre0_ex1 gstk_E31 12 20" 
value "multi_step tre0_ex1 gstk_E31 13 20" 
value "multi_step tre0_ex1 gstk_E31 14 20" 
value "multi_step tre0_ex1 gstk_E31 15 20" 
value "multi_step tre0_ex1 gstk_E31 16 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E31 16 20)"


(*E32 --- (xx=0, r=0) \<rightarrow>* (xx=3, r=4)
  let xx, r
  switch add(xx, 1)
  default
  {
      xx,r := f()
  }
*)
(*
value "multi_step tre0_ex1 gstk_E32 1 20" 
value "multi_step tre0_ex1 gstk_E32 2 20" 
value "multi_step tre0_ex1 gstk_E32 3 20" 
value "multi_step tre0_ex1 gstk_E32 4 20" 
value "multi_step tre0_ex1 gstk_E32 5 20" 
value "multi_step tre0_ex1 gstk_E32 6 20" 
value "multi_step tre0_ex1 gstk_E32 7 20" 
value "multi_step tre0_ex1 gstk_E32 8 20" 
value "multi_step tre0_ex1 gstk_E32 9 20" 
value "multi_step tre0_ex1 gstk_E32 10 20"
value "multi_step tre0_ex1 gstk_E32 11 20" 
value "multi_step tre0_ex1 gstk_E32 12 20" 
value "multi_step tre0_ex1 gstk_E32 13 20" 
value "multi_step tre0_ex1 gstk_E32 14 20" 
value "multi_step tre0_ex1 gstk_E32 15 20" 
value "multi_step tre0_ex1 gstk_E32 16 20" 
value "multi_step tre0_ex1 gstk_E32 17 20" 
value "multi_step tre0_ex1 gstk_E32 18 20" 
value "multi_step tre0_ex1 gstk_E32 19 20" 
value "multi_step tre0_ex1 gstk_E32 20 20"
value "multi_step tre0_ex1 gstk_E32 21 20" 
value "multi_step tre0_ex1 gstk_E32 22 20" 
value "multi_step tre0_ex1 gstk_E32 23 20" 
value "multi_step tre0_ex1 gstk_E32 24 20" 
value "multi_step tre0_ex1 gstk_E32 25 20" 
value "multi_step tre0_ex1 gstk_E32 26 20" 
value "multi_step tre0_ex1 gstk_E32 27 20" 
value "multi_step tre0_ex1 gstk_E32 28 20" 
value "multi_step tre0_ex1 gstk_E32 29 20" 
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_E32 28 20)
           [(xx_id, (NL 3) :L U256), (r_id, (NL 4) :L U256)]"

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_E32 29 20) (3000000-95)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_E32 29 20)"


(*E33 --- same code as E32, but with gas exhaustion*)
(*
value "multi_step tre0_ex1 gstk_E33 1 20" 
value "multi_step tre0_ex1 gstk_E33 2 20" 
value "multi_step tre0_ex1 gstk_E33 3 20" 
value "multi_step tre0_ex1 gstk_E33 4 20" 
value "multi_step tre0_ex1 gstk_E33 5 20" 
value "multi_step tre0_ex1 gstk_E33 6 20" 
value "multi_step tre0_ex1 gstk_E33 7 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E33 7 20)"


(*E34 --- same code as E32, but with overflow of words stack*)
(*
value "multi_step tre0_ex1 gstk_E34 1 20" 
value "multi_step tre0_ex1 gstk_E34 2 20" 
value "multi_step tre0_ex1 gstk_E34 3 20" 
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_E34 3 20)"


(*E35 --- same code as E32, but with count error*)
value "multi_step tre0_ex1 gstk_E32 1 0" 

value "check_gstk_cnt_err (multi_step tre0_ex1 gstk_E32 1 0)"


end
