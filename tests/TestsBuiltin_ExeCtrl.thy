(******
Tests for builtin functions of Yul language for execution control
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

chapter \<open>the tests of formal Yul language about execution control built-in function\<close>

theory "TestsBuiltin_ExeCtrl" 

imports 
  Main "../Syntax" "../Typing" "../SmallStep" "../utils/Keccak" Common_defs

begin 
(* simplest example for external calls*)
(*C1 --- ((id:-122)) \<rightarrow>* ((id:-122)=1)
    {
      u256 (-122) := call(1000, 0x1, 0, 0, 0, 0, 0)
     }
    callee{
        var bool (-121)
      }
*)
(*
value "multi_step tre0_ex1 (gstk_C1 # []) 1 100"
value "multi_step tre0_ex1 (gstk_C1 # []) 2 100"
value "multi_step tre0_ex1 (gstk_C1 # []) 3 100"
value "multi_step tre0_ex1 (gstk_C1 # []) 4 100"
value "multi_step tre0_ex1 (gstk_C1 # []) 5 100"
value "multi_step tre0_ex1 (gstk_C1 # []) 6 100"
value "multi_step tre0_ex1 (gstk_C1 # []) 7 100"
*)

value "check_var_val_stp (multi_step tre0_ex1 (gstk_C1 # []) 6 100) [(- 122, (NL 1) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 (gstk_C1 # []) 5 100) (3000000-705)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 (gstk_C1 # []) 7 100)"


(*C2 --- (a=0,xx=0) \<rightarrow>* (a=0,xx=99)
    {     
       a := call(10,0,30,0,32,23,32) 
       xx := 99       
      callee{ }
    }
  callee{ }
*)
(*call \<rightarrow>* exception, due to insufficient balance *)
(*
value "multi_step tre0_ex1 gstk_C2 1 10"
value "multi_step tre0_ex1 gstk_C2 2 10"
value "multi_step tre0_ex1 gstk_C2 3 10"
value "multi_step tre0_ex1 gstk_C2 4 10"
value "multi_step tre0_ex1 gstk_C2 5 10"
value "multi_step tre0_ex1 gstk_C2 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C2 5 10)
  [(xx_id, (NL 99) :L U256),(a_id, (NL 0) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C2 6 10) (3000000-14)"

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_C2 2 10)"


(*C3 ---(xx=28,y=0) \<rightarrow>* (xx=1,y=400)
    {
      xx := call(10,0,30,0,32,23,32))
      y := 400   
    }
     callee{ }
*)
(*
value "multi_step tre0_ex1 gstk_C3 1 10"
value "multi_step tre0_ex1 gstk_C3 2 10"
value "multi_step tre0_ex1 gstk_C3 3 10"
value "multi_step tre0_ex1 gstk_C3 4 10"
value "multi_step tre0_ex1 gstk_C3 5 10"
value "multi_step tre0_ex1 gstk_C3 6 10"
value "multi_step tre0_ex1 gstk_C3 7 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C3 6 10)
  [(xx_id, (NL 1) :L U256),(y_id, (NL 400) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C3 4 10) (3000000-9700)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C3 4 10)"


(*C4 --- (xx=28,y=0) \<rightarrow>* (xx=1,y=400)
    {
      y := callcode(10,0,30,0,32,23,32))
      y := 400   
    }
    callcodeblk{ }
*)
(*
value "multi_step tre0_ex1 gstk_C4 1 10"
value "multi_step tre0_ex1 gstk_C4 2 10"
value "multi_step tre0_ex1 gstk_C4 3 10"
value "multi_step tre0_ex1 gstk_C4 4 10"
value "multi_step tre0_ex1 gstk_C4 5 10"
value "multi_step tre0_ex1 gstk_C4 6 10"
value "multi_step tre0_ex1 gstk_C4 7 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C4 6 10)
  [(xx_id, (NL 1) :L U256),(y_id, (NL 400) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C4 4 10) (3000000-9700)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C4 4 10)"


(*C5 ---(xx=28,y=0) \<rightarrow>* (xx=1,y=400)
   {
      xx := delegatecall(10,0,0,32,23,32)
      y := 400
   }
    delcallblk{ }
*)
(*
value "multi_step tre0_ex1 gstk_C5 1 10"
value "multi_step tre0_ex1 gstk_C5 2 10"
value "multi_step tre0_ex1 gstk_C5 3 10"
value "multi_step tre0_ex1 gstk_C5 4 10"
value "multi_step tre0_ex1 gstk_C5 5 10"
value "multi_step tre0_ex1 gstk_C5 6 10"
value "multi_step tre0_ex1 gstk_C5 7 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C5 6 10)
  [(xx_id, (NL 1) :L U256),(y_id, (NL 400) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C5 4 10) (3000000-700)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C5 4 10)"


(*C6 ---
  gstk1#gstk2
   gstk1{
          x := 4
          revert(x,2)
         }
   gstk2 {
            h := true
          }
*)
(*
value "multi_step tre0_ex1 gstk_C6 1 10"
value "multi_step tre0_ex1 gstk_C6 2 10"
value "multi_step tre0_ex1 gstk_C6 3 10"
value "multi_step tre0_ex1 gstk_C6 4 10"
value "multi_step tre0_ex1 gstk_C6 5 10"
value "multi_step tre0_ex1 gstk_C6 6 10"
value "multi_step tre0_ex1 gstk_C6 7 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C6 6 10) [(h_id, TL :L Bool)]" 

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C6 6 10)"


(*C7 ---
    gstk1#gstk2
   gstk1 {
            return(x,2)
             x := 4
          }
   gstk2 {
             h := true
          }
*)
(*
value "multi_step tre0_ex1 gstk_C7 1 10"
value "multi_step tre0_ex1 gstk_C7 2 10"
value "multi_step tre0_ex1 gstk_C7 3 10"
value "multi_step tre0_ex1 gstk_C7 4 10"
value "multi_step tre0_ex1 gstk_C7 5 10"
value "multi_step tre0_ex1 gstk_C7 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C7 5 10) [(h_id, TL :L Bool)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C7 3 10) (3000000-3-0)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C7 6 10)"


(*C8 ---
   selfdestruct(1)
*)
(*
value "multi_step tre0_ex1 gstk_C8 1 20"  
value "multi_step tre0_ex1 gstk_C8 2 20"  
*)

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C8 2 20) (3000000-5000)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C8 2 20)"


(*C9 ---
   log0(0x1,32)
*)

(*
value "multi_step tre0_ex1 gstk_C9 1 20"
value "multi_step tre0_ex1 gstk_C9 2 20"
value "multi_step tre0_ex1 gstk_C9 3 20"
*)

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C9 2 20) (3000000-(375+8*32+0))"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C9 3 20)"


(*C10 ---
   log1(0x1,0x20,0x24 )
*)
(*
value "multi_step tre0_ex1 gstk_C10 1 20"
value "multi_step tre0_ex1 gstk_C10 2 20"
value "multi_step tre0_ex1 gstk_C10 3 20"
*)

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C10 2 20) (3000000-(375+8*32+375))"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C10 3 20)"


(*C11 ---
  log2(0x1,0x20,0x24,0x31)
*)
(*
value "multi_step tre0_ex1 gstk_C11 1 20"
value "multi_step tre0_ex1 gstk_C11 2 20"
value "multi_step tre0_ex1 gstk_C11 3 20"
*)

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C11 2 20) (3000000-(375+8*32+375*2))"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C11 3 20)"


(*C12 ---
  log3(0x1,0x20,0x24,0x31,0x3a)
*)
(*
value "multi_step tre0_ex1 gstk_C12 1 20"
value "multi_step tre0_ex1 gstk_C12 2 20"
value "multi_step tre0_ex1 gstk_C12 3 20"
*)

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C12 2 20) (3000000-(375+8*32+375*3))"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C12 3 20)"


(*C13 ---
  log4(0x1,0x20,0x24,0x31,0x3a,0x44)
*)
(*
value "multi_step tre0_ex1 gstk_C13 1 20"
value "multi_step tre0_ex1 gstk_C13 2 20"
value "multi_step tre0_ex1 gstk_C13 3 20"
*)

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C13 2 20) (3000000-(375+8*32+375*4))"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C13 3 20)"


(*C14 --- 
   invalid()
*)
(*
value "multi_step tre0_ex1 gstk_C14 1 20"
value "multi_step tre0_ex1 gstk_C14 2 20"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_C14 2 20)"


(*C15 ---
  stop()
*)
(*
value "multi_step tre0_ex1 gstk_C15 1 20"
value "multi_step tre0_ex1 gstk_C15 2 20"
*)

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C15 2 20) (3000000)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C15 2 20)"


(*C16 --- external call fails.
    {
      xx := callcode(10,0,30,0,32,23,32))
      y := 400   
    }
     callcodeblk{ }
*)
(*
value "multi_step tre0_ex1 gstk_C16 1 10"
value "multi_step tre0_ex1 gstk_C16 2 10"
value "multi_step tre0_ex1 gstk_C16 3 10"
value "multi_step tre0_ex1 gstk_C16 4 10"
value "multi_step tre0_ex1 gstk_C16 5 10"
value "multi_step tre0_ex1 gstk_C16 6 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C16 5 10)
  [(xx_id, (NL 0) :L U256),(y_id, (NL 400) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C16 6 10) (3000000-14)"

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_C16 2 10)"


(*C17 --- same code as C16, but to_addr is None and eternal call successes.*)
(*
value "multi_step tre0_ex1 gstk_C17 1 10"
value "multi_step tre0_ex1 gstk_C17 2 10"
value "multi_step tre0_ex1 gstk_C17 3 10"
value "multi_step tre0_ex1 gstk_C17 4 10"
value "multi_step tre0_ex1 gstk_C17 5 10"
value "multi_step tre0_ex1 gstk_C17 6 10"
value "multi_step tre0_ex1 gstk_C17 7 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C17 6 10)
  [(xx_id, (NL 1) :L U256),(y_id, (NL 400) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C17 7 10) (3000000-9714)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C17 3 10)"


(*C18 --- external call fails and gas exhaustion. 
    {
      xx := delegatecall(10,0,0,32,23,32)
      y := 400   
    }
     delegatecallblk{ }
*)
(*
value "multi_step tre0_ex1 gstk_C18 1 10"
value "multi_step tre0_ex1 gstk_C18 2 10"
value "multi_step tre0_ex1 gstk_C18 3 10"
value "multi_step tre0_ex1 gstk_C18 4 10"
value "multi_step tre0_ex1 gstk_C18 5 10"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_C18 2 10)"

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_C18 5 10)"


(*C19 --- same code as C18, but to_addr is None*)
(*
value "multi_step tre0_ex1 gstk_C19 1 10"
value "multi_step tre0_ex1 gstk_C19 2 10"
value "multi_step tre0_ex1 gstk_C19 3 10"
value "multi_step tre0_ex1 gstk_C19 4 10"
value "multi_step tre0_ex1 gstk_C19 5 10"
value "multi_step tre0_ex1 gstk_C19 6 10"
value "multi_step tre0_ex1 gstk_C19 7 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C19 6 10)
  [(xx_id, (NL 1) :L U256),(y_id, (NL 400) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C19 7 10) (3000000-714)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C19 3 10)"


(*C20 --- with insufficient gas and gas exhaustion
{
      xx := call(10,0,30,0,32,23,32))
      y := 400   
    }
     callee{ }
*)
(*
value "multi_step tre0_ex1 gstk_C20 1 10"
value "multi_step tre0_ex1 gstk_C20 2 10"
value "multi_step tre0_ex1 gstk_C20 3 10"
value "multi_step tre0_ex1 gstk_C20 4 10"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_C20 2 10)"

value "check_gstk_exc_stp (multi_step tre0_ex1 gstk_C20 4 10)"


(*C21 --- same code as C20, but to_addr is None*)
(*
value "multi_step tre0_ex1 gstk_C21 1 10"
value "multi_step tre0_ex1 gstk_C21 2 10"
value "multi_step tre0_ex1 gstk_C21 3 10"
value "multi_step tre0_ex1 gstk_C21 4 10"
value "multi_step tre0_ex1 gstk_C21 5 10"
value "multi_step tre0_ex1 gstk_C21 6 10"
value "multi_step tre0_ex1 gstk_C21 7 10"
*)

value "check_var_val_stp (multi_step tre0_ex1 gstk_C21 6 10)
  [(xx_id, (NL 1) :L U256),(y_id, (NL 400) :L U256)]" 

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C21 7 10) (3000000-34714)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C21 7 10)"


(*C22 --- to_addr is None.
  selfdestruct(0)
*)
(*
value "multi_step tre0_ex1 gstk_C22 1 10"
value "multi_step tre0_ex1 gstk_C22 2 10"
*)

value "check_gs_gas_stp (multi_step tre0_ex1 gstk_C22 2 10) (3000000-30000)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 gstk_C22 2 10)"


(*C23 --- with overflow of call stacks.
    {
      u256 (-122) := call(1, 0x1, 0, 0, 0, 0, 0)
     }
    callee{
        var xx := call(1, 0x1, 0, 0, 0, 0, 0)
      }
*)
(*
value "multi_step tre0_ex1 (gstk_C23 # []) 1 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 3 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 4 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 5 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 6 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 7 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 8 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 9 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 10 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 11 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 12 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 13 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 14 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 15 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 16 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 17 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 18 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 1120 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2020 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2030 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2033 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2035 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2037 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2040 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2042 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2044 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2046 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2047 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2048 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2049 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2050 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2051 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2052 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2053 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 2054 100"
value "multi_step tre0_ex1 (gstk_C23 # []) 4210 100"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 (gstk_C23 # []) 2048 100)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 (gstk_C23 # []) 2049 100)"


(*C24 --- with overflow of call stacks.
    {
      u256 (-122) := callcode(10, 0x11, 0, 0, 0, 0, 0)
     }
    callee{
        var xx := call(10, 0x11, 0, 0, 0, 0, 0)
      }
*)
(*
value "multi_step tre0_ex1 (gstk_C24 # []) 1 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 3 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 4 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 5 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 6 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 7 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 8 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 9 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 10 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2044 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2046 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2047 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2048 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2049 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2050 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2051 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2052 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2053 100"
value "multi_step tre0_ex1 (gstk_C24 # []) 2054 100"
*)

value "check_gstk_exc_stp (multi_step tre0_ex1 (gstk_C24 # []) 2048 100)"

value "\<not> check_gstk_exc_stp (multi_step tre0_ex1 (gstk_C24 # []) 2049 100)"


end