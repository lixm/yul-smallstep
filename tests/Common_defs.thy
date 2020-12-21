(******
Common definitions for the test cases 
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

theory "Common_defs" 

imports 
  Main "../Syntax" "../Typing" "../SmallStep" "../utils/Keccak"

begin 

definition a_id where "a_id = -111"
definition b_id where "b_id = -112"
definition b1_id where "b1_id = -1112"
definition x_id where "x_id = -134"
definition y_id where "y_id = -135"
definition h_id where "h_id = -118"
definition r_id where "r_id = -128"
definition s_id where "s_id = -129"
definition z_id where "z_id = -136" 
definition aa_id where "aa_id = -1111" 
definition a1_id where "a1_id = -10011" 
definition a2_id where "a2_id = -10112"
definition xx_id where "xx_id = -1134"
definition k_id where "k_id = -11345"


definition empty_account  :: "account"  where 
  "empty_account = \<lparr>
    code_of = None,
    store_of = (\<lambda>x . (case x of _ \<Rightarrow> (0x0 :: (256 word)))),
    bal_of = (0x0 :: 256 word),
    nonce_of = (0x0 :: 256 word)
  \<rparr>"

definition account1  :: "account"  where 
  "account1 = \<lparr>
    code_of = None,
    store_of = (\<lambda>x . (case x of _ \<Rightarrow> (0x0 :: (256 word)))),
    bal_of = (0xfff4 :: 256 word),
    nonce_of = (0x02 :: 256 word)
  \<rparr>"


definition ls_ex1 where "ls_ex1 = []"

(*definition ls_ex_y0 where "ls_ex_y0 = [(y_id, IntV 0)]" *)
definition ls_ex_a0 where "ls_ex_a0 = [(a_id, ((NL 0) :L U256))]" 
definition ls_ex_x0 where "ls_ex_x0 = [(x_id, ((NL 0) :L U256))]" 
definition ls_ex_h0 where "ls_ex_h0 = [(h_id, (FL :L Bool))]"
definition ls_ex_b0 where "ls_ex_b0 = [(b_id, (FL :L Bool))]"
definition ls_ex_r0 where "ls_ex_r0 = [(r_id, ((NL 0) :L U256))]"
definition ls_ex_s0 where "ls_ex_s0 = [(s_id, ((NL 0) :L S256))]"
definition ls_ex_aa where "ls_ex_aa = [(aa_id, ((NL 0):L S256))]" 

(*
definition ts_ex1 where "ts_ex1 = []" 
definition ts_ex_a where "ts_ex_a = [(a_id, U256)]" 
definition ts_ex_b where "ts_ex_b = [(b_id, Bool)]" 
definition ts_ex_x where "ts_ex_x = [(x_id, U256)]" 
definition ts_ex_y where "ts_ex_y = [(y_id, U256)]" 
definition ts_ex_r where "ts_ex_r = [(r_id, U256)]"
definition ts_ex_s where "ts_ex_s = [(s_id, S256)]"
definition ts_ex_h where "ts_ex_h = [(h_id, Bool)]"
definition ts_ex_aa where "ts_ex_aa = [(aa_id, S256)]" 
*)

definition ls_ex_x1 where "ls_ex_x1 = [(x_id, ((NL 20) :L U256))]"
definition ls_ex20 where "ls_ex20 = [(x_id, ((NL 20) :L U256)),(a_id, ((NL 0) :L U256))]" 
definition ls_ex_a1 where "ls_ex_a1 = [(a_id, ((NL 6) :L U256))]" 
definition ls_ex_s1 where "ls_ex_s1 = [(s_id, ((NL (-8)) :L S256))]"  
definition ls_ex2_a1 :: lstate where "ls_ex2_a1 = [(a1_id, ((NL 10) :L U256)),(a2_id, ((NL 0) :L U256))]" 
definition ls_ex2 :: lstate where "ls_ex2 = [(xx_id, ((NL 28) :L U256)),(y_id, ((NL 0) :L U256))]" 
(*definition ls_a3 where "ls_a3 = [(a_id, IntV 3)]" *)

(*
definition ts_ex_x11 where "ts_ex_x11 = [(a_id, U256),(r_id, U256)]" 
definition ts_ex20 where "ts_ex20 = [(a_id, U256),(x_id, U256)]" 
definition ts_ex_x_a1 where "ts_ex_x_a1 = [(a1_id, U256),(a2_id, U256)]" 
definition ts_ex2 where "ts_ex2 = [(xx_id, U256),(y_id,U256)]" 
*)

definition a1_expr1 :: expr where "a1_expr1 = EAssg [a1_id] (EImLit ((NL 3):L U256))"
definition xx_expr1 :: expr where "xx_expr1 = EAssg [xx_id] (EImLit ((NL 22):L U256))"
definition y_expr1 :: expr where "y_expr1 = EAssg [y_id] (EImLit ((NL 400):L U256))  " 


definition gs0_ex1 :: gstate where 
  "gs0_ex1 = 
  \<lparr>
    addr_of = 0x0,
    saddr_of = 0x0, 
    money_of = (0xffff :: 256 word), 
    input_of = [(0x26 :: 8 word), (0x12 :: 8 word), (0x1f :: 8 word), (0xf0 :: 8 word)],
    mem_of = (\<lambda>x. 0x0), 
    naws_of = 0, 
    gas_of = 3000000, 
    ct_of = 10,
    accs_of = (\<lambda>x. (case x of _ \<Rightarrow> Some empty_account)), 
    refund_of = (0x0 :: 256 word), 
    logs_of = [], 
    ss_of = {}
  \<rparr>"

definition gs1_bfun :: gstate where 
  "gs1_bfun = 
  \<lparr>
    addr_of =  0x0DCd2F752394c41875e259e00bb44fd505297caF,
    saddr_of = 0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c, 
    money_of = (0xffff :: 256 word), 
    input_of = [(0x26 :: 8 word), (0x12 :: 8 word), (0x1f :: 8 word), (0xf0 :: 8 word)],
    mem_of = (\<lambda>x. 0x01), 
    naws_of = 3, 
    gas_of = 3000000, 
    ct_of = 10,
    accs_of = (\<lambda>x. (case x of _ \<Rightarrow> Some account1)), 
    refund_of = (0x0 :: 256 word), 
    logs_of = [], 
    ss_of = {}
  \<rparr>"

definition blk_hdr_ex1 :: blk_header where 
  "
    blk_hdr_ex1 = 
    \<lparr> 
      pheader_hash_of = (0x0 :: 256 word), 
      beneficiary_of = 0x0e9281e9C6a0808672EAba6bd1220E144C9bb07a, 
      difficulty_of = (0xa :: 256 word), 
      number_of = (0x10 :: 256 word), 
      gas_limit_of = (0x1000 :: 256 word), 
      time_stamp_of = (0x20 :: 256 word)
    \<rparr>
  "
(*
record trans_env = 
  oaddr_of :: address \<comment> \<open>address of the original transactor\<close>
  gprice_of :: "256 word" 
  bheader_of :: blk_header
*)
value "0x1000::nat"

definition tre0_ex1 :: trans_env where 
  "
    tre0_ex1 = 
    \<lparr>
      oaddr_of = 0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c, 
      gprice_of = (0xa2 :: 256 word), 
      bheader_of = blk_hdr_ex1
    \<rparr>
  "

definition check_var_val_stp :: "gstack \<Rightarrow> (id0 \<times> literal) list \<Rightarrow> bool" where 
  "check_var_val_stp gstk id_lits = (
    case gstk of 
      [GFrmNormal [LFrm_E (_, ls, _)] _ _] \<Rightarrow> 
        (foldl (\<lambda> acc (x, lit). (acc \<and> lm_get ls x = Some lit)) True id_lits)
    | [GFrmNormal [LFrm_B (BEGIN[]END, ls, _, _)] _ _] \<Rightarrow>
        (foldl (\<lambda> acc (x, lit). (acc \<and> lm_get ls x = Some lit)) True id_lits)
    | _ => False
    )"

definition check_gs_gas_stp :: "gstack \<Rightarrow> 256 word \<Rightarrow> bool" where 
  "check_gs_gas_stp gstk left_gas = (
    case gstk of 
      [GFrmNormal [LFrm_E (_, _, _)] gs _] \<Rightarrow> 
        (if left_gas = (gas_of gs) then (True) else (False))
    | (GFrmHalt gs _ _) # gstk \<Rightarrow>
        (if left_gas = (gas_of gs) then (True) else (False))
    | [GFrmNormal [LFrm_B (_, _, _, _)] gs _] \<Rightarrow>
        (if left_gas = (gas_of gs) then (True) else (False))
    | _ \<Rightarrow> False
    )"

definition check_gstk_exc_stp :: "gstack \<Rightarrow> bool" where 
  "check_gstk_exc_stp gstk = (
    case gstk of 
      ((GFrmExc _) # gstk') \<Rightarrow> True
     | _ \<Rightarrow> False 
  )"

definition check_gstk_cnt_err :: "gstack \<Rightarrow> bool" where 
  "check_gstk_cnt_err gstk = (
    case gstk of 
      ((GFrmCounterErr) # gstk') \<Rightarrow> True
     | _ \<Rightarrow> False 
  )"


(*
  - (E1 --- E35) : about expressions features. 
  - (L1 --- L10) : about logic built-in functions.
  - (A1 --- A26) : about arithmetic built-in functions.
  - (M1 --- M7) : about memory and storage built-in functions.
  - (C1 --- C24) : about execution control built-in functions.
  - (S1 --- S18) : about state queries built-in functions and other built-in functions.
*)




(* 
  - (E1 --- E35) : about expressions features.
*)

(*E1 --- assign : u256 x=99  *)
definition gstk_E1 where
  "gstk_E1 = ((GFrmNormal 
                ([LFrm_E (([x_id] ::= (ELit ((NL 99) :L U256))), ls_ex_x0, [])])
                   gs0_ex1 CKDummy) # [])"

(* 
 E2 ---  if true {}     
*)
definition fb_expr_if_true where 
  "fb_expr_if_true = (IF (EImLit (TL :L Bool)) THEN (BEGIN [] END))"

definition gstk_E2 :: gstack where
  "gstk_E2 = 
    ((GFrmNormal 
      ([LFrm_E (fb_expr_if_true, ls_ex_x0, [])]) gs0_ex1 CKDummy) # [])"

(* (x=0) if false {x := 99}*)
definition gstk_E2_false :: gstack where
  "gstk_E2_false = ((GFrmNormal 
        ([LFrm_E ((IF (EImLit (FL :L Bool)) THEN 
                    (BEGIN [[x_id] ::= (EImLit ((NL 99) :L U256))] END)),
                  ls_ex_x0, [])]) gs0_ex1 CKDummy) # [])"

(*
  E3 ---  (a=0,x=20)
           if lt(a,3) {
            if gt(x,0) {x := 99}
          }
*)
definition fb_expr_if :: expr where
  "fb_expr_if = (IF (CALL b_gt_id [EId x_id, EImLit ((NL 1) :L U256)]) THEN 
                    (BEGIN [[x_id] ::= (EImLit ((NL 99) :L U256))] END))"

definition gstk_E3 :: gstack where
  "gstk_E3 = ((GFrmNormal 
        ([LFrm_E ((IF (CALL b_lt_id [EId a_id, EImLit ((NL 3) :L U256)]) THEN 
                    (BEGIN [fb_expr_if] END)),
                  ls_ex20, [])]) gs0_ex1 CKDummy) # [])"

(*E4 --- (x=20)
     for {let a := 1} gt(x, a) { a := 21 }
             {x := 10}              
            
*)
definition fb_expr_for :: expr where
  "fb_expr_for = (FOR (BEGIN [([a_id] ::= EImLit ((NL 1) :L U256))] END) 
                  (CALL b_gt_id [EId x_id, EId a_id])  (BEGIN [([a_id] ::= EImLit ((NL 21) :L U256))] END) 
                  (BEGIN [([x_id] ::= EImLit ((NL 10) :L U256))] END))"

definition gstk_E4 :: gstack where
  "gstk_E4 = ((GFrmNormal 
        ([LFrm_E (fb_expr_for, ls_ex20, [])]) gs0_ex1 CKDummy) # [])"

(*E5 --- (x=0)  switch x   
           case 0 {r := add(x,10)}
           case 1 {x := 99}
           default{
                r := 1
            } 
*)
definition fb_exprx111 :: expr where
  "fb_exprx111 = ([r_id] ::= (CALL b_add_id [EId x_id, EImLit ((NL (10)) :L U256)]))"

definition fb_expr_switch :: expr where
  "fb_expr_switch = (SWITCH(EId x_id) 
                       CASES([( ((NL 0) :L U256), BEGIN [fb_exprx111] END ),( ((NL 1) :L U256), BEGIN [[x_id] ::= (EImLit ((NL 99) :L U256))] END)])
                         DEFAULT (Some (BEGIN[[r_id] ::= EImLit ((NL (1)) :L U256)]END) ))"

definition gstk_E5 :: gstack where
  "gstk_E5 = ((GFrmNormal 
        ([LFrm_E (fb_expr_switch, ls_ex_x0@ls_ex_r0, [])]) gs0_ex1 CKDummy) # [])"

(*E6  --- (x=0) id: x *)
definition gstk_E6 where 
  "gstk_E6 = 
    ((GFrmNormal 
        ([LFrm_E (EId x_id, ls_ex_x0, [])]) gs0_ex1 CKDummy) # [])"

(*E7 --- VarDecl: {let z, r} *)
definition gstk_E7 where 
  "gstk_E7 = 
    ((GFrmNormal 
        ([LFrm_E (VAR [(z_id, U256),(r_id, U256)], [], [])]) gs0_ex1 CKDummy) # [])"

(*E8 --- EFunDef and EFunCall:
   {  let r,b := f()
      f() \<rightarrow> a,x {
        a := add(1,2)
        x := add(2,2)
      }
   }
*)
definition f_func :: expr where
  "f_func = 
    FUN f_id [] [(a_id, U256),(x_id, U256)] IS
      BEGIN[
        [a_id] ::= (CALL b_add_id [EImLit ((NL (1)) :L U256), EImLit ((NL (2)) :L U256)]), 
          [x_id] ::= (CALL b_add_id [EImLit ((NL (2)) :L U256), EImLit ((NL (2)) :L U256)])
      ]END
  " 

definition gstk_E8 :: gstack where
  "gstk_E8 = ((GFrmNormal 
        ([LFrm_B (BEGIN[(VAR [(r_id, U256),(b_id, U256)] ::- CALL f_id [])]END,
            [], (get_func_values (Blk[f_func])),
               None)]) gs1_bfun CKDummy) # [])"

(*E9 --- EFunDef and EFunCall:
      a := g(1)
        function g(x) -> y {
           y := add(x, 4)
        }
*)
definition g_funId where "g_funId = -1"

definition g_func :: block where
  "g_func = BEGIN[
      FUN g_funId [(x_id, U256)] [(y_id, U256)] IS 
      BEGIN[
        [y_id] ::= CALL b_add_id [EId x_id, EImLit ((NL (0x4)) :L U256)]
      ]END
   ]END"

definition gstk_E9 :: gstack where
  "gstk_E9 = ((GFrmNormal 
        ([LFrm_B (BEGIN[
                   VAR [(a_id, U256)],
                   [a_id] ::= (CALL g_funId [ELit ((NL (0x01)) :L U256)])]END,
               [], []@(get_func_values g_func), None)]) gs0_ex1 CKDummy) # []) "

(*E10 --- EFunDef and EFunCall:
{
	   let xx := 1
     let a1 := f1(1,f1(2,3))
     xx := f2(2,3)
     
     function f1(a,x) -> y {                           
        y := add(a, x)
      }
      
  function f2(a,x) -> y {                           
    y := mul(a, x)
  }
*)

definition f1_id :: id0 where "f1_id = -101"
definition f2_id :: id0 where "f2_id = -102"
definition f3_id :: id0 where "f3_id = -103" 
definition f4_id :: id0 where "f4_id = -104"
definition f5_id :: id0 where "f5_id = -105" 


definition f1_func :: block where
  "f1_func = BEGIN[
    FUN f_id [(a_id, U256),(x_id, U256)] [(y_id, U256)] IS
      BEGIN[
        [y_id] ::= (CALL b_add_id [ID a_id, ID x_id])
      ]END
  ]END" 

definition f2_func :: block where
  "f2_func = BEGIN[
      FUN f2_id [(a_id, U256),(x_id, U256)] [(y_id, U256)] IS 
      BEGIN[
        [y_id] ::= (CALL b_mul_id [ID a_id, ID x_id])
      ]END
   ]END"

definition gstk_E10 :: gstack where
  "gstk_E10 = ((GFrmNormal 
        ([LFrm_B (BEGIN[
                   VAR [(xx_id, U256)] ::- (ELit ((NL (0x01)) :L U256)),
                   VAR [(a1_id, U256)] ::- (CALL f1_id [(ELit ((NL (0x01)) :L U256)), 
                          (CALL f1_id [ELit ((NL (0x02)) :L U256), ELit ((NL (0x03)) :L U256)])]),
                    [xx_id] ::= (CALL f2_id [ELit ((NL (0x02)) :L U256),
                                                  ELit ((NL (0x03)) :L U256)])]END,
               [], (get_func_values f1_func)@(get_func_values f2_func), None)]) gs0_ex1 CKDummy) # []) "

(*E11
  function f3() -> h {                           
    h := lt(1, 2)
  }
  
  if f3() then { x := 1 }
*)

definition f3_func :: block where
  "f3_func = 
    BEGIN [
      FUN f3_id [] [(h_id, Bool)] IS 
        BEGIN [ [h_id] ::= (CALL b_lt_id [LIT ((NL 1) :L U256), LIT ((NL 2) :L U256)]) ] END
    ] END" 

definition gstk_E11 :: gstack where 
  "gstk_E11 = 
    (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(x_id, U256)], 
          IF (CALL f3_id []) THEN (BEGIN [[x_id] ::= LIT ((NL 1) :L U256)] END)] 
         END),
         [], (get_func_values f3_func), None)]
       gs0_ex1 CKDummy
    ) # []"

(*E12 --- same code as E11, but with gas exhaustion*)
definition gstk_E12 :: gstack where 
  "gstk_E12 = 
    (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(x_id, U256)], 
          IF (CALL f3_id []) THEN (BEGIN [[x_id] ::= LIT ((NL 1) :L U256)] END)] 
         END),
         [], (get_func_values f3_func), None)]
       (gs0_ex1\<lparr> gas_of := 3 \<rparr>) CKDummy
    ) # []"

(*E13 --- same code as E11, but with overflow of words stack*)
definition gstk_E13 :: gstack where 
  "gstk_E13 = 
    (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(x_id, U256)], 
          IF (CALL f3_id []) THEN (BEGIN [[x_id] ::= LIT ((NL 1) :L U256)] END)] 
         END),
         [], (get_func_values f3_func), None)]
       (gs0_ex1\<lparr> gas_of := 10 \<rparr>) CKDummy
    ) # []"

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
definition f4_func :: block where
  "f4_func = BEGIN[
      FUN f4_id [(a_id, U256)] [(y_id, U256)] IS 
      BEGIN[
        [y_id] ::= (CALL b_exp_id [ID a_id, EImLit ((NL (2)) :L U256)])
      ]END
   ]END"
 
definition gstk_E14 :: gstack where
  "gstk_E14 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(r_id, U256)],
        SWITCH(EId x_id) 
        CASES([(((NL 0) :L U256), BEGIN [[r_id] ::= (CALL b_and_id [EId x_id, EImLit ((NL 4) :L U256)])] END)])
        DEFAULT (Some (BEGIN[[r_id] ::= CALL f4_id [EId x_id]]END) )
      ]END, ls_ex_x1, (get_func_values f4_func), None)]) gs0_ex1 CKDummy) # [])"

(*E15 --- same code as E14, but with gas exhaustion*)
definition gstk_E15 :: gstack where 
  "gstk_E15 = 
    (GFrmNormal 
      [LFrm_B (
        (BEGIN[
        VAR [(r_id, U256)],
        SWITCH(EId x_id) 
        CASES([(((NL 0) :L U256), BEGIN [[r_id] ::= (CALL b_and_id [EId x_id, EImLit ((NL 4) :L U256)])] END)])
        DEFAULT (Some (BEGIN[[r_id] ::= CALL f4_id [EId x_id]]END) )
      ]END),
         ls_ex_x1, (get_func_values f4_func), None)]
       (gs0_ex1\<lparr> gas_of := 83 \<rparr>) CKDummy
    ) # []"

(*E16 ---  \<rightarrow>* (xx=16)
  let xx := f4(f1(1,3))
*)
definition gstk_E16 :: gstack where 
  "gstk_E16 = (GFrmNormal 
      ([LFrm_B (BEGIN[ VAR [(xx_id, U256)] ::- (CALL f4_id 
                               [(CALL f1_id [ELit ((NL (0x01)) :L U256), ELit ((NL (0x03)) :L U256)])])]END,
               [], (get_func_values f1_func)@(get_func_values f4_func), None)]) gs0_ex1 CKDummy) # []"

(*E17 --- same code as E16, but with gas exhaustion*)
definition gstk_E17 :: gstack where 
  "gstk_E17 = (GFrmNormal 
      ([LFrm_B (BEGIN[ VAR [(xx_id, U256)] ::- (CALL f4_id 
                               [(CALL f1_id [ELit ((NL (0x01)) :L U256), ELit ((NL (0x03)) :L U256)])])]END,
               [], (get_func_values f1_func)@(get_func_values f4_func), None)])
                 (gs0_ex1\<lparr> gas_of := 61 \<rparr>) CKDummy) # []"

(*E18 --- (xx=3) \<rightarrow> * (xx=6)
    let xx := 3
    xx := f2(xx, sub(3,1))
*)
definition gstk_E18 :: gstack where 
  "gstk_E18 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(xx_id, U256)] ::- (ELit ((NL (0x03)) :L U256)),
                 [(xx_id)] ::= (CALL f2_id
                        [EId xx_id, (CALL b_sub_id [ELit ((NL (0x03)) :L U256), ELit ((NL (0x01)) :L U256)])])]END,
          [], (get_func_values f2_func), None)]) gs0_ex1 CKDummy) # []"
                
(*E19 --- same code as E18, but with gas exhaustion*)
definition gstk_E19 :: gstack where 
  "gstk_E19 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(xx_id, U256)] ::- (ELit ((NL (0x03)) :L U256)),
                 [(xx_id)] ::= (CALL f2_id
                        [EId xx_id, (CALL b_sub_id [ELit ((NL (0x03)) :L U256), ELit ((NL (0x01)) :L U256)])])]END,
          [], (get_func_values f2_func), None)])
             (gs0_ex1\<lparr> gas_of := 19 \<rparr>) CKDummy) # []"

(*E20 --- (xx=3) \<rightarrow>* (xx=20)
     let xx := 3 
     if f3() {
          xx := f2(4,5)
      }
*)
definition gstk_E20 :: gstack where
  "gstk_E20 = (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)] ::- (ELit ((NL (0x03)) :L U256)), 
          IF (CALL f3_id []) THEN (BEGIN [[xx_id] ::= (CALL f2_id
                        [ELit ((NL (0x04)) :L U256), ELit ((NL (0x05)) :L U256)])] END)] 
         END),
         [], (get_func_values f3_func)@(get_func_values f2_func), None)] gs0_ex1 CKDummy
    ) # []"

(*E21 --- same code as E20, but with gas exhaustion*)
definition gstk_E21 :: gstack where
  "gstk_E21 = (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)] ::- (ELit ((NL (0x03)) :L U256)), 
          IF (CALL f3_id []) THEN (BEGIN [[xx_id] ::= (CALL f2_id
                        [ELit ((NL (0x04)) :L U256), ELit ((NL (0x05)) :L U256)])] END)] 
         END),
         [], (get_func_values f3_func)@(get_func_values f2_func), None)] 
           (gs0_ex1\<lparr> gas_of := 50 \<rparr>) CKDummy
    ) # []"

(*E22 --- same code as E20, but with overflow of words stack*)
definition gstk_E22 :: gstack where
  "gstk_E22 = (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)] ::- (ELit ((NL (0x03)) :L U256)), 
          IF (CALL f3_id []) THEN (BEGIN [[xx_id] ::= (CALL f2_id
                        [ELit ((NL (0x04)) :L U256), ELit ((NL (0x05)) :L U256)])] END)] 
         END),
         [], (get_func_values f3_func)@(get_func_values f2_func), None)] 
           (gs0_ex1\<lparr> ct_of := 1022 \<rparr>) CKDummy
    ) # []"

(*E23 --- (r=0) \<rightarrow>* (r=7)
   let xx := 3
   let r
   for {let k:=1} gt(xx,k) {k:=add(k,1)}
    {
        r:= add(xx, f4(k))
    }
*)
definition gstk_E23 :: gstack where
  "gstk_E23 = ((GFrmNormal       
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)] ::- ELit ((NL (0x03)) :L U256),
          VAR [(r_id, U256)], 
          FOR (BEGIN [(VAR [(k_id, U256)] ::- ELit ((NL 1) :L U256))] END) 
              (CALL b_gt_id [EId xx_id, EId k_id]) 
              (BEGIN [([k_id] ::= CALL b_add_id [ID k_id, ELit ((NL 1) :L U256)])] END) 
              (BEGIN [
                 [(r_id)] ::= CALL b_add_id [ID xx_id, CALL f4_id [EId k_id]]
              ] END)] 
         END),
         [], (get_func_values f4_func), None)]
           gs0_ex1 CKDummy) # [])"

(*E24 ---same code as E23, but with gas exhaustion*)
definition gstk_E24 :: gstack where
  "gstk_E24 = ((GFrmNormal       
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)] ::- ELit ((NL (0x03)) :L U256),
          VAR [(r_id, U256)], 
          FOR (BEGIN [(VAR [(k_id, U256)] ::- ELit ((NL 1) :L U256))] END) 
              (CALL b_gt_id [EId xx_id, EId k_id]) 
              (BEGIN [([k_id] ::= CALL b_add_id [ID k_id, ELit ((NL 1) :L U256)])] END) 
              (BEGIN [
                 [(r_id)] ::= CALL b_add_id [ID xx_id, CALL f4_id [EId k_id]]
              ] END) 
         ] END),
         [], (get_func_values f4_func), None)]
           (gs0_ex1\<lparr> gas_of := 102 \<rparr>) CKDummy) # [])"

(*E25 --- same code as E23, but with overflow of words stack*)
definition gstk_E25 :: gstack where
  "gstk_E25 = ((GFrmNormal       
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)] ::- ELit ((NL (0x03)) :L U256),
          VAR [(r_id, U256)], 
          FOR (BEGIN [(VAR [(k_id, U256)] ::- ELit ((NL 1) :L U256))] END) 
              (CALL b_gt_id [EId xx_id, EId k_id]) 
              (BEGIN [([k_id] ::= CALL b_add_id [ID k_id, ELit ((NL 1) :L U256)])] END) 
              (BEGIN [
                 [(r_id)] ::= CALL b_add_id [ID xx_id, CALL f4_id [EId k_id]]
              ] END)] 
         END),
         [], (get_func_values f4_func), None)]
           (gs0_ex1\<lparr> ct_of := 1022 \<rparr>) CKDummy) # [])"

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
definition gstk_E26 :: gstack where
  "gstk_E26 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256), (r_id, U256)],
        SWITCH(EId xx_id) 
        CASES([(((NL 0) :L U256), BEGIN [
            IF (CALL f3_id []) THEN (
            BEGIN [
              (CALL b_mstore_id [EId xx_id,
                  CALL b_exp_id [ELit ((NL (0x02)) :L U256), 
                                 ELit ((NL (0x04)) :L U256)]]),
              [r_id] ::= (CALL b_mload_id [EId xx_id])] END)
          ] END)])
        DEFAULT (Some (BEGIN[[r_id] ::= CALL f4_id [EId xx_id]]END) )
      ]END, [], (get_func_values f3_func)@(get_func_values f4_func), None)])
           gs0_ex1 CKDummy) # [])"

(*E27 --- same code as E26, but with gas exhaustion*)
definition gstk_E27 :: gstack where
  "gstk_E27 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256), (r_id, U256)],
        SWITCH(EId xx_id) 
        CASES([(((NL 0) :L U256), BEGIN [
            IF (CALL f3_id []) THEN (
            BEGIN [
              (CALL b_mstore_id [EId xx_id,
                  CALL b_exp_id [ELit ((NL (0x02)) :L U256), 
                                 ELit ((NL (0x04)) :L U256)]]),
              [r_id] ::= (CALL b_mload_id [EId xx_id])] END)
          ] END)])
        DEFAULT (Some (BEGIN[[r_id] ::= CALL f4_id [EId xx_id]]END) )
      ]END, [], (get_func_values f3_func)@(get_func_values f4_func), None)])
            (gs0_ex1\<lparr> gas_of := 78 \<rparr>) CKDummy) # [])"

(*E28 --- same code as E26, but with overflow of words stack*)
definition gstk_E28 :: gstack where
  "gstk_E28 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256), (r_id, U256)],
        SWITCH(EId xx_id) 
        CASES([(((NL 0) :L U256), BEGIN [
            IF (CALL f3_id []) THEN (
            BEGIN [
              (CALL b_mstore_id [EId xx_id,
                  CALL b_exp_id [ELit ((NL (0x02)) :L U256), 
                                 ELit ((NL (0x04)) :L U256)]]),
              [r_id] ::= (CALL b_mload_id [EId xx_id])] END)
          ] END)])
        DEFAULT (Some (BEGIN[[r_id] ::= CALL f4_id [EId xx_id]]END) )
      ]END, [], (get_func_values f3_func)@(get_func_values f4_func), None)])
            (gs0_ex1\<lparr> ct_of := 1021 \<rparr>) CKDummy) # [])"

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
definition gstk_E29 :: gstack where
  "gstk_E29 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256)] ::- ELit ((NL (0x01)) :L U256),
        VAR [(r_id, U256)] ::- EId xx_id, 
        SWITCH(EId xx_id) 
        CASES([(((NL 1) :L U256), BEGIN [
            IF (CALL f3_id []) THEN (
            BEGIN [
              FOR (BEGIN [(VAR [(k_id, U256)] ::- ELit ((NL 0) :L U256))] END) 
              (CALL b_gt_id [EId xx_id, EId k_id]) 
              (BEGIN [([k_id] ::= CALL b_add_id [ID k_id, ELit ((NL 1) :L U256)])] END) 
              (BEGIN [
                 [(r_id)] ::= CALL b_add_id [ID r_id, CALL f1_id [EId k_id, ELit ((NL 1) :L U256)]]
               ] END)
            ] END)
          ] END)])
        DEFAULT (Some (BEGIN[[r_id] ::= ELit ((NL (0x0)) :L U256)]END) )
      ]END, [], (get_func_values f3_func)@(get_func_values f1_func), None)])
           gs0_ex1 CKDummy) # [])"

(*E30 --- same code as E29, but with gas exhaustion*)
definition gstk_E30 :: gstack where
  "gstk_E30 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256)] ::- ELit ((NL (0x01)) :L U256),
        VAR [(r_id, U256)] ::- EId xx_id, 
        SWITCH(EId xx_id) 
        CASES([(((NL 1) :L U256), BEGIN [
            IF (CALL f3_id []) THEN (
            BEGIN [
              FOR (BEGIN [(VAR [(k_id, U256)] ::- ELit ((NL 0) :L U256))] END) 
              (CALL b_gt_id [EId xx_id, EId k_id]) 
              (BEGIN [([k_id] ::= CALL b_add_id [ID k_id, ELit ((NL 1) :L U256)])] END) 
              (BEGIN [
                 [(r_id)] ::= CALL b_add_id [ID r_id, CALL f1_id [EId k_id, ELit ((NL 1) :L U256)]]
               ] END)
            ] END)
          ] END)])
        DEFAULT (Some (BEGIN[[r_id] ::= ELit ((NL (0x0)) :L U256)]END) )
      ]END, [], (get_func_values f3_func)@(get_func_values f1_func), None)])
           (gs0_ex1\<lparr> gas_of := 180 \<rparr>) CKDummy) # [])"

(*E31 --- same code as E29, but with overflow of words stack*)
definition gstk_E31 :: gstack where
  "gstk_E31 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256)] ::- ELit ((NL (0x01)) :L U256),
        VAR [(r_id, U256)] ::- EId xx_id, 
        SWITCH(EId xx_id) 
        CASES([(((NL 1) :L U256), BEGIN [
            IF (CALL f3_id []) THEN (
            BEGIN [
              FOR (BEGIN [(VAR [(k_id, U256)] ::- ELit ((NL 0) :L U256))] END) 
              (CALL b_gt_id [EId xx_id, EId k_id]) 
              (BEGIN [([k_id] ::= CALL b_add_id [ID k_id, ELit ((NL 1) :L U256)])] END) 
              (BEGIN [
                 [(r_id)] ::= CALL b_add_id [ID r_id, CALL f1_id [EId k_id, ELit ((NL 1) :L U256)]]
               ] END)
            ] END)
          ] END)])
        DEFAULT (Some (BEGIN[[r_id] ::= ELit ((NL (0x0)) :L U256)]END) )
      ]END, [], (get_func_values f3_func)@(get_func_values f1_func), None)])
           (gs0_ex1\<lparr> ct_of := 1020 \<rparr>) CKDummy) # [])"

(*E32 --- (xx=0, r=0) \<rightarrow>* (xx=3, r=4)
  let xx, r
  switch add(xx, 1)
  default
  {
      xx,r := f()
  }
*)
definition gstk_E32 :: gstack where
  "gstk_E32 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256), (r_id, U256)],
        SWITCH(CALL b_add_id [ID xx_id, ELit ((NL 1) :L U256)]) 
        CASES([])
        DEFAULT (Some (BEGIN[[xx_id, r_id] ::= CALL f_id []]END) )
      ]END, [], (get_func_values (Blk [f_func])), None)])
            gs0_ex1 CKDummy) # [])"

(*E33 --- same code as E32, but with gas exhaustion*)
definition gstk_E33 :: gstack where
  "gstk_E33 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256), (r_id, U256)],
        SWITCH(CALL b_add_id [ID xx_id, ELit ((NL 1) :L U256)]) 
        CASES([])
        DEFAULT (Some (BEGIN[[xx_id, r_id] ::= CALL f_id []]END) )
      ]END, [], (get_func_values (Blk [f_func])), None)])
            (gs0_ex1\<lparr> gas_of := 16 \<rparr>) CKDummy) # [])"

(*E34 --- same code as E32, but with overflow of words stack*)
definition gstk_E34 :: gstack where
  "gstk_E34 = ((GFrmNormal ([LFrm_B (
      BEGIN[
        VAR [(xx_id, U256), (r_id, U256)],
        SWITCH(CALL b_add_id [ID xx_id, ELit ((NL 1) :L U256)]) 
        CASES([])
        DEFAULT (Some (BEGIN[[xx_id, r_id] ::= CALL f_id []]END) )
      ]END, [], (get_func_values (Blk [f_func])), None)])
            (gs0_ex1\<lparr> ct_of := 1021 \<rparr>) CKDummy) # [])"

(*E35 --- same code as E32, but with count error*)




(* 
  - (L1 --- L10) : about logic built-in functions.
*)

(*L1 ---  (b=false, a=0)
      h := lor(b, eq(a,mul(0,3)))*)
definition gstk_L1 :: gstack where
  "gstk_L1 = ((GFrmNormal ([LFrm_E (([h_id] ::= (CALL b_lor_id [EId b_id, (CALL b_eq_id [EId a_id, 
                (CALL b_mul_id [EImLit ((NL 0) :L U256), EImLit ((NL 3) :L U256)])])])), 
                    ls_ex_b0@ls_ex_h0@ls_ex_a0, [])])
                       gs0_ex1 CKDummy) # [])"

(*L2 --- (b=false, a=0)
    h := land(b, lt(a,3))*)
definition gstk_L2 :: gstack where
  "gstk_L2 = ((GFrmNormal ([LFrm_E (([h_id]::=(CALL b_land_id [EId b_id,
                 (CALL b_lt_id [EId a_id, EImLit ((NL (3)) :L U256)])])), ls_ex_b0@ls_ex_h0@ls_ex_a0,
                    [])]) gs0_ex1 CKDummy) # [])"

(*L3 --- (b=false, x=0)
       h := lxor(b,gt(x,2))*)
definition gstk_L3 :: gstack where
  "gstk_L3 = ((GFrmNormal ([LFrm_E (([h_id]::=(CALL b_lxor_id [EId b_id,
                 (CALL b_gt_id [EId x_id, EImLit ((NL 2) :L U256)])])), ls_ex_b0@ls_ex_h0@ls_ex_x0, 
                   [])]) gs0_ex1 CKDummy) # [])"

(*L4 --- (b=false) 
      h := lnot(b)*)
definition gstk_L4 :: gstack where
  "gstk_L4 = ((GFrmNormal ([LFrm_E (([h_id] ::= (CALL b_lnot_id [EId b_id])), 
                  ls_ex_h0@ls_ex_b0, [])]) gs0_ex1 CKDummy) # [])"

(*L5 --- (b=false) \<rightarrow>* (b=true)
  let b
  b := lor(f3(), b)
*)
definition gstk_L5 :: gstack where 
  "gstk_L5 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_lor_id
                        [(CALL f3_id []),EId b_id])]END,
          [], (get_func_values f3_func), None)]) gs0_ex1 CKDummy) # []"

(*L6 --- same code as L5, but with gas exhaustion*)
definition gstk_L6 :: gstack where 
  "gstk_L6 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_lor_id
                        [(CALL f3_id []),EId b_id])]END,
          [], (get_func_values f3_func), None)]) 
            (gs0_ex1\<lparr> gas_of := 51 \<rparr>) CKDummy) # []"

(*L7  --- same code as L5, but with overflow of words stack*)
definition gstk_L7 :: gstack where 
  "gstk_L7 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_lor_id
                        [(CALL f3_id []),EId b_id])]END,
          [], (get_func_values f3_func), None)]) 
            (gs0_ex1\<lparr> ct_of := 1022 \<rparr>) CKDummy) # []"

(*L8 --- (b=false) \<rightarrow>* (b=true)
  let b
  b := lxor(f3(), not(f3()))
*)
definition gstk_L8 :: gstack where 
  "gstk_L8 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_lxor_id
                        [(CALL f3_id []), (CALL b_lnot_id [CALL f3_id []])])]END,
          [], (get_func_values f3_func), None)]) gs0_ex1 CKDummy) # []"

(*L9 --- same code as L8, but with gas exhaustion*)
definition gstk_L9 :: gstack where 
  "gstk_L9 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_lxor_id
                        [(CALL f3_id []), (CALL b_lnot_id [CALL f3_id []])])]END,
          [], (get_func_values f3_func), None)])  
            (gs0_ex1\<lparr> gas_of := 51 \<rparr>) CKDummy) # []"

(*L10 --- same code as L8, but with overflow of words stack*)
definition gstk_L10 :: gstack where 
  "gstk_L10 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_lxor_id
                        [(CALL f3_id []), (CALL b_lnot_id [CALL f3_id []])])]END,
          [], (get_func_values f3_func), None)])  
            (gs0_ex1\<lparr> ct_of := 1022 \<rparr>) CKDummy) # []"




(* 
  - (A1 --- A26) : about arithmetic built-in functions.
*)

(*A1: (x=20) 
      arithmetic -- x := add(x,add(3,2))
*)
definition fb_expr_11 :: expr where
  "fb_expr_11 = ([x_id] ::= (CALL b_add_id [EId x_id, (CALL b_add_id [EImLit ((NL 3) :L U256), EImLit ((NL 2) :L U256)])]))"

definition gstk_A1 :: gstack where
  "gstk_A1 = ((GFrmNormal 
        ([LFrm_E (fb_expr_11, ls_ex_x1, [])]) gs0_ex1 CKDummy) # [])"

(*A2 --- (x=20)
       x := sub(x,sub(3,2)) *)
definition fb_expr0 :: expr where
  "fb_expr0 = ([x_id] ::= (CALL b_sub_id [EId x_id, (CALL b_sub_id [EImLit ((NL 3) :L U256), EImLit ((NL 2) :L U256)])]))"

definition gstk_A2 :: gstack where
  "gstk_A2 = ((GFrmNormal 
        ([LFrm_E (fb_expr0, ls_ex_x1, [])]) gs0_ex1 CKDummy) # [])"

(*A3 ---  (x=20)
      mul(x,mul(3,2))*)
definition gstk_A3 :: gstack where
  "gstk_A3 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_mul_id [EId x_id, 
                 (CALL b_mul_id [EImLit ((NL 3) :L U256), EImLit ((NL 2) :L U256)])])),
                   ls_ex_x1, [])]) gs0_ex1 CKDummy) # [])"

(*A4 : (x=20)
      arithmetic --- aa := sdiv(x,-2) *)
definition gstk_A4 :: gstack where
  "gstk_A4 = ((GFrmNormal 
        ([LFrm_E (([aa_id] ::= (CALL b_sdiv_id [EId x_id, EImLit ((NL (-2)) :L S256)])),
           ls_ex_x1@ls_ex_aa, [])]) gs0_ex1 CKDummy) # [])"

(*A5 : (x=20)
      arithmetic --- x := div(x,div(2,2)) *)
definition gstk_A5 :: gstack where
  "gstk_A5 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_div_id [EId x_id,
       (CALL b_div_id [EImLit ((NL (2)) :L U256), EImLit ((NL (2)) :L U256)])])),
           ls_ex_x1, [])]) gs0_ex1 CKDummy) # [])"

(*A6 ---  (x=20) 
      x := mod(x,3)*)
definition gstk_A6 :: gstack where
  "gstk_A6 = ((GFrmNormal 
        ([LFrm_E (([x_id] ::= (CALL b_mod_id [EId x_id, EImLit ((NL (3)) :L U256)])),
             ls_ex_x1, [])]) gs0_ex1 CKDummy) # [])"

(*A7 ---  (x=20)
      s := smod(x,-3)*)
definition gstk_A7 :: gstack where
  "gstk_A7 = ((GFrmNormal 
        ([LFrm_E (([s_id] ::= (CALL b_smod_id [EId x_id, EImLit ((NL (-3)) :L S256)])),
             ls_ex_x1@ls_ex_s0, [])]) gs0_ex1 CKDummy) # [])"

(*A8 --- (x=20)
    x := exp(x,2) *)
definition gstk_A8 :: gstack where
  "gstk_A8 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_exp_id [EId x_id, 
                  EImLit ((NL 2) :L U256)])), 
                  ls_ex_x1, [])]) gs0_ex1 CKDummy) # [])"

(*A9 --- (x=20, a=0) 
      addmod -- x := addmod(x,a,3) *)
definition gstk_A9 :: gstack where
  "gstk_A9 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_addmod_id [(EId x_id), 
                  (EId a_id), ( EImLit ((NL 3) :L U256))])), ls_ex20, [])]) 
                gs0_ex1 CKDummy) # [])"

(*A10 --- (x=20, a=0) 
      x := mulmod(x,a,3)*)
definition gstk_A10 :: gstack where
  "gstk_A10 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_mulmod_id [(EId x_id),
                  (EId a_id), (EImLit ((NL 3) :L U256))])), ls_ex20, []
                   )]) gs0_ex1 CKDummy) # [])"

(*A11 :   (x=0)
    comparison -- h := gt(x,sub(6,4))*)
definition gstk_A11 :: gstack where
  "gstk_A11 = ((GFrmNormal ([LFrm_E (([h_id] ::= (CALL b_gt_id [EId x_id,
                (CALL b_sub_id [EImLit ((NL 6) :L U256), EImLit ((NL 4) :L U256)])])), 
                  ls_ex_x0@ls_ex_h0, [])]) gs0_ex1 CKDummy) # [])"

(*A12 --- (s=0)
      h := sgt(s,-2*)
definition gstk_A12 :: gstack where
  "gstk_A12 = ((GFrmNormal ([LFrm_E (([h_id] ::= (CALL b_sgt_id [EId s_id, 
                  EImLit ((NL (-2)) :L S256)])), ls_ex_s0@ls_ex_h0,
                     [])]) gs0_ex1 CKDummy) # [])"

(*A13 --- (a=0)
       h := lt(a,3)*)
definition gstk_A13 :: gstack where
  "gstk_A13 = ((GFrmNormal ([LFrm_E ([h_id] ::= (CALL b_lt_id [EId a_id,
                 EImLit ((NL (3)) :L U256)]), ls_ex_a0@ls_ex_h0,
                   [])]) gs0_ex1 CKDummy) # [])"

(*A14 --- (a=0)
       h := slt(a,-3)*)
definition gstk_A14 :: gstack where
  "gstk_A14 = ((GFrmNormal ([LFrm_E (([h_id] ::= (CALL b_slt_id [EId a_id,
                 EImLit ((NL (-3)) :L S256)])), ls_ex_a0@ls_ex_h0,
                   [])]) gs0_ex1 CKDummy) # [])"

(*A15 --- (a=0)
       h := eq(a,mul(0,3))*)
definition gstk_A15 :: gstack where
  "gstk_A15 = ((GFrmNormal ([LFrm_E (([h_id] ::= (CALL b_eq_id [EId a_id,
                 (CALL b_mul_id [EImLit ((NL 0) :L U256), EImLit ((NL 3) :L U256)])])), 
                   ls_ex_a0@ls_ex_h0, [])]) gs0_ex1 CKDummy) # [])"

(*A16 --- (x=20) 
       x := and(x,add(3,4))*)
definition gstk_A16 :: gstack where
  "gstk_A16 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_and_id [EId x_id, 
                 (CALL b_add_id [EImLit ((NL 3) :L U256), EImLit ((NL 4) :L U256)])])), 
                  ls_ex_x1@ls_ex_h0, [])]) gs0_ex1 CKDummy) # [])"

(*A17 ---   (a=6)
       x := not(a)*)
value "eval_opbuiltin gs0_ex1 Not [NL 6]"
definition gstk_A17 :: gstack where
  "gstk_A17 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_not_id [EId a_id])), 
                 ls_ex_a1@ls_ex_x0, [])]) gs0_ex1 CKDummy) # [])"

(*A18 --- (x=0)
      iszero -- h := iszero(x) *)
definition gstk_A18 :: gstack where
  "gstk_A18 = ((GFrmNormal ([LFrm_E (([h_id] ::= (CALL b_iszero_id [EId x_id])),
                     ls_ex_x0@ls_ex_h0, [])]) gs0_ex1 CKDummy) # [])"

(*A19 --- (a=6)
      x := shl(a,div(3,1))*)
definition gstk_A19 :: gstack where
  "gstk_A19 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_shl_id [EId a_id,
                 (CALL b_div_id [EImLit ((NL (3)) :L U256), EImLit ((NL (1)) :L U256)])])), 
                   ls_ex_a1@ls_ex_x0, [])]) gs0_ex1 CKDummy) # [])"

(*A20 ---  (a=6) \<rightarrow>* (x=0)
      x := shr(a,2)*)
definition gstk_A20 :: gstack where
  "gstk_A20 = ((GFrmNormal ([LFrm_E (([x_id] ::= (CALL b_shr_id [EId a_id, 
                  EImLit ((NL (2)) :L U256)])), ls_ex_a1@ls_ex_x0, []
                    )]) gs0_ex1 CKDummy) # [])"

(*A21 ---  x \<rightarrow> (x=115792089237316195423570985008687907853269984665640564039457584007913129639932)
      x := sar(2,-16)*)
definition gstk_A21 :: gstack where
  "gstk_A21 = ((GFrmNormal ([LFrm_E ((VAR [(x_id, U256)] ::- (CALL b_sar_id [EImLit ((NL (2)) :L U256), 
                  EImLit ((NL (-16)) :L S256)])), [], [] 
                    )]) gs0_ex1 CKDummy) # [])"

(*A22 --- (x=0)  \<rightarrow>* (x=4095)
      let x := or(0xfff,0xf0f)*)
definition gstk_A22 :: gstack where
  "gstk_A22 = ((GFrmNormal ([LFrm_E ((VAR [(x_id, U256)] ::- (CALL b_or_id [EImLit ((NL (0xfff)) :L U256), 
                  EImLit ((NL (0xf0f)) :L U256)])), [], [] 
                    )]) gs0_ex1 CKDummy) # [])"

(*A23 --- (x=0) 
      let x := xor(0xfff,0xf0f)*)
definition gstk_A23 :: gstack where
  "gstk_A23 = ((GFrmNormal ([LFrm_E ((VAR [(x_id, U256)] ::- (CALL b_xor_id [EImLit ((NL (0xfff)) :L U256), 
                  EImLit ((NL (0xf0f)) :L U256)])), [], [] 
                    )]) gs0_ex1 CKDummy) # [])"

(*A24 --- (b=false) \<rightarrow>* (b=true)
  let b
  b := gt(f1(3, 9), f4(2))
*)
definition gstk_A24 :: gstack where 
  "gstk_A24 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_gt_id
                        [(CALL f1_id [ELit ((NL (0x03)) :L U256), ELit ((NL (0x09)) :L U256)]),
                         (CALL f4_id [ELit ((NL (0x02)) :L U256)])])]END,
          [], (get_func_values f1_func)@(get_func_values f4_func), None)]) gs0_ex1 CKDummy) # []"

(*A25 --- same code as A24, but with gas exhaustion*)
definition gstk_A25 :: gstack where 
  "gstk_A25 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_gt_id
                        [(CALL f1_id [ELit ((NL (0x03)) :L U256), ELit ((NL (0x09)) :L U256)]),
                         (CALL f4_id [ELit ((NL (0x02)) :L U256)])])]END,
          [], (get_func_values f1_func)@(get_func_values f4_func), None)]) 
           (gs0_ex1\<lparr> gas_of := 70 \<rparr>) CKDummy) # []"

(*A26 --- same code as A24, but with overflow of words stack*)
definition gstk_A26 :: gstack where 
  "gstk_A26 = (GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(b_id, Bool)],
                 [(b_id)] ::= (CALL b_gt_id
                        [(CALL f1_id [ELit ((NL (0x03)) :L U256), ELit ((NL (0x09)) :L U256)]),
                         (CALL f4_id [ELit ((NL (0x02)) :L U256)])])]END,
          [], (get_func_values f1_func)@(get_func_values f4_func), None)]) 
           (gs0_ex1\<lparr> ct_of := 1022 \<rparr>) CKDummy) # []"




(*
   - (M1 --- M7) : about memory and storage built-in functions.
*)

(*M1 ---
  {  mstore(0x01, 11289525020298692601998108039226097635691122580326809888208074282503241728)
    x := mload(0x01)   
  }
*)
definition gstk_M1 :: gstack where
  "gstk_M1 = ((GFrmNormal ([LFrm_B (BEGIN[(CALL b_mstore_id [EImLit ((NL (0x01)) :L U256),
                    EImLit ((NL (11289525020298692601998108039226097635691122580326809888208074282503241728)) :L U256)]),
                    [x_id] ::= (CALL b_mload_id [EImLit ((NL (0x01)) :L U256)])]END,
                  ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*M2 ---
     mstore8(0x01,0x11)
    x := mload(0x01)  
*)
definition gstk_M2 :: gstack where
  "gstk_M2 = ((GFrmNormal ([LFrm_B
            (BEGIN[(CALL b_mstore8_id [EImLit ((NL (0x01)) :L U256), EImLit ((NL (0x11)) :L U256)]),
                   [x_id] ::= (CALL b_mload_id [EImLit ((NL (0x01)) :L U256)])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*M3 ---
     sstore(0x01,0x11)
    x := sload(0x01)  
*)
definition gstk_M3 :: gstack where
  "gstk_M3 = ((GFrmNormal 
        ([LFrm_B (BEGIN[(CALL b_sstore_id [EImLit ((NL (0x01)) :L U256),EImLit ((NL (0x11)) :L U256)]),
                   [x_id] ::= (CALL b_sload_id [EImLit ((NL (0x01)) :L U256)])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*M4 ---
  { 
    a1 := msize()
  }
*)
definition gstk_M4 :: gstack where
  "gstk_M4 = ((GFrmNormal ([LFrm_B (BEGIN [([a1_id]::= CALL b_msize_id [])] END ,
                     [(a1_id, ((NL 0) :L U256))], [], None)]) gs1_bfun CKDummy) # [])"

(*M5 --- (xx=0) \<rightarrow>* (xx=9)
  let xx
  if f3() {
    mstore(0x01, f2(exp(2,2),5))
    xx := mload(0x01)
  }
*)
definition gstk_M5 :: gstack where
  "gstk_M5 = (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)], 
          IF (CALL f3_id []) THEN (
            BEGIN [
              (CALL b_mstore_id [ELit ((NL (0x01)) :L U256),
                  CALL f2_id [CALL b_exp_id [ELit ((NL (0x02)) :L U256), 
                                            ELit ((NL (0x02)) :L U256)], 
                              ELit ((NL (0x05)) :L U256)]]),
              [xx_id] ::= (CALL b_mload_id
                        [ELit ((NL (0x01)) :L U256)])] END)] 
         END),
         [], (get_func_values f3_func)@(get_func_values f2_func), None)] gs0_ex1 CKDummy
    ) # []"

(*M6 --- same code as M5, but with gas exhaustion*)
definition gstk_M6 :: gstack where
  "gstk_M6 = (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)], 
          IF (CALL f3_id []) THEN (
            BEGIN [
              (CALL b_mstore_id [ELit ((NL (0x01)) :L U256),
                  CALL f2_id [CALL b_exp_id [ELit ((NL (0x02)) :L U256), 
                                            ELit ((NL (0x02)) :L U256)], 
                              ELit ((NL (0x05)) :L U256)]]),
              [xx_id] ::= (CALL b_mload_id
                        [ELit ((NL (0x01)) :L U256)])] END)] 
         END),
         [], (get_func_values f3_func)@(get_func_values f2_func), None)] 
           (gs0_ex1\<lparr> gas_of := 48 \<rparr>) CKDummy
    ) # []"

(*M7 --- same code as M5, but with overflow of words stack*)
definition gstk_M7 :: gstack where
  "gstk_M7 = (GFrmNormal 
      [LFrm_B (
        (BEGIN [
          VAR [(xx_id, U256)], 
          IF (CALL f3_id []) THEN (
            BEGIN [
              (CALL b_mstore_id [ELit ((NL (0x01)) :L U256),
                  CALL f2_id [CALL b_exp_id [ELit ((NL (0x02)) :L U256), 
                                            ELit ((NL (0x02)) :L U256)], 
                              ELit ((NL (0x05)) :L U256)]]),
              [xx_id] ::= (CALL b_mload_id
                        [ELit ((NL (0x01)) :L U256)])] END)] 
         END),
         [], (get_func_values f3_func)@(get_func_values f2_func), None)]
           (gs0_ex1\<lparr> ct_of := 1022 \<rparr>) CKDummy
    ) # []"




(* 
  - (C1 --- C24) : about execution control built-in functions. 
*)
definition zero :: expr where "zero = EImLit ((NL 0) :L U256)"

definition callee_blk_ex2 :: "block" where 
 "
  callee_blk_ex2 = (
    BEGIN 
      [VAR [(-121, Bool)]]
    END
  )
 "

definition callee_blk_ex3 :: "block" where 
 "
  callee_blk_ex3 = (
    BEGIN [
      EVarDecl [(xx_id, U256)]
          (CALL b_call_id [EImLit ((NL 1000000) :L U256), EImLit ((NL 0x1) :L U256), zero, 
                           zero, zero, zero, zero])
    ] END
  )
 "

definition callee_account_ex2  :: "account"  where 
  "callee_account_ex2 = \<lparr>
    code_of = Some callee_blk_ex2,
    store_of = (\<lambda>x . (case x of _ => (0x0 :: (256 word)))),
    bal_of = (0x0 :: 256 word),
    nonce_of = (0x0 :: 256 word)
  \<rparr>"

definition callee_account_ex3  :: "account"  where 
  "callee_account_ex3 = \<lparr>
    code_of = Some callee_blk_ex3,
    store_of = (\<lambda>x . (case x of _ => (0x0 :: (256 word)))),
    bal_of = (0x0 :: 256 word),
    nonce_of = (0x0 :: 256 word)
  \<rparr>"

definition gs0_ex2 :: gstate where 
  "gs0_ex2 = 
  \<lparr>
    addr_of = 0x0,
    saddr_of = 0x0, 
    money_of = (0xff :: 256 word), 
    input_of = [(0x0 :: 8 word), (0x0 :: 8 word)], 
    mem_of = (\<lambda>x. 0x0), 
    naws_of = 0, 
    gas_of = 3000000, 
    ct_of = 10,
    accs_of = (\<lambda>x. (if x = (0x1::address) then 
                      (Some callee_account_ex2)
                    else
                      (Some empty_account))), 
    refund_of = (0x0 :: 256 word), 
    logs_of = [], 
    ss_of = {}
  \<rparr>"

definition gs0_ex3 :: gstate where 
  "gs0_ex3 = 
  \<lparr>
    addr_of = 0x0,
    saddr_of = 0x0, 
    money_of = (0xff :: 256 word), 
    input_of = [(0x0 :: 8 word), (0x0 :: 8 word)], 
    mem_of = (\<lambda>x. 0x0), 
    naws_of = 0, 
    gas_of = 30000000, 
    ct_of = 10,
    accs_of = (\<lambda>x. (if x = (0x1::address) then 
                      (Some callee_account_ex3)
                    else
                      (Some empty_account))), 
    refund_of = (0x0 :: 256 word), 
    logs_of = [], 
    ss_of = {}
  \<rparr>"

definition main_blk_ex2 :: block where 
  "main_blk_ex2 = 
    BEGIN 
      [
        EVarDecl [(-122, U256)]
          (CALL b_call_id [EImLit ((NL 1000) :L U256), EImLit ((NL 0x1) :L U256), zero, 
                           zero, zero, zero, zero])
      ] 
    END
  " 

definition main_blk_ex3 :: block where 
  "main_blk_ex3 = 
    BEGIN 
      [
        EVarDecl [(-122, U256)]
          (CALL b_call_id [EImLit ((NL 1000000) :L U256), EImLit ((NL 0x1) :L U256), zero, 
                           zero, zero, zero, zero])
      ] 
    END
  " 

(* simplest example for external calls*)
(*C1 ---
    {
      u256 (-122) := call(1000, 0x1, 0, 0, 0, 0, 0)
     }
    callee{
        var bool (-121)
      }
*)

definition gstk_C1 where 
  "gstk_C1 = GFrmNormal ([LFrm_B (main_blk_ex2, [], 
                get_func_values main_blk_ex2 @ [], None)]) gs0_ex2 CKDummy"

(*C2 ---
    {     
       a := call(10,0,30,0,32,23,32) 
       xx := 99       
      callee{ }
    }
  callee{ }
*)
definition literal_1 :: "expr list" where 
  "literal_1 = ([(EImLit ((NL 10) :L U256)),(EImLit ((NL 0x0) :L U256)),(EImLit ((NL 30) :L U256)),
(EImLit ((NL 0) :L U256)),(EImLit ((NL 32) :L U256)),(EImLit ((NL 23) :L U256)),(EImLit ((NL 32) :L U256))])"

definition gstk_C2 :: gstack where
  "gstk_C2 = [(GFrmNormal ([(LFrm_B ((BEGIN [([a_id] ::= (CALL b_call_id literal_1)),
                                               [xx_id] ::= (EImLit ((NL 99) :L U256))] END), 
                                     ls_ex_a0@[(xx_id, ((NL 0) :L U256))], 
                        [], None))]) gs0_ex1 CKDummy)]"

(*C3 ---
    {
      xx := call(10,0,30,0,32,23,32))
      y := 400   
    }
     callee{ }
*)
definition gstk_C3 :: gstack where
  "gstk_C3 =  [(GFrmNormal [(LFrm_B (BEGIN[[xx_id]::=(CALL b_call_id literal_1), y_expr1] END, 
       ls_ex2, [], None))] gs1_bfun CKDummy)]"

(*C4 ---
    {
      xx := callcode(10,0,30,0,32,23,32))
      y := 400   
    }
    callcodeblk{ }
*)
definition gstk_C4 :: gstack where
  "gstk_C4 = [(GFrmNormal [(LFrm_B (BEGIN[([xx_id]::= CALL b_callcode_id literal_1), y_expr1] END, 
       ls_ex2, [], None))] gs1_bfun CKDummy)]"

(*C5 ---
   {
      xx := delegatecall(10,0,0,32,23,32)
      y := 400
   }
    delcallblk{ }
*)

definition literal_2 :: "expr list" where 
  "literal_2 = ([(EImLit ((NL 10) :L U256)),(EImLit ((NL 0x0) :L U256)),
(EImLit ((NL 0) :L U256)),(EImLit ((NL 32) :L U256)),(EImLit ((NL 23) :L U256)),(EImLit ((NL 32) :L U256))])"

definition gstk_C5 :: gstack where
"gstk_C5 = [(GFrmNormal [(LFrm_B (BEGIN[([xx_id] ::=(CALL b_delegatecall_id literal_2)), y_expr1] END, 
       ls_ex2, [], None))] gs1_bfun CKDummy)]"

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
definition gstk1_u :: gstack where
  "gstk1_u = ((GFrmNormal
        ([LFrm_B ((BEGIN [ ([h_id] ::= (EImLit (TL :L Bool))) ] END), 
                   ls_ex_h0, [], None) ]) gs0_ex1 CKDummy) # [])"

definition ck_ex_rev where "ck_ex_rev = CKCall 2000 0x0 0 0 0 0 0"

definition gstk_C6 :: gstack where
  "gstk_C6 = ((GFrmNormal ([LFrm_B ((BEGIN[([x_id] ::= (EImLit ((NL 4) :L U256))), 
                  (CALL b_revert_id [EId x_id, EImLit ((NL 2) :L U256)])]END), ls_ex_x0, 
                      [], None)]) gs1_bfun ck_ex_rev) 
                # gstk1_u)"

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
definition lstk3 :: lstack_frame where 
   "lstk3 = (LFrm_B ((Blk ([([x_id] ::= (EImLit ((NL 4) :L U256)))])), 
                ls_ex_x0, [], None ))"

definition ck_ex_ret where "ck_ex_ret = CKCall 2000 0x0 0 0 0 0 0"

definition gstk_C7 :: gstack where
  "gstk_C7 = ((GFrmNormal ((LFrm_B (BEGIN [(CALL b_return_id [EId x_id, 
                  EImLit ((NL 2) :L U256)])] END, ls_ex_x0, [], None)) 
                    # [lstk3]) gs1_bfun ck_ex_ret) # gstk1_u)"

(*C8 ---
   selfdestruct(1)
*)
definition gstk_C8 :: gstack where
  "gstk_C8 = ((GFrmNormal 
        ([LFrm_B (BEGIN[(CALL b_selfdestruct_id [EImLit ((NL (0x1)) :L U256)])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*C9 ---
   log0(0x1,32)
*)
definition gstk_C9 :: gstack where
  "gstk_C9 = ((GFrmNormal ([LFrm_B (BEGIN[(CALL b_log0_id [EImLit ((NL (0x1)) :L U256),
                    EImLit ((NL 0x20) :L U256)])]END, ls_ex_x0, [],
                      None)]) gs1_bfun CKDummy) # [])"

(*C10 ---
   log1(0x1,0x20,0x24 )
*)
definition gstk_C10 :: gstack where
  "gstk_C10 = ((GFrmNormal ([LFrm_B (BEGIN[(CALL b_log1_id [EImLit ((NL (0x1)) :L U256),
                    EImLit ((NL (0x20)) :L U256), EImLit ((NL (0x24)) :L U256)])]END, ls_ex_x0, [],
                      None)]) gs1_bfun CKDummy) # [])"

(*C11 ---
  log2(0x1,0x20,0x24,0x31)
*)
definition gstk_C11 :: gstack where
  "gstk_C11 = ((GFrmNormal ([LFrm_B (BEGIN[(CALL b_log2_id [EImLit ((NL (0x1)) :L U256),
                    EImLit ((NL (0x20)) :L U256), EImLit ((NL (0x24)) :L U256),
                    EImLit ((NL (0x31)) :L U256)])]END, ls_ex_x0, [],
                      None)]) gs1_bfun CKDummy) # [])"

(*C12 ---
  log3(0x1,0x20,0x24,0x31,0x3a)
*)
definition gstk_C12 :: gstack where
  "gstk_C12 = ((GFrmNormal ([LFrm_B (BEGIN[(CALL b_log3_id [EImLit ((NL (0x1)) :L U256),
                    EImLit ((NL (0x20)) :L U256), EImLit ((NL (0x24)) :L U256),
                    EImLit ((NL (0x31)) :L U256), EImLit ((NL (0x3a)) :L U256)])]END, ls_ex_x0, [],
                      None)]) gs1_bfun CKDummy) # [])"

(*C13 ---
  log4(0x1,0x20,0x24,0x31,0x3a,0x44)
*)
definition gstk_C13 :: gstack where
  "gstk_C13 = ((GFrmNormal ([LFrm_B (BEGIN[(CALL b_log4_id [EImLit ((NL (0x1)) :L U256),
                    EImLit ((NL (0x20)) :L U256), EImLit ((NL (0x24)) :L U256),
                    EImLit ((NL (0x31)) :L U256), EImLit ((NL (0x3a)) :L U256),
                    EImLit ((NL (0x44)) :L U256)])]END, ls_ex_x0, [],
                      None)]) gs1_bfun CKDummy) # [])"

(*C14 --- 
   invalid()
*)
definition gstk_C14 :: gstack where
  "gstk_C14 = ((GFrmNormal 
        ([LFrm_B (BEGIN[(CALL b_invalid_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*C15 ---
  stop()
*)
definition gstk_C15 :: gstack where
  "gstk_C15 = ((GFrmNormal 
        ([LFrm_B (BEGIN[(CALL b_stop_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"
                                     
(*C16 ---
    {
      xx := callcode(10,0,30,0,32,23,32))
      y := 400   
    }
     callcodeblk{ }
*)
definition gstk_C16 :: gstack where
  "gstk_C16 =  [(GFrmNormal [(LFrm_B (BEGIN[[xx_id]::=(CALL b_callcode_id literal_1), y_expr1] END, 
       ls_ex2, [], None))] gs0_ex1 CKDummy)]"

(*C17 --- same code as C16, but to_addr is None and eternal call successes.*)
definition gstk_C17 :: gstack where
  "gstk_C17 =  [(GFrmNormal [(LFrm_B (BEGIN[[xx_id]::=(CALL b_callcode_id literal_1), y_expr1] END, 
       ls_ex2, [], None))] 
        (gs1_bfun\<lparr> accs_of := (\<lambda>x. (if x = (0x0::address) then None else Some account1)) \<rparr>)
           CKDummy)]"
                      
(*C18 --- external call fails and gas exhaustion.
    {
      xx := delegatecall(10,0,0,32,23,32)
      y := 400   
    }
     delegatecallblk{ }
*)
definition gstk_C18 :: gstack where
  "gstk_C18 =  [(GFrmNormal [(LFrm_B (BEGIN[[xx_id]::=(CALL b_delegatecall_id literal_2), y_expr1] END, 
       ls_ex2, [], None))] (gs0_ex1\<lparr> gas_of := 6 \<rparr>) CKDummy)]"

(*C19 --- same code as C18, but to_addr is None*)
definition gstk_C19 :: gstack where
  "gstk_C19 =  [(GFrmNormal [(LFrm_B (BEGIN[[xx_id]::=(CALL b_delegatecall_id literal_2), y_expr1] END, 
       ls_ex2, [], None))]
         (gs1_bfun\<lparr> accs_of := (\<lambda>x. (if x = (0x0::address) then None else Some account1)) \<rparr>)
            CKDummy)]"

(*C20 --- with gas exhaustion
{
      xx := call(10,0,30,0,32,23,32))
      y := 400   
    }
     callee{ }
*)
definition gstk_C20 :: gstack where
  "gstk_C20 =  [(GFrmNormal [(LFrm_B (BEGIN[[xx_id]::=(CALL b_call_id literal_1), y_expr1] END, 
       ls_ex2, [], None))] (gs1_bfun\<lparr> gas_of := 4 \<rparr>) CKDummy)]"

(*C21 --- same code as C20, but to_addr is None*)
definition gstk_C21 :: gstack where
  "gstk_C21 =  [(GFrmNormal [(LFrm_B (BEGIN[[xx_id]::=(CALL b_call_id literal_1), y_expr1] END, 
       ls_ex2, [], None))] 
        (gs1_bfun\<lparr> accs_of := (\<lambda>x. (if x = (0x0::address) then None else Some account1)) \<rparr>)
           CKDummy)]"

(*C22 --- to_addr is None.
  selfdestruct(0)
*)
definition gstk_C22 :: gstack where
  "gstk_C22 = ((GFrmNormal 
    ([LFrm_B (BEGIN[(CALL b_selfdestruct_id [EImLit ((NL (0x0)) :L U256)])]END,
        ls_ex_x0, [], None)]) 
           (gs1_bfun\<lparr> accs_of := (\<lambda>x. (if x = (0x0::address) then None else Some account1)) \<rparr>)
             CKDummy) # [])"

(*C23 --- with overflow of call stacks.
    {
      u256 (-122) := call(10, 0x11, 0, 0, 0, 0, 0)
     }
    callee{
        var xx := call(10, 0x11, 0, 0, 0, 0, 0)
      }
*)
definition gstk_C23 where 
  "gstk_C23 = GFrmNormal ([LFrm_B (main_blk_ex3, [], 
                get_func_values main_blk_ex3 @ [], None)]) gs0_ex3 CKDummy"

(*C24 --- with overflow of call stacks.
    {
      u256 (-122) := callcode(10, 0x11, 0, 0, 0, 0, 0)
     }
    callee{
        var xx := call(10, 0x11, 0, 0, 0, 0, 0)
      }
*)
definition gstk_C24 where 
  "gstk_C24 = GFrmNormal ([LFrm_B (
    BEGIN 
      [
        EVarDecl [(-122, U256)]
          (CALL b_callcode_id [EImLit ((NL 1000000) :L U256), EImLit ((NL 0x1) :L U256), zero, 
                           zero, zero, zero, zero])
      ] 
    END, 
    [], get_func_values main_blk_ex3 @ [], None)]) gs0_ex3 CKDummy"




(*
  - (S1 --- S18) : about state queries built-in functions and other built-in functions.
*)

(*S1 --- 
    {
      a1 := balance(a1)
    }
*)
value "0xfff4 ::int"

definition gstk_S1 :: gstack where
  "gstk_S1 = ((GFrmNormal ([LFrm_B (BEGIN[([a1_id]::= CALL b_balance_id [EId a1_id])]END,
                   [(a1_id, ((NL 0) :L U256))], [], None)]) gs1_bfun CKDummy) # [])"

(*S2 --- 
    {
      a1 := caller()
    }
*)
value "eval_rbuiltin gs1_bfun Caller []"
value "0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c ::int"

definition gstk_S2 :: gstack where
  "gstk_S2 = ((GFrmNormal 
        ([LFrm_B (BEGIN[([a1_id]::= CALL b_caller_id [])]END,
               [(a1_id, ((NL 0) :L U256))], [], None)]) gs1_bfun CKDummy) # [])"

(*S3 --- 
    {
      a1 := callvalue()
    }
*)
value "0xffff ::int"

definition gstk_S3 :: gstack where
  "gstk_S3 = ((GFrmNormal 
        ([LFrm_B (BEGIN[([a1_id]::= CALL b_callvalue_id [])]END,
               [(a1_id, ((NL 0) :L U256))], [], None)]) gs1_bfun CKDummy) # [])"

(*S4 ---
    x := calldataload(0x1)
*)
definition gstk_S4 :: gstack where
  "gstk_S4 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_calldataload_id [EImLit ((NL (0x1)) :L U256)])]END,
               ls_ex_x0, [], None)]) gs0_ex1 CKDummy) # [])"

(*S5 ---
   x := address()
*)
value "eval_rbuiltin gs1_bfun Address []"

definition gstk_S5 :: gstack where
  "gstk_S5 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_address_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S6 --- (x=0) \<rightarrow>* (x=4)
    calldatacopy(0, 54, 33)
   x := calldatasize()
*)
definition gstk_S6 :: gstack where
  "gstk_S6 = ((GFrmNormal 
    ([LFrm_B (BEGIN[ 
     (CALL b_calldatacopy_id [EImLit ((NL (0x0)) :L U256),
           EImLit ((NL (0x36)) :L U256), EImLit ((NL (0x21)) :L U256)]),
      [x_id] ::= (CALL b_calldatasize_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S7 ---
   x := gas()
*)
definition gstk_S7 :: gstack where
  "gstk_S7 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_gas_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S8 ---
   x := origin()
*)
value "0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c ::int"

definition gstk_S8 :: gstack where
  "gstk_S8 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_origin_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S9 ---
   x := gasprice()
*)
value "0xa2 :: int"

definition gstk_S9 :: gstack where
  "gstk_S9 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_gasprice_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S10 ---
   x := coinbase()
*)
value "0x0e9281e9C6a0808672EAba6bd1220E144C9bb07a :: int"

definition gstk_S10 :: gstack where
  "gstk_S10 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_coinbase_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S11 ---
   x := number()
*)
definition gstk_S11 :: gstack where
  "gstk_S11 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_number_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S12 ---
   x := difficulty()
*)
definition gstk_S12 :: gstack where
  "gstk_S12 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_difficulty_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S13 ---
   x := timestamp()
*)
definition gstk_S13 :: gstack where
  "gstk_S13 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_timestamp_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"

(*S14 ---
   x := gaslimit()
*) 
value "0x1000 ::int"

definition gstk_S14 :: gstack where
  "gstk_S14 = ((GFrmNormal 
        ([LFrm_B (BEGIN[[x_id] ::= (CALL b_gaslimit_id [])]END,
               ls_ex_x0, [], None)]) gs1_bfun CKDummy) # [])"
 
(*S15 --- 
  { 
    x := keccak256(0, 32)
  }
*)
value "eval_rbuiltin gs0_ex1 Keccak256 [NL 0, NL 32]"

definition gstk_S15 :: gstack where
  "gstk_S15 = ((GFrmNormal ([LFrm_B (BEGIN[(VAR [(x_id, U256)] ::-
                    (CALL b_keccak256_id [EImLit ((NL (0)) :L U256), EImLit ((NL (32)) :L U256)])
                )]END, [], [], None)]) gs0_ex1 CKDummy) # [])"

(*S16 --- (xx=0) \<rightarrow>* (xx=131059)
  let xx
  xx := f1(balance(0), callvalue()) 
*)
definition gstk_S16 :: gstack where
  "gstk_S16 = ((GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(xx_id, U256)],
                 [(xx_id)] ::= (CALL f1_id
                        [(CALL b_balance_id [ELit ((NL (0x0)) :L U256)]), 
                          (CALL b_callvalue_id [])])]END,
          [], (get_func_values f1_func), None)]) gs1_bfun CKDummy) # [])"

(*S17 --- same code as S16, but with gas exhaustion*)
definition gstk_S17 :: gstack where
  "gstk_S17 = ((GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(xx_id, U256)],
                 [(xx_id)] ::= (CALL f1_id
                        [(CALL b_balance_id [ELit ((NL (0x0)) :L U256)]), 
                          (CALL b_callvalue_id [])])]END,
          [], (get_func_values f1_func), None)])
             (gs1_bfun\<lparr> gas_of := 8\<rparr>) CKDummy) # [])"

(*S18 --- same code as S16, but with overflow of words stack*)
definition gstk_S18 :: gstack where
  "gstk_S18 = ((GFrmNormal 
      ([LFrm_B (BEGIN[ 
                 VAR [(xx_id, U256)],
                 [(xx_id)] ::= (CALL f1_id
                        [(CALL b_balance_id [ELit ((NL (0x0)) :L U256)]), 
                          (CALL b_callvalue_id [])])]END,
          [], (get_func_values f1_func), None)])
             (gs1_bfun\<lparr> ct_of := 1022\<rparr>) CKDummy) # [])"




end
