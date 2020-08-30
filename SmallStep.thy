(******
Small-step semantics for Yul language
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

theory "SmallStep"
                                    
imports Syntax Typing "./utils/Keccak"

begin

(* the function values *)
datatype fvalue =
    FunctionV id0 "(id0 * type_name) list" "(id0 * type_name) list" block
  | OpBuiltinV "opbuiltin"
  | RBuiltinV " rbuiltin "
  | CallBuiltinV "callbuiltin"
  | HdRBuiltinV "hdrbuiltin"
  | WBuiltinV "wbuiltin"

(* we identify builtin functions via their ids *)
definition builtin_ctx :: "fvalue list_map" where (*'a \<Rightarrow> 'b option*)
  "builtin_ctx = 
    [
      (b_mload_id, (RBuiltinV MLoad)), 
      (b_msize_id, (RBuiltinV MSize)), 
      (b_sload_id, (RBuiltinV SLoad)), 
      (b_gas_id, (RBuiltinV Gas)), 
      (b_address_id, (RBuiltinV Address)),
      (b_balance_id, (RBuiltinV Balance)), 
      (b_calldataload_id, (RBuiltinV CalldataLoad)),
      (b_calldatasize_id, (RBuiltinV CalldataSize)),
      (b_callvalue_id, (RBuiltinV Callvalue)),
      (b_caller_id, (RBuiltinV Caller)), 
\<comment> \<open>      (b_codesize_id, (RBuiltinV CodeSize)), \<close>
\<comment> \<open>      (b_extcodesize_id, (RBuiltinV ExtCodeSize)), \<close>
      (b_keccak256_id, (RBuiltinV Keccak256)), 

      (b_difficulty_id, (HdRBuiltinV Difficulty)),
      (b_number_id, (HdRBuiltinV Number)),
      (b_timestamp_id, (HdRBuiltinV Timestamp)),
      (b_coinbase_id, (HdRBuiltinV CoinBase)),
      (b_gaslimit_id, (HdRBuiltinV GasLimit)),
      (b_gasprice_id, (HdRBuiltinV GasPrice)),
      (b_origin_id, (HdRBuiltinV Origin)),

      (b_call_id, (CallBuiltinV Call)),
      (b_callcode_id, (CallBuiltinV CallCode)),
      (b_delegatecall_id, (CallBuiltinV DelegateCall)),
      (b_return_id, (CallBuiltinV Return)),
      (b_revert_id, (CallBuiltinV Revert)),
      (b_selfdestruct_id, (CallBuiltinV Selfdestruct)), 
      (b_stop_id, (CallBuiltinV Stop)),
      (b_invalid_id, (CallBuiltinV Invalid)),

      (b_mstore_id, (WBuiltinV MStore)),
      (b_mstore8_id, (WBuiltinV MStore8)),
      (b_sstore_id, (WBuiltinV SStore)), 
      (b_calldatacopy_id, (WBuiltinV CalldataCopy)),  
      (b_log0_id, (WBuiltinV (Log 0))),
      (b_log1_id, (WBuiltinV (Log 1))),
      (b_log2_id, (WBuiltinV (Log 2))),
      (b_log3_id, (WBuiltinV (Log 3))), 
      (b_log4_id, (WBuiltinV (Log 4))), 
\<comment> \<open>      (b_pop_id, (WBuiltinV Pop)), \<close>

      \<comment> \<open>two\<close>
      (b_add_id, (OpBuiltinV Add)), 
      (b_sub_id, (OpBuiltinV Sub)), 
      (b_mul_id, (OpBuiltinV Mul)), 
      (b_sdiv_id, (OpBuiltinV SDiv)), 
      (b_div_id, (OpBuiltinV Div)), 
      (b_mod_id, (OpBuiltinV Mod)), 
      (b_smod_id, (OpBuiltinV SMod)),
      (b_exp_id, (OpBuiltinV Exp)), 
      (b_and_id, (OpBuiltinV And)), 
      (b_or_id, (OpBuiltinV Or)),
      (b_xor_id, (OpBuiltinV Xor)),
      (b_lt_id, (OpBuiltinV Lt)), 
      (b_slt_id, (OpBuiltinV SLt)), 
      (b_gt_id, (OpBuiltinV Gt)), 
      (b_sgt_id, (OpBuiltinV SGt)), 
      (b_eq_id, (OpBuiltinV Eq)), 
      (b_land_id, (OpBuiltinV LAnd)),   
      (b_lor_id, (OpBuiltinV LOr)), 
      (b_lxor_id, (OpBuiltinV LXor)),
      (b_shl_id, (OpBuiltinV Shl)), 
      (b_shr_id, (OpBuiltinV Shr)),  
      (b_sar_id, (OpBuiltinV Sar)),  
      (b_lnot_id, (OpBuiltinV LNot)), 
      (b_not_id, (OpBuiltinV Not)), 
      (b_iszero_id, (OpBuiltinV IsZero)),
      (b_mulmod_id, (OpBuiltinV MulMod)),
      (b_addmod_id, (OpBuiltinV AddMod))
  ]" 

value "(lm_dom builtin_fte) = (lm_dom builtin_ctx)"

datatype hole = Hole

(* no alternative for blocks since blocks are not expressions in the formalization *)
datatype ectx = 
    ECFunCall id0 "expr list" hole "literal list" 
  | ECVarDecl "(id0 * type_name) list" hole
  | ECAssg "id0 list" hole 
  | ECCond hole block
  | ECSwitch hole "(literal * block) list" "block option"

type_synonym lstate = "literal list_map"

type_synonym fstate = "fvalue list_map"

type_synonym cflag = "fvalue option"

datatype lstack_frame = 
  LFrm_E "expr \<times> lstate \<times> fstate" | 
  LFrm_B "block \<times> lstate \<times> fstate \<times> cflag" 
\<comment> \<open>the Boolean value indicates whether the stack frame is created due to a function call or not\<close>

type_synonym lstack = "lstack_frame list" 
type_synonym address = "160 word"

record log = 
  address_of :: address 
  args_of :: "(256 word) list" 
  mem_frag_of :: "(8 word) list"

(*
record trans_effect = 
  refund_of :: "256 word" \<comment> \<open>refund balance\<close>
  logs_of :: "log list" 
  suicides_of :: "address set" 
*)

record account = 
  code_of :: "block option"
  store_of :: "256 word \<Rightarrow> 256 word"
  bal_of :: "256 word" 
  nonce_of :: "256 word" 

(* We distinguish between the code for each account and the currently executing code.
   The former never contains any $'s. *)
 
record gstate = 
  addr_of :: address      (* current address *)
  saddr_of :: address     (* sender address *)
  money_of :: "256 word"  (* natural number represented by 256bits *)
  input_of :: "(8 word) list"
  mem_of :: "256 word \<Rightarrow> 8 word"
  naws_of :: "256 word"          (* number of active words in the memory *)
  gas_of :: "256 word"
  ct_of :: nat   (* record the size of word stack *)
  accs_of :: "address \<Rightarrow> (account option)" 
  refund_of :: "256 word" (* refund balance *)
  logs_of :: "log list" 
  ss_of :: "address set"  (* suicide set *)

datatype call_kind = 
  CKCall int int int int int int int | 
  CKDelCall int int int int int int | 
  CKCallCode int int int int int int int | 
  CKDummy

(* the stack frames of the global stack *) 
(* the byte list is for the returned data when an explicit call 
   to the builtin function return(offt, sz) is made *)
datatype gstack_frame = 
    GFrmNormal lstack gstate call_kind
  | GFrmExc call_kind
  | GFrmHalt gstate "(8 word) list" call_kind
  | GFrmCounterErr

type_synonym gstack = "(gstack_frame) list" 

record blk_header = 
  pheader_hash_of :: "256 word" 
  beneficiary_of :: address 
  difficulty_of :: "256 word" 
  number_of :: "256 word" 
  gas_limit_of :: "256 word" 
  time_stamp_of :: "256 word"

record trans_env = 
  oaddr_of :: address \<comment> \<open>address of the original transactor\<close>
  gprice_of :: "256 word" 
  bheader_of :: blk_header

fun eval_lit :: "expr \<Rightarrow> int option" where 
  "eval_lit (EImLit lit) = (
   case lit of 
     Literal TrueLiteral Boolean \<Rightarrow> Some 1
   | Literal FalseLiteral Boolean \<Rightarrow> Some 0
   | Literal (NumberLiteral i) type_name \<Rightarrow> 
      (if (in_range i type_name) then (Some i) else None)
   | _ \<Rightarrow> None
  )" | 
  "eval_lit _ = None"

fun valid :: "256 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool " where
  "valid gas_call cost ct = (gas_call \<ge> (word_of_int (int cost)) \<and> ct < 1024)"

fun valid_gas_cost :: "256 word \<Rightarrow> 256 word \<Rightarrow> bool " where
  "valid_gas_cost gas_call cost = (gas_call \<ge> cost)" 

value "(10 div 6) ::int"

definition Cmem :: "int \<Rightarrow> int \<Rightarrow> int" where 
  "Cmem aw aw' = 
    3 * (aw' - aw) + 
    ((aw' * aw') div 512) - ((aw * aw) div 512)
  "

value "Cmem (uint(26 :: 8 word)) 32"

fun hfill_e :: "ectx \<Rightarrow> expr \<Rightarrow> expr" where 
  "hfill_e (ECFunCall f el Hole ll) e = (
    case e of 
      (EList es) \<Rightarrow> EImFunCall f (el @ es @ (map EImLit ll))
    | _ \<Rightarrow> EImFunCall f (el @ [e] @ (map EImLit ll))
  )" |
  "hfill_e (ECVarDecl xs Hole) e = EVarDecl xs e" | 
  "hfill_e (ECAssg xs Hole) e = EAssg xs e" |
  "hfill_e (ECCond Hole blk) e = (
    case e of 
      (EList es) \<Rightarrow> ECond (es!0) blk 
    | _ \<Rightarrow> ECond e blk
  )" |
  "hfill_e (ECSwitch Hole brs blk_opt) e = (
    case e of 
      (EList es) \<Rightarrow> ESwitch (es!0) brs blk_opt
    |_ \<Rightarrow> ESwitch e brs blk_opt
  )"

(* THIS DEFINITION CAUSES ILL-FORMED ECond and ESwitch WITH ELIST IN THE CONDITIONAL PART 
   TO BE GENERATED, WHEN THERE ARE FUNCTION CALLS IN THE CONDITIONAL PART OF THESE CONSTRUCTS
fun hfill_e :: "ectx \<Rightarrow> expr \<Rightarrow> expr" where 
  "hfill_e (ECFunCall f el Hole ll) e = (
    case e of 
      (EList es) \<Rightarrow> EImFunCall f (el @ es @ (map EImLit ll)) 
    | _ \<Rightarrow> EImFunCall f (el @ [e] @ (map EImLit ll))
  )" |
  "hfill_e (ECVarDecl xs Hole) e = EVarDecl xs e" | 
  "hfill_e (ECAssg xs Hole) e = EAssg xs e" |
  "hfill_e (ECCond Hole blk) e = (ECond e blk)" |
  "hfill_e (ECSwitch Hole brs blk_opt) e = ESwitch e brs blk_opt"
*)

(* well-typedness assumed of contract for which the function is used *)
fun get_func_values :: "block \<Rightarrow> fvalue list_map" where 
  "get_func_values (Blk []) = []" | 
  "get_func_values (Blk ((EFunDef f ptl rtl e) # es')) = 
    [(f, FunctionV f ptl rtl e)] @ (get_func_values (Blk es'))" | 

  "get_func_values (Blk (_ # es')) = get_func_values (Blk es')"

fun get_mem_bytes :: "(256 word \<Rightarrow> 8 word) \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (8 word) list" where 
  "get_mem_bytes mem _ 0 = []" | 
  "get_mem_bytes mem offt (Suc sz') = 
      (mem ((word_of_int offt))) # (get_mem_bytes mem (offt+1) sz')"

definition lst_find_idx0 :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (nat \<times> bool)" where 
  "lst_find_idx0 idx0 lst f = 
    (foldl 
      (\<lambda>(cnt, brk) e. 
        if brk then (cnt, brk) else (if (f e) then (cnt, True) else (cnt+1, brk)))
      (idx0, False) lst)" 

value "lst_find_idx0 L [[1] ::= EImLit (TL:LBool), EImLit ((NL 3):L U256), 
                    EImLit (FL:LBool)] 
       (\<lambda>e. case e of EImLit _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition lst_find_idx :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (nat \<times> bool)" where 
  "lst_find_idx es f = lst_find_idx0 0 es f"

value "lst_find_idx [[0] ::= EImLit (TL:LBool), EImLit ((NL 3):L U256), 
                    EImLit (FL:LBool)] 
       (\<lambda>e. case e of EImLit _ \<Rightarrow> True | _ \<Rightarrow> False)"

value "take 3 [1::nat, 2, 3, 3, 2]"
value "take 4 [0::nat,1,5,2,4,4]"
value "drop 2 [1::nat, 2, 3, 3, 2]"
value "drop 5 [1::nat, 2, 3, 3, 2]"

fun aggr_ls :: "lstack \<Rightarrow> literal list_map" where 
  "aggr_ls ((LFrm_B (b, ls, fs, None)) # lstk') = (aggr_ls lstk') @ ls" |
  "aggr_ls ((LFrm_B (b, ls, fs, Some v)) # lstk') = ls" |
  "aggr_ls ((LFrm_E (e, ls, fs)) # lstk') = (aggr_ls lstk') @ ls" |
  "aggr_ls [] = []" 

fun aggr_fs :: "lstack \<Rightarrow> fvalue list_map" where 
  "aggr_fs ((LFrm_B (b, ls, fs, _)) # lstk') = (aggr_fs lstk') @ fs" | 
  "aggr_fs ((LFrm_E (e, ls, fs)) # lstk') = (aggr_fs lstk') @ fs" | 
  "aggr_fs [] = []" 

fun idx_id_in_ls :: "lstack \<Rightarrow> id0 \<Rightarrow> (nat \<times> bool)" where 
  "idx_id_in_ls lstk x = 
    lst_find_idx lstk 
      (\<lambda>lfrm. (case lfrm of 
                  (LFrm_B (_, ls, _, _)) \<Rightarrow> (x \<in> lm_dom ls) 
               |  (LFrm_E (_, ls, _)) \<Rightarrow> (x \<in> lm_dom ls) 
              ))"

fun upd_var_in_lstack :: "lstack \<Rightarrow> id0 \<Rightarrow> literal \<Rightarrow> lstack" where 
  "upd_var_in_lstack lstk x v = (
     let (idx, found) = idx_id_in_ls (lstk) x in
      let new_ele = 
        (case (lstk!idx) of
          (LFrm_E (e0, ls0, fs0)) \<Rightarrow> LFrm_E (e0, ls0 @ [(x,v)], fs0)
         | (LFrm_B (b0, ls0, fs0, cf)) \<Rightarrow> LFrm_B (b0, ls0 @ [(x,v)], fs0, cf))
      in
      let lstk' = list_update lstk idx (new_ele) in lstk'
    )
    " 

(* (ceiling_times i align) gives the roundup of the result of (i / align) *)
definition ceiling_div :: "int \<Rightarrow> int \<Rightarrow> int" where 
  "ceiling_div i align = (((i + align) - (1 :: int)) div align)"

value "0xf2 ::nat"
value "2*ceiling_div (uint (10 :: 16 word)) 3"
value "ceiling_div (uint (8::4 word)) 2"
value "ceiling_div (uint (0xf2 :: 16 word)) 34"

definition ext_mem_sz :: "256 word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 256 word" where 
  "ext_mem_sz naws offt sz = (
    if sz = 0 then 
      naws
    else 
      (max (naws) (word_of_int (ceiling_div ((offt) + (sz)) (32 :: int))))
  )"

fun expr_fill_retids :: "expr \<Rightarrow> lstate \<Rightarrow> expr" and 
    blk_fill_retids :: "block \<Rightarrow> lstate \<Rightarrow> block" where 

  "expr_fill_retids (ERetId xt) ls = (case (lm_get ls (fst xt)) of (Some l) \<Rightarrow> (EImLit l))" |
  "expr_fill_retids (EList es) ls = (EList (map (\<lambda>e. expr_fill_retids e ls) es))" |
  "expr_fill_retids (EImFunCall f es) ls = (
    let es' = map (\<lambda>e. (expr_fill_retids e ls)) es in (EImFunCall f es')
  )" | 
  "expr_fill_retids (VAR xts ::- e) ls = (VAR xts ::- (expr_fill_retids e ls))" |
  "expr_fill_retids (xs ::= e) ls = (xs ::= (expr_fill_retids e ls))" | 
  "expr_fill_retids (IF e THEN blk) ls = 
    (IF (expr_fill_retids e ls) THEN (blk_fill_retids blk ls))" | 
  "expr_fill_retids (FOR blk0 e blk1 blk) ls = 
    (FOR (blk_fill_retids blk0 ls) (expr_fill_retids e ls) (blk_fill_retids blk1 ls) 
         (blk_fill_retids blk ls))" |
  "expr_fill_retids (COND e blk) ls = 
    (COND (expr_fill_retids e ls) (blk_fill_retids blk ls))" | 
  "expr_fill_retids (SWITCH e CASES cases DEFAULT blk_opt) ls = 
    (SWITCH (expr_fill_retids e ls) 
     CASES (map (\<lambda>(l, blk). (l, blk_fill_retids blk ls)) cases)
     DEFAULT (case blk_opt of Some blk \<Rightarrow> Some (blk_fill_retids blk ls) | None \<Rightarrow> None))" | 
  "expr_fill_retids e ls = e" |

  "blk_fill_retids (Blk es) ls = Blk (map (\<lambda>e. expr_fill_retids e ls) es)"

definition f_id :: id0 where "f_id = -101" 
definition g_id :: id0 where "g_id = -102"
definition f_res_id :: id0 where "f_res_id = -103"
definition f_param_id :: id0 where "f_param_id = -104" 
definition ls_1 :: lstate where "ls_1 = [(f_res_id, ((NL 102) :L U256))]" 
definition fs_1 :: fstate where 
  "fs_1 = [(f_id, FunctionV f_id [(f_param_id, U256)] [(f_res_id, U256)] (BEGIN [] END))]" 

value "expr_fill_retids (EList [ERetId (f_res_id, U256)]) ls_1"

definition call_expr :: expr where 
  "call_expr = EImFunCall g_id [EImLit ((NL 2) :L U256), ERetId (f_res_id, U256)]" 

value "expr_fill_retids call_expr ls_1"

definition call_expr_2 :: expr where 
  "call_expr_2 = EImFunCall g_id [EImLit ((NL 2) :L U256), ERetId (f_res_id, U256), EId 10]" 

value "expr_fill_retids call_expr_2 ls_1"

definition call_expr_3 :: expr where 
  "call_expr_3 = 
    EImFunCall g_id [EImLit ((NL 2) :L U256), EImFunCall g_id [ERetId (f_res_id, U256)]]"

value "expr_fill_retids call_expr_3 ls_1"

definition extcall_ret_id where "extcall_ret_id = 0" 

definition blk_fill_bool :: "block \<Rightarrow> bool \<Rightarrow> block" where 
  "blk_fill_bool blk tf = 
    (if tf then 
      (blk_fill_retids blk [(extcall_ret_id, ((NL 1) :L U256))])
     else 
      (blk_fill_retids blk [(extcall_ret_id, ((NL 0) :L U256))]) 
    )"

(* update the range [offt, offt + sz) of mem with v *)
fun upd_mem_bytes :: "(256 word \<Rightarrow> 8 word) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (8 word) list \<Rightarrow> (256 word \<Rightarrow> 8 word)" where
  "upd_mem_bytes mem offt sz v = (
   \<lambda>(x::256 word). 
    if (x \<ge> (word_of_int offt) \<and> (x < word_of_int (offt + sz))) then 
      (v ! (nat (uint x) - (nat offt)))
    else 
      (mem x)
  )"

definition Cbase :: "int \<Rightarrow> int \<Rightarrow> int" where
  "Cbase va flag = (
      let va' = if (va = 0) then 0 else 9000 in
       let flag' = if (flag = 0) then 25000 else 0 in
        (700 + va' + flag')
  )"

value "Cbase 1 1"
value "Cbase 0 0"

definition Cgascap :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 256 word \<Rightarrow> 256 word" where
  "Cgascap va flag g gas_gs = (
     let cex = (700 + (if (va = 0) then 0 else 9000) 
                  + (if (flag = 0) then 25000 else 0)) 
       in (
          let va' = (if (va = 0) then 0 else 2300) in
          let cex' = if (cex > (uint gas_gs)) then (word_of_int g)
                     else (min (word_of_int g)  (gas_gs - (word_of_int cex)))
           in (cex' + word_of_int va')
          )
  )"

value "Cgascap 1 0 3000 9000"

fun MyLog :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "MyLog _ a b 0 = 0"|
  "MyLog lst a b (Suc n) = (
    let x = nat (lst ! n) in
    if (a^x \<le> b \<and> b < a^(x+1)) 
    then x else (MyLog lst a b n)
  )"

value "MyLog [1 .. 4] 10 3500 4"
value "MyLog [1..32] 256 25 20"
value "MyLog [1..32] 256 257 20"
value "MyLog [1..32] 256 65576 20"

fun callret :: "gstack \<Rightarrow> gstack" where
 "callret 
   ((GFrmHalt gs' ret_data (CKCall g to val io is oo os))
     # (GFrmNormal (LFrm_B (blk, ls, fs, cf) # lstk') gs ck) # gstk') 
   =      
    ( let to = ((word_of_int (to mod 2^160)) :: (160 word)) in
      let naws = ext_mem_sz (ext_mem_sz (naws_of gs) io is) oo os in
      let flag = if (accs_of gs to = None) then 0 else 1 in
      let c_call = Cgascap val flag g (gas_of gs) in   
      let c = (Cbase val flag) +  (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) 
      in (
       (GFrmNormal (LFrm_B (blk_fill_bool blk True, ls, fs, cf) # lstk')
        (gs \<lparr> accs_of := (accs_of gs'),
              mem_of := (upd_mem_bytes (mem_of gs) oo os ret_data),
              naws_of := naws,
              gas_of := (gas_of gs') + (gas_of gs) - (word_of_int c), 
              ct_of := (ct_of gs) + 1,
              refund_of := (refund_of gs'), 
              logs_of := (logs_of gs'), 
              ss_of := (ss_of gs')
              \<rparr> ) ck ) # gstk'  
         ) 
    )
 " |
 "callret gstk = []"

fun callcoderet :: "gstack \<Rightarrow> gstack" where
 "callcoderet  
   ((GFrmHalt gs' ret_data (CKCallCode g to val io is oo os))
    # (GFrmNormal (LFrm_B (blk, ls, fs, cf) # lstk') gs ck) # gstk') 
   = (          
       let to = ((word_of_int (to mod 2^160)) :: (160 word)) in
       let naws = ext_mem_sz (ext_mem_sz (naws_of gs) io is) oo os in
       let c_call = Cgascap val 1 g (gas_of gs) in   
       let c = (Cbase val 1) +  (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) in
       ( (GFrmNormal (LFrm_B (blk_fill_bool blk True, ls, fs, cf) # lstk') 
           (gs \<lparr> accs_of := (accs_of gs'),
                 mem_of := (upd_mem_bytes (mem_of gs) oo os ret_data),
                 naws_of := naws,
                 gas_of := (gas_of gs') + (gas_of gs) - (word_of_int c),
                 ct_of := (ct_of gs) + 1,
                 refund_of := (refund_of gs'), 
                 logs_of := (logs_of gs'), 
                 ss_of := (ss_of gs')
             \<rparr> ) ck ) # gstk' )  
     )
 " |
 "callcoderet gstk = []"

fun delcallret :: "gstack \<Rightarrow> gstack" where
 "delcallret  
    ((GFrmHalt gs' ret_data (CKDelCall g to io is oo os))
        # (GFrmNormal (LFrm_B (blk, ls, fs, cf) # lstk') gs ck) # gstk')  
   = (  
     let to = ((word_of_int (to mod 2^160)) :: (160 word)) in
      let naws = ext_mem_sz (ext_mem_sz (naws_of gs) io is) oo os in
       let c_call = Cgascap 0 1 g (gas_of gs) in   
       let c = (Cbase 0 1) +  (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) in
        ( (GFrmNormal (LFrm_B (blk_fill_bool blk True, ls, fs, cf) # lstk') 
           (gs \<lparr> accs_of := (accs_of gs'),
                 mem_of := (upd_mem_bytes (mem_of gs) oo os ret_data),
                 naws_of := naws,
                 gas_of := (gas_of gs') + (gas_of gs) - (word_of_int c),
                 ct_of := (ct_of gs) + 1, 
                 refund_of := (refund_of gs'), 
                 logs_of := (logs_of gs'), 
                 ss_of := (ss_of gs')
             \<rparr> ) ck ) # gstk' )
  )
 " |  
 "delcallret gstk = []"

definition update_gstate  :: " gstate \<Rightarrow> gstate \<Rightarrow> gstate "  where 
  " update_gstate g ng = ( 
  (let acc1 = (\<lambda> x . 
               if x = (addr_of ng) then (accs_of ng) x else
                 (accs_of ng) x) in  
  (g \<lparr> accs_of := acc1, logs_of := (logs_of ng) \<rparr>)) )"

definition eval_opbuiltin :: "gstate \<Rightarrow> opbuiltin \<Rightarrow> (lit_content)list \<Rightarrow> (gstate*(literal option))"  
  where 
 "eval_opbuiltin gs bib lst = (
  (case (bib,lst) of
    (Add, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
             Some ((NL ((a+b) mod 2^256)):L U256))
       else (gs, None)) 
   | (Sub, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
             Some ((NL ((a-b) mod 2^256)) :L U256))
       else (gs, None))
   | (Mul, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 5 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 5),
                 ct_of := (ct_of gs) + 1 \<rparr>,
       Some ((NL ((a*b) mod 2^256)):L U256))
       else (gs, None)) 
   | (SDiv, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 5 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 5),
                 ct_of := (ct_of gs) + 1 \<rparr>,
          Some (if (b = 0) then ((NL 0):L U256) else ((NL (a div b)):L S256)))
       else (gs, None))
   | (Div, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 5 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 5),
                 ct_of := (ct_of gs) + 1 \<rparr>,
         Some (if (b = 0) then ((NL 0):L U256) else ((NL ((a div b) mod 2^256)):L U256)))
       else (gs, None))
   | (SMod, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 5 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 5),
                 ct_of := (ct_of gs) + 1 \<rparr>,
         Some (if (b = 0) then ((NL 0):L U256) else ((NL ((a mod b))):L S256)))
       else (gs, None))
   | (Mod, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 5 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 5),
                 ct_of := (ct_of gs) + 1 \<rparr>,
        Some (if (b = 0) then ((NL 0):L U256) else ((NL ((a mod b) mod 2^256)):L U256)))
       else (gs, None)) 
   | (And, [NL a, NL b]) \<Rightarrow> 
      (if (valid_gas_cost (gas_of gs) 3)
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3) \<rparr>, 
        Some ((NL (uint (bitAND ((word_of_int a) :: 256 word) ((word_of_int b)::256 word)))):L U256))
            \<comment> \<open>Some (IntV (andu256_bin_list a b))\<close>
            \<comment> \<open>previously [IntV (uint (bitAND (Abs_word a :: 256 word) (Abs_word b :: 256 word)))]\<close> 
       else (gs, None)) 
   | (Or, [NL a, NL b]) \<Rightarrow> 
      (if (valid_gas_cost (gas_of gs) 3)
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3) \<rparr>, 
        Some ((NL (uint (bitOR ((word_of_int a) :: 256 word) ((word_of_int b)::256 word)))):L U256))
            \<comment> \<open>Some (IntV (andu256_bin_list a b))\<close>
            \<comment> \<open>previously [IntV (uint (bitOR (Abs_word a :: 256 word) (Abs_word b :: 256 word)))]\<close> 
       else (gs, None))
   | (Xor, [NL a, NL b]) \<Rightarrow> 
      (if (valid_gas_cost (gas_of gs) 3)
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3) \<rparr>, 
        Some ((NL (uint (bitXOR ((word_of_int a) :: 256 word) ((word_of_int b)::256 word)))):L U256))
            \<comment> \<open>Some (IntV (andu256_bin_list a b))\<close>
            \<comment> \<open>previously [IntV (uint (bitXOR (Abs_word a :: 256 word) (Abs_word b :: 256 word)))]\<close> 
       else (gs, None)) 
   | (Lt, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
             Some (if ((a mod 2^256) < (b mod 2^256)) then (TL :L Bool) else (FL :L Bool)))
       else (gs, None)) 
   | (SLt, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
        Some (if (a < b) then (TL :L Bool) else (FL :L Bool)))
       else (gs, None))  
   | (Gt, [NL a, NL b]) \<Rightarrow>
      (if (valid (gas_of gs) 3 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
       Some ((if ((a mod 2^256) > (b mod 2^256)) then (TL :L Bool) else (FL :L Bool))))
       else (gs, None)) 
   | (SGt, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
        Some ((if (a > b) then (TL :L Bool) else (FL :L Bool))))
       else (gs, None)) 
   | (Eq, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
        Some (if (a = b) then (TL :L Bool) else (FL :L Bool)))
       else (gs, None)) 
   | (LOr, [v1, v2]) \<Rightarrow>
      (if (valid (gas_of gs) 3 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
         Some (if (v1=TL \<or> v2=TL) then (TL :L Bool) else (FL :L Bool)))
       else (gs, None))
   | (LAnd, [v1, v2]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
        Some (if (v1=TL \<and> v2=TL) then (TL :L Bool) else (FL :L Bool))) 
       else (gs, None)) 
   | (LXor, [v1, v2]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
          Some (if ((\<not>v1=TL) \<and> (v2=TL)) \<or> ((\<not>v2=TL) \<and> (v1=TL)) then (TL :L Bool) else (FL :L Bool)))
       else (gs, None))
   | (Shl, [NL a, NL b]) \<Rightarrow> 
      (if (valid_gas_cost (gas_of gs) 3)
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3) \<rparr>,
        Some (if (nat a = 0) then ((NL b):L U256) else ((NL ((2^(nat a) * b) mod 2^256)) :L U256)))
       else (gs, None)) 
   | (Shr, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
            Some (if (nat a = 0) then ((NL b):L U256) else ((NL ((b div (2^(nat a))) mod 2^256)) :L U256)))
       else (gs, None))
   | (Sar, [NL a, NL b]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
            Some (if (nat a = 0) then ((NL b):L U256) else ((NL ((b div (2^(nat a))) mod 2^256)) :L U256)))
       else (gs, None))
   | (Not, [NL a]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
            Some ((NL (uint (bitNOT ((word_of_int a) :: 256 word)))) :L U256))
       else (gs, None)) 
   | (LNot, [v]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
             Some (if (v=TL) then (FL :L Bool) else (TL :L Bool)))
       else (gs, None)) 
   | (IsZero, [NL a]) \<Rightarrow> 
      (if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 3),
                 ct_of := (ct_of gs) + 1 \<rparr>,
             Some (if (a = 0) then (TL :L Bool) else (FL :L Bool)))
       else (gs, None)) 
   | (AddMod, [NL a, NL b, NL c]) \<Rightarrow> 
      (if (valid (gas_of gs) 8 ((ct_of gs)+1))
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 8),
                 ct_of := (ct_of gs) + 1 \<rparr>,
             Some(if (c = 0) then ((NL 0):L U256) else ((NL ((a+b) mod c)):L U256))) 
       else (gs, None))
   | (MulMod, [NL a, NL b, NL c]) \<Rightarrow> 
      (if (valid (gas_of gs) 8 ((ct_of gs)+1)) 
       then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int 8),
                 ct_of := (ct_of gs) + 1 \<rparr>,
             Some(if (c = 0) then ((NL 0):L U256) else ((NL ((a*b) mod c)):L U256))) 
       else (gs, None)) 
   | (Exp, [NL a, NL b]) \<Rightarrow> ( 
      let c = (if b=0 then 10 else (10+10*(1+(MyLog [0..31] 256 b 32)))) in
       if (valid (gas_of gs) c ((ct_of gs)+1))
               then (gs\<lparr> gas_of := (gas_of gs)-(word_of_int (int c)),
                         ct_of := (ct_of gs) + 1 \<rparr>,
                     Some ((NL ((a^(nat b)) mod 2^256)):L U256)) 
               else (gs, None)
     ) 
   | _ \<Rightarrow> (gs, None)
  
  ))"

definition step_callbuiltin :: 
  " gstack_frame \<Rightarrow> callbuiltin \<Rightarrow> (lit_content) list \<Rightarrow> gstack " where
  "step_callbuiltin gfrm callgb lst = (
   case gfrm of 
    (GFrmNormal (LFrm_E (EImFunCall _ _, ls, fs) # lstk) gs ck) \<Rightarrow> 
    (case (callgb, lst) of 
       (Call, [(NL gas), (NL to_addr), (NL money), 
         (NL in_offset), (NL in_size), (NL out_offset), (NL out_size)]) \<Rightarrow> (
           let naws =(ext_mem_sz (ext_mem_sz (naws_of gs) in_offset in_size) out_offset out_size) in
           let from = addr_of gs in (
               case (accs_of gs from) of 
                 Some cur_acc \<Rightarrow> (
                   if (uint (bal_of cur_acc)) \<ge> money then (
                     let to = ((word_of_int (to_addr mod 2^160)) :: (160 word)) in (
                     case (accs_of gs to) of 
                      Some to_acc \<Rightarrow> (
                       let c_call = Cgascap money 1 gas (gas_of gs) in   
                       let c = (Cbase money 1) +  (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) in
                        if (valid (gas_of gs) (nat c) ((ct_of gs)+1))
                        then (
                           let gs' = 
                             gs \<lparr> accs_of := 
                                ((accs_of gs)
                                    (from := Some (cur_acc\<lparr> bal_of := 
                                                  (word_of_int ((uint (bal_of cur_acc)) - money)) \<rparr>)))
                                    (to := Some (to_acc\<lparr> bal_of := 
                                                  (word_of_int ((uint (bal_of to_acc)) + money)) \<rparr>)) \<rparr>
                           in (
                              [(GFrmNormal 
                                [case (code_of to_acc) of 
                                  Some blk \<Rightarrow> LFrm_B (blk, [], get_func_values blk, None)
                                 | None \<Rightarrow> LFrm_B (BEGIN [] END, [], [], None)] 
                                (gs' \<lparr> addr_of := to,
                                       saddr_of := from,
                                       input_of := get_mem_bytes (mem_of gs) in_offset (nat (abs in_size)),
                                       money_of := word_of_int money, 
                                       mem_of := (\<lambda>addr. 0), 
                                       naws_of := 0, 
                                       gas_of := c_call
                                   \<rparr>)
                                (CKCall gas to_addr money in_offset in_size out_offset out_size)
                              )] @ 
                              [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                           )
                        )
                        else 
                          [(GFrmExc (CKCall gas to_addr money in_offset in_size out_offset out_size))]
                          @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                     )
                     | None \<Rightarrow> (
                       let new_acc = 
                         (\<lparr> code_of = None, store_of = (\<lambda>a. 0), bal_of = word_of_int money, nonce_of = 0 \<rparr>)
                       in (
                        let c_call = Cgascap money 0 gas (gas_of gs) in   
                        let c = (Cbase money 0) +  (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) in
                         if (valid (gas_of gs) (nat c) ((ct_of gs)+1))
                         then (
                           let gs' = 
                             gs \<lparr> accs_of := 
                                  ((accs_of gs)
                                    (from := Some (cur_acc\<lparr> bal_of := 
                                             (word_of_int ((uint (bal_of cur_acc)) - money)) \<rparr>)))
                                    (to := Some new_acc) \<rparr>
                           in 
                            [(GFrmNormal [LFrm_B (BEGIN [] END, [], [], None)] 
                                (gs' \<lparr> addr_of := to,
                                       saddr_of := from,
                                       input_of := get_mem_bytes (mem_of gs) in_offset (nat (abs in_size)),
                                       money_of := word_of_int money, 
                                       mem_of := (\<lambda>addr. 0), 
                                       naws_of := 0, 
                                       gas_of := c_call
                                   \<rparr>) (CKCall gas to_addr money in_offset in_size out_offset out_size))
                             ] 
                             @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck] 
                           )
                         else 
                          [(GFrmExc (CKCall gas to_addr money in_offset in_size out_offset out_size))]
                          @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                        )
                      )
                  )) else 
                    [(GFrmExc (CKCall gas to_addr money in_offset in_size out_offset out_size))]
                    @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                )
              | None \<Rightarrow> [] 
            )

          )
       | (CallCode, [(NL gas), (NL to_addr), (NL money), 
           (NL in_offset), (NL in_size), (NL out_offset), (NL out_size)]) \<Rightarrow> (
             let naws =(ext_mem_sz (ext_mem_sz (naws_of gs) in_offset in_size) out_offset out_size) in
              let from = addr_of gs in (
              case (accs_of gs from) of 
                Some cur_acc \<Rightarrow> (
                  if (uint (bal_of cur_acc)) \<ge> money then (
                    let to = ((word_of_int (to_addr mod 2^160)) :: (160 word)) in (
                    case (accs_of gs to) of 
                      Some to_acc \<Rightarrow> (
                       let c_call = Cgascap money 1 gas (gas_of gs) in   
                       let c = (Cbase money 1) + (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) in
                        if (valid (gas_of gs) (nat c) ((ct_of gs)+1)) 
                        then (
                         let gs' = gs
                          in (
                              [(GFrmNormal 
                                [case (code_of to_acc) of 
                                  Some blk \<Rightarrow> LFrm_B (blk, [], get_func_values blk, None)
                                 | None \<Rightarrow> LFrm_B (BEGIN [] END, [], [], None)] 
                                (gs' \<lparr> 
                                       saddr_of := from,
                                       input_of := get_mem_bytes (mem_of gs) in_offset (nat (abs in_size)),
                                       money_of := word_of_int money, 
                                       mem_of := (\<lambda>addr. 0), 
                                       naws_of := 0, 
                                       gas_of := c_call
                                   \<rparr>)
                                (CKCallCode gas to_addr money in_offset in_size out_offset out_size)
                              )] 
                              @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                          )
                        )
                        else 
                          [(GFrmExc (CKCallCode gas to_addr money in_offset in_size out_offset out_size))]
                          @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                     )
                    | None \<Rightarrow> (
                       let c_call = Cgascap money 1 gas (gas_of gs) in   
                       let c = (Cbase money 1) + (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) in
                        if (valid (gas_of gs) (nat c) ((ct_of gs)+1))
                        then (
                          let gs' =  gs
                          in 
                            [(GFrmNormal [LFrm_B (BEGIN [] END, [], [], None)] 
                                (gs' \<lparr> 
                                       saddr_of := from,
                                       input_of := get_mem_bytes (mem_of gs) in_offset (nat (abs in_size)),
                                       money_of := word_of_int money, 
                                       mem_of := (\<lambda>addr. 0), 
                                       naws_of := 0, 
                                       gas_of := c_call
                                   \<rparr>) (CKCallCode gas to_addr money in_offset in_size out_offset out_size))
                            ] 
                            @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                        )
                        else 
                          [(GFrmExc (CKCallCode gas to_addr money in_offset in_size out_offset out_size))]
                          @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                      )
                  )) else 
                    [(GFrmExc (CKCallCode gas to_addr money in_offset in_size out_offset out_size))]
                    @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                )
              | None \<Rightarrow> [] 
             ) 
          )
       | (DelegateCall, [(NL gas), (NL to_addr), 
           (NL in_offset), (NL in_size), (NL out_offset), (NL out_size)]) \<Rightarrow> (
             let naws =(ext_mem_sz (ext_mem_sz (naws_of gs) in_offset in_size) out_offset out_size) in
              let from = addr_of gs in (
              case (accs_of gs from) of 
                Some cur_acc \<Rightarrow> (
                  let to = ((word_of_int (to_addr mod 2^160)) :: (160 word)) in (                   
                    case (accs_of gs to) of 
                      Some to_acc \<Rightarrow> (
                         let c_call = Cgascap 0 1 gas (gas_of gs) in   
                         let c = (Cbase 0 1) + (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) in
                          if (valid (gas_of gs) (nat c) ((ct_of gs)+1))
                           then (
                              let gs' = gs
                               in (
                                [(GFrmNormal 
                                  [case (code_of to_acc) of 
                                    Some blk \<Rightarrow> LFrm_B (blk, [], get_func_values blk, None)
                                   | None \<Rightarrow> LFrm_B (BEGIN [] END, [], [], None)] 
                                  (gs' \<lparr> 
                                         
                                         input_of := get_mem_bytes (mem_of gs) in_offset (nat (abs in_size)),
                                        
                                         mem_of := (\<lambda>addr. 0), 
                                         naws_of := 0, 
                                         gas_of := c_call
                                     \<rparr>)
                                  (CKDelCall gas to_addr in_offset in_size out_offset out_size)
                                )] 
                                @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                             )
                           )
                           else 
                             [(GFrmExc (CKDelCall gas to_addr in_offset in_size out_offset out_size))]
                             @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                     )
                    | None \<Rightarrow> (    
                      let c_call = Cgascap 0 1 gas (gas_of gs) in   
                       let c = (Cbase 0 1) +  (Cmem (uint (naws_of gs)) (uint naws)) + (uint c_call) in
                        if (valid (gas_of gs) (nat c) ((ct_of gs)+1))
                        then (
                          let gs' =  gs
                          in 
                            [(GFrmNormal [LFrm_B (BEGIN [] END, [], [], None)] 
                                (gs' \<lparr>
                                      
                                       input_of := get_mem_bytes (mem_of gs) in_offset (nat (abs in_size)),
                                      
                                       mem_of := (\<lambda>addr. 0), 
                                       naws_of := 0, 
                                       gas_of := c_call
                                   \<rparr>) (CKDelCall gas to_addr in_offset in_size out_offset out_size))
                            ] 
                            @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                        )
                        else 
                          [(GFrmExc (CKDelCall gas to_addr in_offset in_size out_offset out_size))]
                          @ [GFrmNormal (LFrm_E (ERetId (extcall_ret_id, U256), ls, fs) # lstk) gs ck]
                      )
                   )
                )
              | None \<Rightarrow> [] 
          )
      )
       | (Revert, [NL io, NL is]) \<Rightarrow> [GFrmExc ck] \<comment> \<open>without appending gfrm this time\<close>
       | (Return, [NL io, NL is]) \<Rightarrow> (
           let naws = (ext_mem_sz (naws_of gs) io is) in 
            let c = (Cmem (uint(naws_of gs)) (uint naws)) in
             let ds = get_mem_bytes (mem_of gs) io (nat (abs is)) in 
               if (valid (gas_of gs) (nat c) (ct_of gs)) 
               then ([GFrmHalt (gs\<lparr>gas_of := (gas_of gs)-(word_of_int c)\<rparr>) ds ck]) 
               else [GFrmExc ck]
              
         )
       | (Selfdestruct, [NL a]) \<Rightarrow>(
           let from = addr_of gs in (
             case (accs_of gs from) of 
               Some cur_acc \<Rightarrow> (
                let money = uint (bal_of cur_acc) in           
                  let to = ((word_of_int (a mod 2^160)) :: (160 word)) in (
                    case (accs_of gs to) of 
                     Some to_acc \<Rightarrow> (
                      let r = (if (from \<in> (ss_of gs)) then (24000) else (0)) in
                       if (valid (gas_of gs) 5000 (ct_of gs)) 
                       then (
                         let gs' = 
                          gs \<lparr> accs_of := 
                              ((accs_of gs)
                                  (from := Some (cur_acc\<lparr> bal_of := 
                                                (word_of_int ((uint (bal_of cur_acc)) - money)) \<rparr>)))
                                  (to := Some (to_acc\<lparr> bal_of := 
                                                (word_of_int ((uint (bal_of to_acc)) + money)) \<rparr>))\<rparr>
                         in (
                              let gs' = gs'\<lparr> refund_of := (refund_of gs) + (word_of_int r),
                                             gas_of := (gas_of gs) - 5000,
                                             ss_of := (ss_of gs) \<union> {from} \<rparr>  
                                in [GFrmHalt gs' [] ck]
                            )
                       )
                       else [GFrmExc ck]
                    )
                   | None \<Rightarrow> (
                     let r = (if (from \<in> (ss_of gs)) then (0) else (24000)) in
                      let new_acc = 
                        (\<lparr> code_of = None, store_of = (\<lambda>a. 0), bal_of = word_of_int money, nonce_of = 0 \<rparr>)
                      in (
                          if (valid (gas_of gs) 30000 (ct_of gs)) 
                          then (
                            let gs' = 
                              gs \<lparr> accs_of := 
                                    ((accs_of gs)
                                      (from := Some (cur_acc\<lparr> bal_of := 
                                               (word_of_int ((uint (bal_of cur_acc)) - money)) \<rparr>)))
                                      (to := Some new_acc) \<rparr>
                             in (
                                let gs' = gs'\<lparr> refund_of := (refund_of gs) + (word_of_int r),
                                               gas_of := (gas_of gs) - 30000,
                                               ss_of := (ss_of gs) \<union> {from} \<rparr>   
                                  in [GFrmHalt gs' [] ck]
                              )
                          )
                          else [GFrmExc ck]                        
                       )
                    )               
                 )                  
              )
              | None \<Rightarrow>[]
            )
          )
       | (Stop, []) \<Rightarrow> [GFrmHalt gs [] ck]
       | (Invalid, []) \<Rightarrow> [GFrmExc ck]
 
       |  _ \<Rightarrow> [] 
    )
  )
 "

definition list_to_map  :: "(8 word)list \<Rightarrow> (256 word \<Rightarrow> (8 word))"  where 
  " list_to_map lst x = (
  (case index lst (nat (abs (uint (x)))) of
    None \<Rightarrow>  0 
  | Some x \<Rightarrow>  x
  ))"

value "list_to_map [2 :: 8 word, 2, 1] 2"

fun fill_zero :: "(8 word)list \<Rightarrow> int \<Rightarrow> (8 word)list" where
  "fill_zero lst sz  = (
    if (sz > 0) then ((fill_zero lst (sz-1)) @ [0 :: 8 word]) else lst
  )"

value "int (size [2 :: int, 2]) - 8"
value "fill_zero [1 :: 8 word, 2 ,3] (5 - int(size [1 :: 8 word, 2 ,3]))"

(* mu.m[a, a+n-1] size=n --- 0^n*)
function (sequential,domintros) memory_integer_be :: 
  "(8 word) list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int "  where 
  "memory_integer_be lst addr 0 acc = acc" |
  "memory_integer_be lst addr ((Suc n)) acc = (
     memory_integer_be lst (addr + 1) n (acc*2^8 + uint (lst!(nat addr)))
  )" 
 by pat_completeness auto
termination by lexicographic_order

value "(get_mem_bytes (((\<lambda> i. 0:: 8 word)(0 := 1:: 8 word))(1 := 2:: 8 word)) (0::int) 3)"
value "get_mem_bytes (upd_mem_bytes (((\<lambda> i. 0:: 8 word)(0 := 1:: 8 word))(1 := 2:: 8 word)) 
        (0::int) 3 [255::8 word,1,0,2]) (0::int) 3"
value "memory_integer_be (get_mem_bytes 
          (upd_mem_bytes (((\<lambda> i. 0:: 8 word)(0 := 1:: 8 word))(1 := 2:: 8 word)) 
          (0::int) 3 [255::8 word,1,0,2])
        (0::int) 3) 0 2 0"
value "255*2^8+1 :: int"
value "memory_integer_be 
        (get_mem_bytes (((\<lambda> i. 0:: 8 word)(0 := 1:: 8 word))(1 := 2:: 8 word)) 
        (0::int) 3) 1 2 0"

value "memory_integer_be [0::8 word, 2, 3] 0 2 0"
value "memory_integer_be [10::8 word, 2] 0 2 0"
value "10*2^8+2 :: int"
value "memory_integer_be (rev [10::8 word, 2]) 0 2 0"
value "2*2^8+10 :: int"

fun int_to_byte_lst :: "int \<Rightarrow> nat \<Rightarrow> (8 word) list"  where 
  "int_to_byte_lst v 0 = []" |
  "int_to_byte_lst v (Suc n) = (
    rev (word_of_int (v mod 2^8) # rev (int_to_byte_lst (v div 2^8) n)) 
  )" 

value "int_to_byte_lst 1355 3"
value "memory_integer_be (int_to_byte_lst 1355 3) 0 3 0"
value "0*2^8*2^8+5*2^8+75 :: int"
value "memory_integer_be (rev(int_to_byte_lst 1355 3)) 0 3 0"
value "75*2^8*2^8+5*2^8+0 :: int"

definition memory_integer_bigendian :: "(8 word) list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "memory_integer_bigendian mem addr n = memory_integer_be mem addr n 0"

value "memory_integer_bigendian 
        (get_mem_bytes ((((\<lambda> i. 0:: 8 word)(0 := 1:: 8 word))(1 := 2:: 8 word))(2 := 32:: 8 word)) 
          (0::int) 2) 0 2 "
value "int_to_byte_lst 172508 32"
value "size(int_to_byte_lst 172508 32)"
value "memory_integer_bigendian (get_mem_bytes 
        (upd_mem_bytes (((\<lambda> i. 0:: 8 word)(0 := 1:: 8 word))(1 := 2:: 8 word)) 
          (0::int) 32 ((int_to_byte_lst 172508 32)))
        (0::int) 32) 0 32"
value "255*2^8+1 :: int"

definition big_num :: "4 word" where "big_num = 2^4-1"
value "big_num"
definition bigger_num :: "4 word" where "bigger_num = big_num + 1"
value "bigger_num"

definition eval_rbuiltin :: 
  "gstate \<Rightarrow> rbuiltin \<Rightarrow> (lit_content)list \<Rightarrow> (gstate *(literal option)) " where
 "eval_rbuiltin gs gb lst =
    (case (gb,lst) of        
        (MSize, []) \<Rightarrow> (
           if (valid (gas_of gs) 2 ((ct_of gs)+1))
           then (
              let v = (uint (naws_of gs))*32 in(
                gs\<lparr>gas_of := (gas_of gs) - 2, ct_of := (ct_of gs) + 1\<rparr>,
                Some ((NL v) :L U256) )
            )
           else (gs, None)
          ) 
      | (Balance, [NL a]) \<Rightarrow> (  
            if (valid (gas_of gs) 400 ((ct_of gs)+1)) 
            then (case (accs_of gs (word_of_int (a mod 2^160))) of 
                Some cur_acc \<Rightarrow>       
                   let b = ((bal_of cur_acc)) in
                    (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 400), ct_of := (ct_of gs) + 1\<rparr>,
                     Some ((NL (uint b)) :L U256))
               | None \<Rightarrow> (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 400), ct_of := (ct_of gs) + 1\<rparr>,
                          Some ((NL 0) :L U256)) 
             )
            else (gs, None)
         )
      | (Gas, []) \<Rightarrow> (
           if (valid (gas_of gs) 2 ((ct_of gs)+1))
           then (
              let v = uint (gas_of gs) in(
               gs\<lparr>gas_of := (gas_of gs) - 2, ct_of := (ct_of gs) + 1\<rparr>, 
               Some ((NL v) :L U256) )
            )
            else (gs, None) 
          )
      | (Address, []) \<Rightarrow> (
          if (valid (gas_of gs) 2 ((ct_of gs)+1))
          then (
             let v = uint(addr_of gs) in(
             gs\<lparr>gas_of := (gas_of gs) - 2, ct_of := (ct_of gs) + 1\<rparr>,
              Some ((NL v) :L U256))
            )
          else (gs, None) 
          )
      | (Caller, []) \<Rightarrow> (
          if (valid (gas_of gs) 2 ((ct_of gs)+1))
          then (
              let sender = uint(saddr_of gs) in
               (gs\<lparr>gas_of := (gas_of gs) - 2, ct_of := (ct_of gs) + 1\<rparr>,
                Some ((NL sender) :L U256))
             )
          else (gs, None)
          )
      | (Callvalue, []) \<Rightarrow> (
           if (valid (gas_of gs) 2 ((ct_of gs)+1))
           then (
              let value = money_of gs in
              (gs\<lparr>gas_of := (gas_of gs) - 2, ct_of := (ct_of gs) + 1\<rparr>,
               Some ((NL (uint value)) :L U256)) 
            )
           else (gs, None) 
          )
      | (CalldataSize, []) \<Rightarrow> (
           if (valid (gas_of gs) 2 ((ct_of gs)+1))
           then (
              let is = size (input_of gs) in
                (gs\<lparr>gas_of := (gas_of gs) - 2, ct_of := (ct_of gs) + 1\<rparr>,
                 Some ((NL (int is)) :L U256)) 
            )
           else (gs, None) 
         )
      | (CalldataLoad, [NL a]) \<Rightarrow> (
          if (valid (gas_of gs) 3 (ct_of gs)) 
          then (
            let v = 
              if (int(size (input_of gs)) - a < 0) then 0
              else (
                 memory_integer_bigendian 
                  (fill_zero (input_of gs) ((a+32) - int(size (input_of gs)))) a 32 
               )
              in (gs\<lparr>gas_of := (gas_of gs) - 3, ct_of := (ct_of gs) + 1\<rparr>,
                  Some ((NL v) :L U256))    
            )
          else (gs, None)
         )  
      |  (MLoad, [NL a]) \<Rightarrow> (
           let v = (memory_integer_bigendian (get_mem_bytes (mem_of gs) a 32) 0 32) in
            let naws = (ext_mem_sz (naws_of gs) a (int 32)) in 
             let c = (Cmem (uint(naws_of gs)) (uint naws)) + 3 in
              if (valid (gas_of gs) (nat c) ((ct_of gs)+1))
              then (gs\<lparr> naws_of := naws, 
                        gas_of := (gas_of gs)-(word_of_int c),
                        ct_of := (ct_of gs) + 1\<rparr>,
                     Some ((NL v) :L U256))
              else (gs, None)
          )
      | (SLoad, [NL a]) \<Rightarrow> (
          if (valid (gas_of gs) 200 ((ct_of gs)+1)) 
          then (
             let from = addr_of gs in 
               (case (accs_of gs from) of 
                 Some cur_acc \<Rightarrow>       
                  let v = ((store_of cur_acc)(word_of_int a)) in
                    (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 200), ct_of := (ct_of gs) + 1\<rparr>,
                     Some ((NL (uint v)) :L U256)) 
                )   
             )
          else (gs, None) 
         )
      | (Keccak256, [NL p, NL sz]) \<Rightarrow> (
           let naws = (ext_mem_sz (naws_of gs) p sz) in  
            let c = (Cmem (uint(naws_of gs)) (uint naws)) + 30 + (6*(ceiling_div sz 32)) in
              if (valid (gas_of gs) (nat c) ((ct_of gs)+1))
              then (
                 let v = get_mem_bytes (mem_of gs) p (nat (sz)) in
                  let h = keccak v in
                    (gs\<lparr> naws_of := naws, 
                         gas_of := (gas_of gs)-(word_of_int c), 
                         ct_of := (ct_of gs) + 1\<rparr>,
                     Some ((NL (uint h)) :L U256)) 
                )
             else (gs, None) 
          ) 
      | _ \<Rightarrow> (gs, None)
  )" 

definition eval_wbuiltin :: "gstate \<Rightarrow> wbuiltin \<Rightarrow> (lit_content)list \<Rightarrow> (gstate * bool) " where
  "eval_wbuiltin gs bb lst = (
    case (bb, lst) of
       (MStore, [NL a, NL b]) \<Rightarrow> (
          let b' = int_to_byte_lst b 32 in
           let naws = (ext_mem_sz (naws_of gs) a (int 32)) in
            let c = (Cmem (uint(naws_of gs)) (uint naws)) + 3 in
             if (valid (gas_of gs) (nat c) (ct_of gs))
             then (gs\<lparr> naws_of := naws, gas_of := (gas_of gs)-(word_of_int c),
                   mem_of := (upd_mem_bytes (mem_of gs) a (int 32) b') \<rparr>, True)
             else (gs, False) 
         )
      | (MStore8, [NL a, NL b]) \<Rightarrow> (
             let naws = (ext_mem_sz (naws_of gs) a (int 1)) in
             let b' = rev (int_to_byte_lst b 32) in
              let mem = ( \<lambda>(x::256 word). 
                if (x = (word_of_int a))
                then ((b' ! (nat ((uint x) - a))) mod (word_of_int 256))
                else 
                  ((mem_of gs) x) mod (word_of_int 256) )
                  in (
                      let c = (Cmem (uint(naws_of gs)) (uint naws)) + 3 in
                       if (valid (gas_of gs) (nat c) (ct_of gs))
                       then (gs\<lparr> naws_of := naws, gas_of := (gas_of gs)-(word_of_int c),
                           mem_of := mem \<rparr>, True)
                       else (gs, False)
                  )
          )
      | (SStore, [NL a, NL b]) \<Rightarrow> (
           let from = addr_of gs in 
             ( case (accs_of gs from) of 
                Some cur_acc \<Rightarrow>       
                let stor = (\<lambda> (x::256 word) . if (x =(word_of_int a)) 
                                              then (word_of_int b)
                                              else ((store_of cur_acc) x))
                in (
                let r = (if (b = 0 \<and> (((store_of cur_acc)(word_of_int a)) \<noteq> 0)) 
                          then (int 15000) else (0))
                in(
                let c = (if (b \<noteq> 0 \<and> (((store_of cur_acc)(word_of_int a)) = 0))
                         then (20000) else (5000))
                in( 
                   if (valid (gas_of gs) (nat c) (ct_of gs)) 
                   then (gs\<lparr> accs_of := ((accs_of gs)(from := Some (cur_acc\<lparr> store_of := stor \<rparr>))),
                             gas_of := (gas_of gs)-(word_of_int c),
                             refund_of := ((refund_of gs)+(word_of_int r)) \<rparr>, True)
                   else (gs, False)) 
                ))
             )
         )
      | (CalldataCopy, [NL pm, NL pd, NL psz]) \<Rightarrow> (
           let naws = (ext_mem_sz (naws_of gs) pm psz) in
            let v = 
              if (int(size (input_of gs)) - pd < 0) then 0
              else (
                 memory_integer_bigendian 
                  (fill_zero (input_of gs) ((pd+psz) - int(size (input_of gs)))) pd (nat psz)
               )
              in
               let c = (Cmem (uint(naws_of gs)) (uint naws)) + 3 + (3*(ceiling_div psz 32)) in
                 if (valid (gas_of gs) (nat c) (ct_of gs))   
                 then (gs\<lparr> mem_of := (upd_mem_bytes (mem_of gs) pm (psz) [word_of_int v]),
                           gas_of := (gas_of gs)-(word_of_int c), naws_of := naws \<rparr>, True) 
                 else (gs, False)  
          )   
      | (Log0, [NL a, NL s]) \<Rightarrow> (
           let naws = (ext_mem_sz (naws_of gs) a s) in
            let data = (get_mem_bytes (mem_of gs) a (nat(s))) in
             let from = (addr_of gs) in
              let lg0 = (\<lparr> address_of = from, args_of = [], mem_frag_of = data \<rparr>)
                 in(
                   let c = (Cmem (uint(naws_of gs)) (uint naws)) + 375 + 8*s in
                    if (valid (gas_of gs) (nat c) (ct_of gs)) 
                    then ( gs\<lparr> logs_of := (logs_of gs)@[lg0],
                               gas_of := (gas_of gs)-(word_of_int c),
                               naws_of := naws \<rparr>, True )
                    else (gs, False)
                   )
          )
      | (Log1, [NL a, NL s, NL t1]) \<Rightarrow> (
           let naws = (ext_mem_sz (naws_of gs) a s) in
            let data = (get_mem_bytes (mem_of gs) a (nat(s))) in
             let from = (addr_of gs) in
              let lg0 = (\<lparr> address_of = from, args_of = [], mem_frag_of = data \<rparr>) in
              let lg1 = (\<lparr> address_of = from, args_of = [(word_of_int t1)], mem_frag_of = data \<rparr>)
                in(
                  let c = (Cmem (uint(naws_of gs)) (uint naws)) + 375 + 8*s + 375 in
                   if (valid (gas_of gs) (nat c) (ct_of gs))
                   then (gs\<lparr> logs_of := (logs_of gs)@[lg0]@[lg1],
                             gas_of := (gas_of gs)-(word_of_int c),
                             naws_of := naws \<rparr>, True)
                   else (gs, False) 
                  )
          )
       | (Log2, [NL a, NL s, NL t1, NL t2]) \<Rightarrow> (
           let naws = (ext_mem_sz (naws_of gs) a s) in
            let data = (get_mem_bytes (mem_of gs) a (nat(s))) in
             let from = (addr_of gs) in
               let lg0 = (\<lparr> address_of = from, args_of = [], mem_frag_of = data \<rparr>) in
               let lg1 = (\<lparr> address_of = from, args_of = [(word_of_int t1)], mem_frag_of = data \<rparr>) in
               let lg2 = (\<lparr> address_of = from, args_of = [(word_of_int t2)], mem_frag_of = data \<rparr>)
                 in(
                   let c = (Cmem (uint(naws_of gs)) (uint naws)) + 375 + 8*s + 2*375 in
                    if (valid (gas_of gs) (nat c) (ct_of gs))
                    then (gs\<lparr> logs_of := (logs_of gs)@[lg0]@[lg1]@[lg2],
                              gas_of := (gas_of gs)-(word_of_int c),
                              naws_of := naws \<rparr>, True ) 
                    else (gs, False)
                   )
                )
       | (Log3, [NL a, NL s, NL t1, NL t2, NL t3]) \<Rightarrow> (
           let naws = (ext_mem_sz (naws_of gs) a s) in
            let data = (get_mem_bytes (mem_of gs) a (nat(s))) in
             let from = (addr_of gs) in
              let lg0 = (\<lparr> address_of = from, args_of = [], mem_frag_of = data \<rparr>) in
              let lg1 = (\<lparr> address_of = from, args_of = [(word_of_int t1)], mem_frag_of = data \<rparr>) in
              let lg2 = (\<lparr> address_of = from, args_of = [(word_of_int t2)], mem_frag_of = data \<rparr>) in
              let lg3 = (\<lparr> address_of = from, args_of = [(word_of_int t3)], mem_frag_of = data \<rparr>)
               in(
                 let c = (Cmem (uint(naws_of gs)) (uint naws)) + 375 + 8*s + 3*375 in
                  if (valid (gas_of gs) (nat c) (ct_of gs)) 
                  then (gs\<lparr> logs_of := (logs_of gs)@[lg0]@[lg1]@[lg2]@[lg3],
                            gas_of := (gas_of gs)-(word_of_int c),
                            naws_of := naws \<rparr>, True)
                  else (gs, False)
                 )
          )
       | (Log4, [NL a, NL s, NL t1, NL t2, NL t3, NL t4]) \<Rightarrow> (
           let naws = (ext_mem_sz (naws_of gs) a s) in
            let data = (get_mem_bytes (mem_of gs) a (nat(s))) in
             let from = (addr_of gs) in
              let lg0 = (\<lparr> address_of = from, args_of = [], mem_frag_of = data \<rparr>) in
              let lg1 = (\<lparr> address_of = from, args_of = [(word_of_int t1)], mem_frag_of = data \<rparr>) in
              let lg2 = (\<lparr> address_of = from, args_of = [(word_of_int t2)], mem_frag_of = data \<rparr>) in
              let lg3 = (\<lparr> address_of = from, args_of = [(word_of_int t3)], mem_frag_of = data \<rparr>) in
              let lg4 = (\<lparr> address_of = from, args_of = [(word_of_int t3)], mem_frag_of = data \<rparr>)
               in(
                 let c = (Cmem (uint(naws_of gs)) (uint naws)) + 375 + 8*s + 4*375 in
                  if (valid (gas_of gs) (nat c) (ct_of gs)) 
                  then (gs\<lparr> logs_of := (logs_of gs)@[lg0]@[lg1]@[lg2]@[lg3]@[lg4],
                            gas_of := (gas_of gs)-(word_of_int c),
                            naws_of := naws \<rparr>, True )
                  else (gs, False)
                 )
          )

  )"

definition eval_hdrbuiltin :: 
  "trans_env \<Rightarrow> gstate \<Rightarrow> hdrbuiltin \<Rightarrow> (lit_content)list \<Rightarrow> (gstate*(literal option))" where
  "eval_hdrbuiltin tre gs hb lst = (
   case (hb,lst) of 
       (Difficulty, []) \<Rightarrow> (
         if (valid (gas_of gs) 2 ((ct_of gs)+1))
         then (
            let hd = (bheader_of tre) in 
             let v = uint (difficulty_of hd)
              in (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 2),
                     ct_of := (ct_of gs) + 1\<rparr>,
                  Some ((NL v) :L U256)) 
          )
         else (gs, None) 
          )
    | (Number, []) \<Rightarrow> (
         if (valid (gas_of gs) 2 ((ct_of gs)+1))
         then (
            let hd = (bheader_of tre) in 
             let v = uint (number_of hd)
               in (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 2),
                      ct_of := (ct_of gs) + 1\<rparr>,
                   Some ((NL v) :L U256))
          )
         else (gs, None)
        )
    | (Timestamp, []) \<Rightarrow> (
        if (valid (gas_of gs) 2 ((ct_of gs)+1))
        then (
            let hd = (bheader_of tre) in 
              let v = uint (time_stamp_of hd)
                in (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 2),
                       ct_of := (ct_of gs) + 1\<rparr>,
                    Some ((NL v) :L U256))
          )
        else (gs, None)
        )
    | (CoinBase, []) \<Rightarrow> (
         if (valid (gas_of gs) 2 ((ct_of gs)+1))
         then (
            let hd = (bheader_of tre) in 
              let v = uint (beneficiary_of hd)
                in (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 2),
                       ct_of := (ct_of gs) + 1\<rparr>,
                    Some ((NL v) :L U256))
          )
         else (gs, None)
        )
    | (GasLimit, []) \<Rightarrow> (
         if (valid (gas_of gs) 2 ((ct_of gs)+1))
         then (
            let hd = (bheader_of tre) in 
              let v = uint (gas_limit_of hd)
                in (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 2),
                       ct_of := (ct_of gs) + 1\<rparr>,
                    Some ((NL v) :L U256))
          )
         else (gs, None)
        )
    | (GasPrice, []) \<Rightarrow> (
        if (valid (gas_of gs) 2 ((ct_of gs)+1))
        then (
            let v = uint (gprice_of tre)
             in (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 2),
                    ct_of := (ct_of gs) + 1\<rparr>,
                 Some ((NL v) :L U256))
          )
        else (gs, None)
        )
    | (Origin, []) \<Rightarrow> (
        if (valid (gas_of gs) 2 ((ct_of gs)+1))
        then (
            let v = uint (oaddr_of tre)
             in (gs\<lparr>gas_of := (gas_of gs)-(word_of_int 2),
                    ct_of := (ct_of gs) + 1\<rparr>,
                 Some ((NL v) :L U256))
          )
        else (gs, None)
        )

  )"

(* (literal option) *)

fun addr_lab_lst :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "addr_lab_lst [] lit _ _ = 0" |
  "addr_lab_lst lst lit _ 0 = 0" |
  "addr_lab_lst lst lit k (Suc n) = (
     if (lst!k = lit) then (k+1) else (addr_lab_lst lst lit (k+1) n)
  )"

value "addr_lab_lst [4::int,5,6,7,3] 3 0 (size[4::int,5,6,7,3])"
value "addr_lab_lst [GPOP::expr,GPOP,GSWAP,GJUMP] GSWAP 0 (size[GPOP::expr,GPOP,GSWAP,GJUMP])"

value "(take (nat 2) [5::int,11,3,4,6]) @ [2] @ (drop (nat 2+1) [5::int,11,3,4,6])"
value "[5::int, 11, 2, 4, 6]!2"
value "take ((size [1::int,2,3])-1) [1::int,2,3]"

fun change_layout :: " int list \<Rightarrow> nat \<Rightarrow> int list" where
  "change_layout lst 0 = []" |
  "change_layout lst (Suc n) = (
    case lst of 
      [] \<Rightarrow> []
    | _ \<Rightarrow> (
      let j = (last lst) in
      let lst' = take ((size lst)-1) lst in
      if (int (size lst') \<ge> j \<and> int (size lst') \<le> 17)
      then (
         if (j < 0) 
         then (
             let GPOP_id = 2 in
              [GPOP_id] @ change_layout (take ((size lst)-1) lst) (Suc n)
          ) 
         else (
           if (j = int (size lst'))
           then []
           else (
              let SWAP_id = 3 in
              let lst'' = (take (nat j) lst') @ [j] @ (drop (nat j+1) lst') @ [lst'!(nat j)] in
              [SWAP_id] @ change_layout lst'' n
            )
         )
      )
      else []
    )
  )"

value "change_layout [1, 0] 2" 
value "change_layout [2, 0, 1] 3"
value "change_layout [3, 0, 1, 2] 4" 

value "change_layout [1, -1, 0] 3"
value "change_layout [2, -1, 0, 1] 4"
value "change_layout [3, -1, 0, 1, 2] 5"

value "change_layout [1, -1, -1, 0] 4"
value "change_layout [2, -1, -1, 0, 1] 5"
value "change_layout [3, -1, -1, 0, 1, 2] 10"

fun n_num_list :: "int \<Rightarrow> nat \<Rightarrow> int list" where
  "n_num_list _ 0 = []" |
  "n_num_list num (Suc n) = [num] @ n_num_list num n"

value "n_num_list (-1) 8"
value "change_layout ([9::int]@(n_num_list (-1) 4)@[1 .. 8]) 10"

fun n_expr_lst :: " expr list \<Rightarrow> expr \<Rightarrow> nat \<Rightarrow> expr list" where
 "n_expr_lst es e 0 = es" | 
 "n_expr_lst es e (Suc n) = (
     (n_expr_lst es e n) @ [e]
  )"

value "[GPOP]"
value "n_expr_lst [GJUMP] GPOP 2"
value "n_expr_lst [] GPOP (nat(n_int_lst (change_layout ([9::int]@(n_num_list (-1) 4)@[1 .. 8]) 10) 3))"

fun num_change_expr_lst :: "int list \<Rightarrow> expr list" where
  "num_change_expr_lst [] = []"|
  "num_change_expr_lst l = (
    case l of 
      n#lst \<Rightarrow> (if n=2 then ([GPOP]@(num_change_expr_lst lst))
                else (if n = 3 then ([GSWAP]@(num_change_expr_lst lst))
                      else (num_change_expr_lst lst)
                  )
            )
  )"
value "num_change_expr_lst (change_layout ([9::int]@(n_num_list (1) 4)@[1 .. 8]) 10)"

definition concat_blk_es :: "block \<Rightarrow> expr list \<Rightarrow> block" where
  " concat_blk_es blk es = (
    case blk of 
      (Blk es') \<Rightarrow> (Blk (es'@es))
  )"

definition concat_es_blk :: " expr list \<Rightarrow> block \<Rightarrow> block" where
  " concat_es_blk es blk = (
    case blk of 
    (Blk es') \<Rightarrow> (Blk (es@es'))
  )"

definition blks_concat :: "block \<Rightarrow> block \<Rightarrow> block" where
  "blks_concat blk1 blk2 = (
    case blk1 of (Blk es1) \<Rightarrow> (case blk2 of (Blk es2) \<Rightarrow> Blk (es1 @ es2))
  )"

value "blks_concat (Blk [GJUMP]) (Blk [GPUSH, GPOP])"

definition peel where "peel e = (case e of EImLit lit \<Rightarrow> lit)" 

definition lkind_of_lit where "lkind_of_lit e = (case e of (EImLit (Literal lkind _)) \<Rightarrow> lkind)"

definition is_lit_expr where "is_lit_expr e = (case e of (EImLit _) \<Rightarrow> False | _ \<Rightarrow> True)"

definition wrap_with_lit where 
  "wrap_with_lit e = (case e of (EImLit lit) \<Rightarrow> lit | _ \<Rightarrow> ((NL 0) :L U256))"

function (sequential, domintros) 
  step :: "trans_env \<Rightarrow> gstack \<Rightarrow> nat \<Rightarrow> gstack"  and 
  step_ctx :: "trans_env \<Rightarrow> expr \<Rightarrow> ectx \<Rightarrow> gstack \<Rightarrow> nat \<Rightarrow> gstack" where

  (* a step of ec[e] -- the context ec filled with the expression e *)
  "step_ctx tre e ec [GFrmNormal (LFrm_E (_, ls, fs) # lstk') gs ck] (Suc n) = (
    case (step tre [(GFrmNormal (LFrm_E (e, ls, fs) # lstk') gs ck)]) n of
      [GFrmNormal (LFrm_E (e', ls', fs') # lstk') gs' ck'] \<Rightarrow> 
        [GFrmNormal (LFrm_E (hfill_e ec e', ls', fs') # lstk') gs' ck']
    | [GFrmNormal ((LFrm_B (b, ls', fs', cf)) # (LFrm_E (e', ls, fs)) # lstk') gs ck] \<Rightarrow> 
      [GFrmNormal ((LFrm_B (b, ls', fs', cf)) # (LFrm_E (hfill_e ec e', ls, fs)) # lstk')
                  gs ck]
    | [GFrmExc ck] \<Rightarrow> [GFrmExc ck]
    | gfrm # [(GFrmNormal (LFrm_E (e', ls, fs) # lstk') gs ck)] \<Rightarrow> 
      gfrm # [GFrmNormal ((LFrm_E (hfill_e ec e', ls, fs)) # lstk') gs ck]
    | [GFrmCounterErr] \<Rightarrow> [GFrmCounterErr]
    | _ \<Rightarrow> []
  )" | 
  "step_ctx _ _ _ _ 0 = [GFrmCounterErr]" | 
  "step_ctx _ _ _ _ _ = []" |

  "step tre _ 0 = [GFrmCounterErr]" |

  "step tre [GFrmNormal (LFrm_E (GJUMPDEST, ls, fs) # lstk') gs ck] (Suc n) = ( 
        if (valid_gas_cost (gas_of gs) 1) 
        then ( let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 1)\<rparr> in
            [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs' ck]
         )
        else [GFrmExc ck]
     )" | 
  "step tre [GFrmNormal (LFrm_E (GJUMP, ls, fs) # lstk') gs ck] (Suc n) = ( 
        if (valid_gas_cost (gas_of gs) 8) 
        then ( let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 8)\<rparr> in
            [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs' ck]
         )
        else [GFrmExc ck]
     )" | 
  "step tre [GFrmNormal (LFrm_E (GPUSH, ls, fs) # lstk') gs ck] (Suc n) = ( 
        if (valid_gas_cost (gas_of gs) 3) 
        then ( let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 3)\<rparr> in
            [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs' ck]
         )
        else [GFrmExc ck] 
     )" |
  "step tre [GFrmNormal (LFrm_E (GSWAP, ls, fs) # lstk') gs ck] (Suc n) = ( 
        if (valid_gas_cost (gas_of gs) 3) 
        then ( let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 3)\<rparr> in
            [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs' ck]
         )
        else [GFrmExc ck]
     )" |
  "step tre [GFrmNormal (LFrm_E (GPOP, ls, fs) # lstk') gs ck] (Suc n) = ( 
        if (valid_gas_cost (gas_of gs) 2) 
        then ( let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 2)\<rparr> in
            [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs' ck]
         )
        else [GFrmExc ck]
     )" | 

  "step tre [GFrmNormal (LFrm_E (EId x, ls, fs) # lstk') gs ck] (Suc n) = ( 
    case (lm_get ((aggr_ls lstk') @ ls) x) of 
      Some lit \<Rightarrow> (if (valid (gas_of gs) 3 ((ct_of gs)+1))
                    then ( let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 3),
                                        ct_of := (ct_of gs) + 1\<rparr> in
                        [GFrmNormal (LFrm_E (EImLit lit, ls, fs) # lstk') gs' ck]
                    )
                     else [GFrmExc ck]
                 ) 
    | _ \<Rightarrow> []
  )" | 
  "step tre [GFrmNormal (LFrm_E (ELit lit, ls, fs) # lstk') gs ck] (Suc n) = ( 
      if (valid (gas_of gs) 3 ((ct_of gs)+1)) 
      then ( let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 3),
                          ct_of := (ct_of gs) + 1\<rparr> in
          [GFrmNormal (LFrm_E (EImLit lit, ls, fs) # lstk') gs' ck]
       )
      else [GFrmExc ck]
   )" | 
  "step tre [GFrmNormal (LFrm_E (FUN f pl rl IS blk, ls, fs) # lstk') gs ck] (Suc n) = 
      [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck]
    " |
  "step tre [GFrmNormal (LFrm_E (ECond e blk, ls, fs) # lstk') gs ck] (Suc n) = (
     case e of
      (EImLit (TL :L Bool)) \<Rightarrow> 
        if (valid (gas_of gs) (3+3+10) (ct_of gs)) 
        then (  let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 16)\<rparr> in
                [GFrmNormal (LFrm_B (blk, [], get_func_values blk, None)
                     # (LFrm_E (STOP, ls, fs))
                     # lstk') gs' ck]
        )
        else [GFrmExc ck]
    | (EImLit (FL :L Bool)) \<Rightarrow> 
         if (valid (gas_of gs) (3+3+10) (ct_of gs))
         then (  let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int 16)\<rparr> in
                [GFrmNormal (LFrm_E (GJUMPDEST, ls, fs) # lstk') gs' ck]
          )
         else [GFrmExc ck]
    | _ \<Rightarrow> (
        step_ctx tre e (ECCond (Hole) blk)  
          [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck] n
      )
    )
  " |
  "step tre [GFrmNormal (LFrm_E (IF e THEN blk, ls, fs) # lstk') gs ck] (Suc n) = 
    [GFrmNormal (LFrm_E (ECond e (concat_blk_es blk [GJUMPDEST]), ls, fs) # lstk') gs ck]
  " |
  "step tre 
    [GFrmNormal (LFrm_E (SWITCH e CASES cases DEFAULT blk_opt, ls, fs) # lstk') gs ck] (Suc n) 
   = (
       let sz_cases = (size cases) in 
          case e of 
            EImLit lit \<Rightarrow>
            let lit_cases = filter (\<lambda> (lit', blk'). eval_lit (EImLit lit) = eval_lit (EImLit lit')) cases 
            in 
            (
              case lit_cases of 
                [] \<Rightarrow> (
                  if (sz_cases = 0) 
                  then (
                     case blk_opt of 
                       Some blk \<Rightarrow> 
                        [GFrmNormal (LFrm_B ((concat_blk_es blk [GPOP]), [], get_func_values blk, None)
                                     # (LFrm_E (STOP, ls, fs)) # lstk') gs ck]
                     | None \<Rightarrow> [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck]
                   )
                  else (   
                    if (valid (gas_of gs) (sz_cases*(3+3+3+3+10)) (ct_of gs))
                    then (
                      let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int (int (sz_cases*(3+3+3+3+10))))\<rparr> in
                      case blk_opt of 
                        Some blk \<Rightarrow> 
                         [GFrmNormal (LFrm_B ((concat_blk_es blk [GPUSH, GJUMP, GJUMPDEST, GPOP]),
                                              [], get_func_values blk, None)
                                      # (LFrm_E (STOP, ls, fs)) # lstk') gs' ck]
                      | None \<Rightarrow> 
                         [GFrmNormal (LFrm_B ((Blk [GPUSH, GJUMP, GJUMPDEST, GPOP]), [], [], None)
                                      # (LFrm_E (STOP, ls, fs)) # lstk') gs' ck]
                     )
                    else [GFrmExc ck]
                  )
               )
              | (l, blk) # lit_cases' \<Rightarrow>
                let exe_gas = (addr_lab_lst cases (l, blk) 0 (size cases)) * (3+3+3+3+10) in
                  if (valid (gas_of gs) (exe_gas) (ct_of gs)) 
                   then (
                     let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int (int (exe_gas))) \<rparr> in
                     let blk' = 
                       if (l = fst (last(cases))) 
                       then (concat_es_blk [GJUMPDEST] (concat_blk_es blk [GJUMPDEST, GPOP]))
                       else (concat_es_blk [GJUMPDEST] (concat_blk_es blk [GPUSH, GJUMP, GJUMPDEST, GPOP])) 
                     in 
                        [GFrmNormal (LFrm_B (blk', [], get_func_values blk, None) 
                                      # (LFrm_E (STOP, ls, fs))
                                      # lstk') gs' ck]
                  ) 
                  else [GFrmExc ck]
            )
          | _ \<Rightarrow> 
            step_ctx tre e (ECSwitch Hole cases blk_opt) 
                            [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck] (Suc n)
  )" | 
  "step tre [GFrmNormal (LFrm_E (FOR blk0 e blk1 blk, ls, fs) # lstk') gs ck] (Suc n) = (
      case blk0 of 
        BEGIN es0 END \<Rightarrow> (
         [GFrmNormal (LFrm_B (Blk (es0 @ [GJUMPDEST] @ [(ECond e (
                                              concat_blk_es (blks_concat blk blk1)
                                             ([GPUSH, GJUMP] @ [(FOR (BEGIN [] END) e blk1 blk)])
                                               ))])
                              , 
                              [], [], None) 
                     # LFrm_E (STOP, ls, fs) # lstk') gs ck]
        )
    )
  " | 
  "step tre [GFrmNormal (LFrm_E (xs ::= e, ls, fs) # lstk') gs ck] (Suc n) = (
    case e of 
      EImLit lit \<Rightarrow> (
        let new_lstk = upd_var_in_lstack (LFrm_E (STOP, ls, fs) # lstk') (xs!0) lit in
        let xs_size = int (size xs) in 
        if (valid (gas_of gs) (5 * (nat xs_size)) (ct_of gs))  
        then (let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int (5*xs_size))\<rparr> in 
                 [GFrmNormal new_lstk gs' ck]
             )
        else [GFrmExc ck]
      )
    | EList es \<Rightarrow> (
        let lits = map (\<lambda>e. ( case e of (EImLit lit) \<Rightarrow> lit | _ \<Rightarrow> ((NL 0) :L U256) ) ) es in 
        let xs_lits = zip xs lits in 
        let new_lstk = 
          (foldl (\<lambda>lstk_acc (x, lit). upd_var_in_lstack lstk_acc x lit) 
                  (LFrm_E (STOP, ls, fs) # lstk') xs_lits) in
        let xs_size = int (size xs) in 
        if (valid (gas_of gs) (5 * (nat xs_size)) (ct_of gs)) 
        then (let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int (5*xs_size))\<rparr> in 
             [GFrmNormal new_lstk gs' ck])
        else [GFrmExc ck]
      )
    | _ \<Rightarrow> 
      step_ctx tre e (ECAssg xs Hole) [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck] (Suc n) 
  )
  "  |
  "step tre [GFrmNormal (LFrm_E ((VAR txs ::- e), ls, fs) # lstk') gs ck] (Suc n) = (
    case e of 
      EImLit lit \<Rightarrow> [GFrmNormal (LFrm_E (STOP, ls @ [(fst (txs!0), lit)], fs) # lstk') gs ck]
    | EList es \<Rightarrow> (
        let lits = map (\<lambda>e. (case e of (EImLit lit) \<Rightarrow> lit | _ \<Rightarrow> ((NL 0) :L U256))) es in
          [GFrmNormal (LFrm_E (STOP, ls @ (zip (map fst txs) lits), fs) # lstk') gs ck]
      )
    | _ \<Rightarrow> 
      step_ctx tre e (ECVarDecl txs Hole) [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck] (Suc n)
  )
  " |
  "step tre [GFrmNormal (LFrm_E (VAR txs, ls, fs) # lstk') gs ck] (Suc n) = (
    let zeros = map (\<lambda>(x, t). (if t=Bool then ((FL) :L Bool) else ((NL 0) :L U256))) txs in 
    let txs_size = int (size txs) in 
       if (valid (gas_of gs) (3 * (nat txs_size)) ((ct_of gs)+(nat txs_size)))
       then (let gs' = gs\<lparr>gas_of := (gas_of gs)-(word_of_int (3*txs_size)),
                          ct_of := (ct_of gs)+(nat txs_size)\<rparr> in 
             [GFrmNormal (LFrm_E (STOP, ls @ (zip (map fst txs) zeros), fs) # lstk') gs' ck] 
          )
       else [GFrmExc ck]
  )" |
  "step tre [GFrmNormal (LFrm_E (CALL f es, ls, fs) # lstk') gs ck] (Suc n) = (
    if (f \<notin> lm_dom builtin_ctx) \<and> (valid (gas_of gs) 3 (ct_of gs)) then (
      let gs' = gs \<lparr> gas_of := (gas_of gs) - 3 \<rparr> in 
      [GFrmNormal (LFrm_E (EImFunCall f es, ls, fs) # lstk') gs' ck]
    ) else (
      if (f \<in> lm_dom builtin_ctx) then 
        [GFrmNormal (LFrm_E (EImFunCall f es, ls, fs) # lstk') gs ck]
      else 
        [GFrmExc ck]
    )
  )" |
  "step tre [GFrmNormal (LFrm_E (EImFunCall f es, ls, fs) # lstk') gs ck] (Suc n) = (
      let (idx, found) = lst_find_idx (rev es) is_lit_expr in
      (
        if found then (
          step_ctx 
          tre (es!(length es - idx - 1)) 
            (ECFunCall f (take (length es-idx-1) es) Hole (map peel (drop (length es - idx) es)))
            [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck] (Suc n)
        )
        else ( 
          case lm_get ((aggr_fs (LFrm_E (EImFunCall f es, ls, fs) # lstk')) @ builtin_ctx) f of 
             Some (FunctionV f ptl rtl blk) \<Rightarrow> ( 
               let sz_ptl = (size ptl) in
               let sz_rtl = (size rtl) in
               let C' = (change_layout ([(int sz_rtl)] 
                         @ (n_num_list (-1) sz_ptl) @ [0 .. (int sz_rtl-1)] ) 18) in 
               let lits = map (wrap_with_lit) es in
               let rzl = map (\<lambda>(x, tn) \<Rightarrow> 
                              (x, (if tn = Bool then ((FL) :L Bool) else ((NL 0) :L tn)))) rtl in 
               let fs' = (get_func_values blk) in 
               [GFrmNormal 
                 (LFrm_B 
                        (concat_blk_es (concat_es_blk
                          (n_expr_lst [GPUSH, GJUMP, GJUMPDEST] GPUSH (size rtl)) blk)
                          ((num_change_expr_lst C')),
                        (zip (map fst ptl) lits) @ rzl, fs', Some (FunctionV f ptl rtl blk))
                 # LFrm_E ((if (length rtl\<noteq>0) then (EList (map (\<lambda>xt. (ERetId xt)) rtl)) else STOP),
                            ls, fs) 
                 # lstk') gs ck]
               )
            | Some (OpBuiltinV bid) \<Rightarrow> (
               let lits = (map lkind_of_lit es) in 
                (case (eval_opbuiltin gs bid lits) of
                   (gs', Some v) \<Rightarrow> [GFrmNormal (LFrm_E ((EImLit v), ls, fs) # lstk') gs' ck]
                 | (gs, None) \<Rightarrow> [GFrmExc ck]
                )
              )  
            | Some (CallBuiltinV callgb) \<Rightarrow> (
               let lits = (map lkind_of_lit es) in 
               if (callgb \<in> {Call, CallCode, DelegateCall, Return, Revert, Selfdestruct, 
                             Stop, Invalid})
               then (step_callbuiltin 
                        (GFrmNormal (LFrm_E (EImFunCall f es, ls, fs) # lstk') gs ck) callgb lits) 
               else [GFrmExc ck]
               )
            | Some (RBuiltinV gb) \<Rightarrow> (
               let lits = (map lkind_of_lit es) in 
                (case (eval_rbuiltin gs gb lits) of
                   (gs', (Some v)) \<Rightarrow> [GFrmNormal (LFrm_E ((EImLit v), ls, fs) # lstk') gs' ck]
                 | (gs', None) \<Rightarrow> [GFrmExc ck] 
                )
              )   
            | Some (HdRBuiltinV hb) \<Rightarrow> (
               let lits = (map lkind_of_lit es) in 
                (case (eval_hdrbuiltin tre gs hb lits) of
                   (gs', Some v) \<Rightarrow> [GFrmNormal (LFrm_E ((EImLit v), ls, fs) # lstk') gs' ck]
                 | (gs', None) \<Rightarrow> [GFrmExc ck] 
                )
              )   
            | Some (WBuiltinV bb) \<Rightarrow> (
                 let lits = (map lkind_of_lit es) in (
                    case (eval_wbuiltin gs bb lits) of
                     (gs', True) \<Rightarrow> [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs' ck]
                   | (gas', False) \<Rightarrow> [GFrmExc ck] 
                  )
               )   
          ) 
      )
    )
  " |

  "step tre ((GFrmNormal (LFrm_B (BEGIN es END, ls, fs, fg) # lstk') gs ck) # gstk') (Suc n) = (
    case es of 
      e # es' \<Rightarrow> (
        case (step tre [(GFrmNormal (LFrm_E (e, ls, fs) # lstk') gs ck)] n) of 
          [(GFrmNormal (LFrm_E (e', ls', fs') # lstk') gs' ck')] \<Rightarrow> (
            ((GFrmNormal (LFrm_B (BEGIN (if e' = STOP then es' else e'#es') END, 
                                  ls', fs', fg)
                          # lstk') gs' ck') # gstk')
          )
        | [(GFrmNormal ((LFrm_B (b, ls', fs', fg')) # (LFrm_E (e', ls, fs)) # lstk') gs' ck')] \<Rightarrow>
             let es' = (if (fs'\<noteq>[] \<or> fs\<noteq>[])\<and>(es' = [])\<and>(lstk' = [])
               then ([GPUSH, GJUMP, GJUMPDEST]) else (es')) in
            (GFrmNormal 
              ((LFrm_B (b, ls', fs', fg')) 
               # (LFrm_B (BEGIN (if e' = STOP then es' else e'#es') END, ls, fs, fg))
               # lstk') gs' ck')
            # gstk'
        | [GFrmHalt gs'' ret_data ck''] \<Rightarrow> (GFrmHalt gs'' ret_data ck'') # gstk'
        | [GFrmExc ck'']  \<Rightarrow> (GFrmExc ck'') # gstk'
        | gfrm # [(GFrmNormal (LFrm_E (e', ls', fs') # lstk') gs' ck')] \<Rightarrow> (
          if (size gstk' + 2 \<le> 1024) then 
            gfrm # ((GFrmNormal (LFrm_B (BEGIN e' # es' END, ls', fs, fg) # lstk')) gs' ck') # gstk'
          else GFrmExc ck # gstk')
      )
      | _ \<Rightarrow> (
        let gas_ls =
          (case fg of 
            Some (FunctionV f ptl rtl blk) \<Rightarrow> 8+1 + 2*word_of_int (int (card (set (map fst ls))
                                              - (size ptl) - (size rtl))) 
           | _ \<Rightarrow> 2*word_of_int (int (card (set (map fst ls))))
          )  
         in
           if (valid_gas_cost (gas_of gs) (gas_ls)) 
           then (
             let gs1 = gs\<lparr>gas_of := (gas_of gs)-gas_ls\<rparr> in  
              case lstk' of 
                (LFrm_B (b, ls', fs', fg')) # lstk'' \<Rightarrow> (
                  if fg = None then 
                    (GFrmNormal ((LFrm_B (b, ls', fs', fg')) # lstk'') gs1 ck) # gstk'
                  else (
                    case b of 
                      BEGIN e'' # es'' END \<Rightarrow> (
                        case expr_fill_retids e'' ls of 
                          e''' \<Rightarrow> 
                            ((GFrmNormal ((LFrm_B (BEGIN (e''' # es'') END, ls', fs', fg')) 
                                          # lstk'') gs1 ck) # gstk')
                      )
                    | _ \<Rightarrow> ((GFrmNormal ((LFrm_B (b, ls', fs', fg')) # lstk'') gs1 ck)) # gstk'
                  )
                )
              | (LFrm_E (e, ls', fs')) # lstk'' \<Rightarrow> (
                  if fg = None then 
                    ((GFrmNormal ((LFrm_E (e, ls', fs')) # lstk'') gs1 ck)) # gstk'
                  else (
                    case expr_fill_retids e ls of 
                      e'' \<Rightarrow> ((GFrmNormal ((LFrm_E (e'', ls', fs')) # lstk'') gs1 ck) # gstk')
                  )
                )
              | [] \<Rightarrow> ((GFrmHalt gs1 [] ck) # gstk')
           ) 
           else (GFrmExc ck # gstk')
        )
   )" |

  "step tre ((GFrmHalt gs' ret_data ck') # gstk') (Suc n) = (
    case gstk' of 
      _ # _ \<Rightarrow> (
        case ck' of 
          (CKCall _ _ _ _ _ _ _) \<Rightarrow> callret ((GFrmHalt gs' ret_data ck') # gstk') 
        | (CKCallCode _ _ _ _ _ _ _) \<Rightarrow> callcoderet ((GFrmHalt gs' ret_data ck') # gstk') 
        | (CKDelCall _ _ _ _ _ _) \<Rightarrow> delcallret ((GFrmHalt gs' ret_data ck') # gstk') 
      )
      | _ \<Rightarrow> [(GFrmHalt gs' ret_data ck')]
  )"                                                       
|
  "step tre 
    (GFrmExc (CKCall g to val io is oo os) 
     # (GFrmNormal (LFrm_B (blk, ls, fs, cf) # lstk') gs ck) 
     # gstk') (Suc n) = (
    let naws = ext_mem_sz (ext_mem_sz (naws_of gs) io is) oo os in 
    ((GFrmNormal 
        (LFrm_B (blk_fill_bool blk False, ls, fs, cf) # lstk') 
        (gs \<lparr> naws_of := naws \<rparr>) ck) 
     # gstk'))
  " |
  "step tre 
    (GFrmExc (CKDelCall g to io is oo os)
      # (GFrmNormal (LFrm_B (blk, ls, fs, cf) # lstk') gs ck)
        # gstk')  (Suc n) = (
    let naws = ext_mem_sz (ext_mem_sz (naws_of gs) io is) oo os in 
    ((GFrmNormal 
        (LFrm_B (blk_fill_bool blk False, ls, fs, cf) # lstk') 
        (gs \<lparr> naws_of := naws \<rparr>) ck) 
     # gstk'))
 " |
  "step tre 
    (GFrmExc (CKCallCode g to val io is oo os) 
     #(GFrmNormal (LFrm_B (blk, ls, fs, cf) # lstk') gs ck) 
     # gstk') (Suc n)  = (
    let naws = ext_mem_sz (ext_mem_sz (naws_of gs) io is) oo os in 
    ((GFrmNormal 
        (LFrm_B (blk_fill_bool blk False, ls, fs, cf) # lstk') 
        (gs \<lparr> naws_of := naws \<rparr>) ck) 
     # gstk'))
  " |
  "step tre [GFrmExc ck] (Suc n) = [GFrmExc ck]" |

  "step tre [GFrmNormal (LFrm_E (EImLit lit, ls, fs) # lstk') gs ck] (Suc n) = (
    [GFrmNormal (LFrm_E (EImLit lit, ls, fs) # lstk') gs ck]
  )" |
  "step tre [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck] (Suc n) = (
    [GFrmNormal (LFrm_E (STOP, ls, fs) # lstk') gs ck]
  )" |
  "step tre [GFrmNormal (LFrm_E (EList el, ls, fs) # lstk') gs ck] (Suc n) = 
    [GFrmNormal (LFrm_E (EList el, ls, fs) # lstk') gs ck]" |
  "step tre [GFrmCounterErr] (Suc n) = [GFrmCounterErr]" |

  "step tre _ _ = []"

  by pat_completeness auto
termination 
  by lexicographic_order

(* [] is used to represent error configurations that cannot occur in the execution of well-typed
   expressions and blocks *)

fun multi_step :: "trans_env \<Rightarrow> gstack \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gstack" where 
  "multi_step tre gs 0 k = gs" | 
  "multi_step tre gs (Suc n) k = multi_step tre (step tre gs k) n k" 

end