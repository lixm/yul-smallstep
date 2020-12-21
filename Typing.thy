(******
Type system for Yul language
Copyright (C) 2020  Ximeng Li, Ning Han

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Library General Public
License as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Library General Public License for more details.
******)

theory "Typing"

imports Main LMap Syntax  

begin

fun in_range :: "int \<Rightarrow> type_name \<Rightarrow> bool" where
  "in_range i S256 = (-(2^255) \<le> i \<and> i < 2^255)" | 
  "in_range i U256 = (0 \<le> i \<and> i < 2^256)" | 
  "in_range i S128 = (-(2^127) \<le> i \<and> i < 2^127)" | 
  "in_range i U128 = (0 \<le> i \<and> i < 2^128)" | 
  "in_range i S64 = (-(2^63) \<le> i \<and> i < 2^63)" | 
  "in_range i U64 = (0 \<le> i \<and> i < 2^64)" | 
  "in_range i S32 = (-(2^31) \<le> i \<and> i < 2^31)" | 
  "in_range i U32 = (0 \<le> i \<and> i < 2^32)" | 
  "in_range i S8 = (-(2^7) \<le> i \<and> i < 2^7)" | 
  "in_range i U8 = (0 \<le> i \<and> i < 2^8)" | 
  "in_range i Address160 = (0 \<le> i \<and> i < 2^160)" | 
  "in_range i _ = False"

(* the types for variables *)
datatype vtype = VType type_name 

(* the types for expressions *)
datatype etype = DataType "type_name list" | StmtType 

(* the types for functions *) 
datatype ftype = FType "type_name list" "type_name list" 

(* typing environments for variables *)
type_synonym type_env = "vtype list_map" 

(* typing environments for functions *)
type_synonym ftype_env = "ftype list_map"

(* result of typing an expression *)
datatype expr_type_res = ETypable etype type_env | EUntypable
  

value "{1::nat, 2, 3} \<inter> {4, 5} = {}"
value "{1::int, 2} \<inter> {2, 3}"

value "sum_list [1::nat,2,3]"

fun size_of_expr :: "expr \<Rightarrow> nat" and 
    size_of_es :: "expr list \<Rightarrow> nat" and 
    size_of_blk :: "block \<Rightarrow> nat" 
    where 
  "size_of_expr (EFunCall f es) = 1 + size_of_es es" | 
  "size_of_expr (EId x) = 1" | 
  "size_of_expr (EImLit lit) = 1" | 
  "size_of_expr (ELit lit) = 1" | 
  "size_of_expr (EFunDef f pts rts blk) = 1 + size_of_blk blk" |
  "size_of_expr (EVarDecl txs e) = 2 + (length txs) + size_of_expr e" |
  "size_of_expr (EEmptyVarDecl txs) = 1" | 
  "size_of_expr (EAssg xs e) = 2 + (length xs) + size_of_expr e" | 
  "size_of_expr (EIf e blk) = 1 + size_of_expr e + size_of_blk blk" |
  "size_of_expr (ECond e blk) = 1 + size_of_expr e + size_of_blk blk" |
  "size_of_expr (ESwitch e cases blk_opt) = 
    2 + size_of_expr e + sum_list (map (size_of_blk \<circ> snd) cases) + 
    (case blk_opt of (Some blk0) \<Rightarrow> size_of_blk blk0 | _ \<Rightarrow> 0)
    " | 
  "size_of_expr (EFor blk1 e blk2 blk) =
    1 + size_of_blk blk1 + size_of_expr e + size_of_blk blk2 + size_of_blk blk
    " | 
  "size_of_expr (ERetId xt) = 1" |
  "size_of_expr (EImFunCall f es) = 1 + size_of_es es" | 
  "size_of_expr (EList es) = size_of_es es" | 
  "size_of_expr EStop = 1" | 
  "size_of_expr EGasJump = 1" | 
  "size_of_expr EGasJumpDest = 1" | 
  "size_of_expr EGasPush = 1" | 
  "size_of_expr EGasPop = 1" | 
  "size_of_expr EGasSwap = 1" | 

  "size_of_blk (Blk es) = 1 + size_of_es es" | 

  "size_of_es es = 1 + sum_list (map size_of_expr es)"


definition builtin_fte :: ftype_env where 
  "
  builtin_fte = 
    [(b_land_id, FType [Bool, Bool] [Bool]),  
    (b_lor_id, FType [Bool, Bool] [Bool]), 
    (b_lxor_id, FType [Bool, Bool] [Bool]), 
    (b_lnot_id, FType [Bool] [Bool]),
    (b_add_id, FType [U256, U256] [U256]),
    (b_sub_id, FType [U256, U256] [U256]),
    (b_mul_id, FType [U256, U256] [U256]),
    (b_div_id, FType [U256, U256] [U256]),
    (b_sdiv_id, FType [S256, S256] [S256]),
    (b_mod_id, FType [U256, U256] [U256]),
    (b_smod_id, FType [S256, S256] [S256]),
    (b_exp_id, FType [U256, U256] [U256]),
    (b_addmod_id, FType [U256, U256, U256] [U256]),
    (b_mulmod_id, FType [U256, U256, U256] [U256]),
    (b_lt_id, FType [U256, U256] [Bool]), 
    (b_slt_id, FType [S256, S256] [Bool]), 
    (b_gt_id, FType [U256, U256] [Bool]), 
    (b_sgt_id, FType [S256, S256] [Bool]),
    (b_eq_id, FType [U256, U256] [Bool]),
    (b_iszero_id, FType [U256] [Bool]),
    (b_not_id, FType [U256] [U256]),
    (b_and_id, FType [U256, U256] [U256]),
    (b_or_id, FType [U256, U256] [U256]),
    (b_xor_id, FType [U256, U256] [U256]),
    (b_shl_id, FType [U256, U256] [U256]),
    (b_shr_id, FType [U256, U256] [U256]),
    (b_sar_id, FType [U256, S256] [U256]),

    (b_mstore_id, FType [U256, U256] []),
    (b_mstore8_id, FType [U256, U256] []),
    (b_mload_id, FType [U256] [U256]),
    (b_sstore_id, FType [U256, U256] []),
    (b_sload_id, FType [U256] [U256]),
    (b_msize_id, FType [] [U256]),

    (b_call_id, FType [U256, U256, U256, U256, U256, U256, U256] [U256]),
    (b_callcode_id, FType [U256, U256, U256, U256, U256, U256, U256] [U256]),
    (b_delegatecall_id, FType [U256, U256, U256, U256, U256, U256] [U256]),
    (b_return_id, FType [U256, U256] []),
    (b_revert_id, FType [U256, U256] []),
    (b_selfdestruct_id, FType [U256] []),
    (b_log0_id, FType [U256, U256] []),
    (b_log1_id, FType [U256, U256, U256] []),
    (b_log2_id, FType [U256, U256, U256, U256] []),
    (b_log3_id, FType [U256, U256, U256, U256, U256] []),
    (b_log4_id, FType [U256, U256, U256, U256, U256, U256] []),
    (b_stop_id, FType [] []), 
    (b_invalid_id, FType [] []), 

    (b_coinbase_id, FType [] [U256]),
    (b_difficulty_id, FType [] [U256]),
    (b_gaslimit_id, FType [] [U256]),
    (b_number_id, FType [] [U256]),
    (b_timestamp_id, FType [] [U256]),
    (b_origin_id, FType [] [U256]),
    (b_gasprice_id, FType [] [U256]),
    (b_gas_id, FType [] [U256]),
    (b_balance_id, FType [U256] [U256]),
    (b_address_id, FType [] [U256]), 
    (b_caller_id, FType [] [U256]),
    (b_callvalue_id, FType [] [U256]),
    (b_calldatasize_id, FType [] [U256]),
    (b_calldatacopy_id, FType [] [U256]),
    (b_calldataload_id, FType [U256] [U256]),

    (b_keccak256_id, FType [U256, U256] [U256])
    ]
  "

(* helper lemma supporting the termination proof for the typing function *)
lemma in_lst_impl_sz_lt [simp]: 
  "\<lbrakk> a \<in> set es \<rbrakk> \<Longrightarrow> size_of_expr a < Suc (sum_list (map size_of_expr es))"
proof(induction es arbitrary: a)
  case Nil
  then show ?case by auto
next
  case (Cons a es)
  fix a es aa
  assume H_IH: "\<And>a. a \<in> set es \<Longrightarrow>
                     size_of_expr a < Suc (sum_list (map size_of_expr es))"
  assume H_in: "aa \<in> set (a # es)"  
  hence H_or: "aa = a \<or> aa \<in> set es" by auto
  thus "size_of_expr aa < Suc (sum_list (map size_of_expr (a # es)))"
  proof
    assume "aa = a" thus ?thesis by simp
  next 
    assume "aa \<in> set es" thus ?thesis using H_IH by fastforce
  qed
qed

(* helper lemma supporting the termination proof for the typing function *)
lemma in_cases_impl_sz_lt: 
  "\<lbrakk> ((lit :L tn), b) \<in> set cases \<rbrakk> 
   \<Longrightarrow> size_of_blk b < Suc (sum_list (map (size_of_blk \<circ> snd) cases))"
proof(induction cases arbitrary: lit tn b)
  case Nil
  then show ?case by auto
next
  case (Cons a cases)
  fix a cases lit tn b
  assume H_IH: 
    "\<And>lit tn b.
           (lit :L tn, b) \<in> set cases \<Longrightarrow>
           size_of_blk b < Suc (sum_list (map (size_of_blk \<circ> snd) cases))"
  assume H_case_in_cases: "(lit :L tn, b) \<in> set (a # cases)"
  hence H_or: "((lit :L tn), b) = a \<or> (lit :L tn, b) \<in> set cases" by auto
  thus "size_of_blk b < Suc (sum_list (map (size_of_blk \<circ> snd) (a # cases)))"
  proof
    assume "((lit :L tn), b) = a" 
    thus ?thesis by auto
  next
    assume "(lit :L tn, b) \<in> set cases" 
    thus ?thesis using H_IH by fastforce
  qed
qed

(* obtain information about the types for the user-defined functions for the code *)
fun get_a_func_types :: "expr list \<Rightarrow> ftype_env option" where 
  "get_a_func_types [] = Some []" |
  "get_a_func_types ((EFunDef f ptl rtl e) # es') = (
      case (get_a_func_types es') of 
        (Some te) \<Rightarrow> 
          (case (lm_get te f) of 
            (Some tp) \<Rightarrow> None 
           | _ \<Rightarrow> (Some (te @ [(f, FType (map snd ptl) (map snd rtl))])))
      | _ \<Rightarrow> None
    )" | 
  "get_a_func_types (_ # es') = get_a_func_types es'"

definition get_a_func_types_blk :: "block \<Rightarrow> ftype_env option" where 
  "get_a_func_types_blk blk = (
    case blk of (Blk es) \<Rightarrow> get_a_func_types es
   )"

fun ret_or_lit :: "expr \<Rightarrow> bool" where
  "ret_or_lit (ERetId (x, t)) = True" | 
  "ret_or_lit (EImLit l) = True" | 
  "ret_or_lit _ = False" 

fun not_elist :: "expr \<Rightarrow> bool" where 
  "not_elist (EList _) = False" | 
  "not_elist _ = True" 

(*
  - The typing of blocks and expressions takes as parameters
    the type environment for the variables that can be used in the current scope, 
    the set of variables that additionally exist in outer scopes statically, and 
    the type environment for the functions in scope. 
  - The variables additionally existing in outer scopes statically 
    are those declared in outer scopes of the immediately surrounding function definition. 
    These variables cannot be used in the function defined, nor can they be re-declared. 
*)
function (sequential) 
    type_es :: "type_env \<Rightarrow> id0 set \<Rightarrow> ftype_env \<Rightarrow> expr list \<Rightarrow> (bool\<times>type_env)" and 
    type_b :: "type_env \<Rightarrow> id0 set \<Rightarrow> ftype_env \<Rightarrow> block \<Rightarrow> bool" and
    type_e :: "type_env \<Rightarrow> id0 set \<Rightarrow> ftype_env \<Rightarrow> expr \<Rightarrow> expr_type_res"
where 
  "type_es vte xs fte es = 
    foldl (\<lambda>acc e. 
            (if (fst acc) then 
              (case type_e (snd acc) xs fte e of 
                (ETypable StmtType vte') \<Rightarrow> (True, vte') | _ \<Rightarrow> (False, (snd acc))) 
             else 
              acc)) 
          (True, vte) es" |

  "type_b vte xs fte (Blk es) = (case (type_es vte xs fte es) of (b, vte') \<Rightarrow> b)" |
  
  "type_e vte xs fte (EId x) = 
    (case (lm_get vte x) of Some (VType tn) \<Rightarrow> ETypable (DataType [tn]) vte | _ \<Rightarrow> EUntypable)" |

  "type_e vte xs fte (EImLit lit) = (
     case lit of 
      (TL :L tn) \<Rightarrow> (if tn = Bool then ETypable (DataType [Bool]) vte else EUntypable)
    | (FL :L tn) \<Rightarrow> (if tn = Bool then ETypable (DataType [Bool]) vte else EUntypable)
    | ((NL i) :L tn) \<Rightarrow> (if (in_range i tn) then (ETypable (DataType [tn]) vte) else EUntypable)
    | ((SL ws) :L _) \<Rightarrow> EUntypable
  )
     " |
  "type_e vte xs fte (ELit lit) = (
     case lit of 
      (TL :L tn) \<Rightarrow> (if tn = Bool then ETypable (DataType [Bool]) vte else EUntypable)
    | (FL :L tn) \<Rightarrow> (if tn = Bool then ETypable (DataType [Bool]) vte else EUntypable)
    | ((NL i) :L tn) \<Rightarrow> (if (in_range i tn) then (ETypable (DataType [tn]) vte) else EUntypable)
    | ((SL ws) :L _) \<Rightarrow> EUntypable
  )" |
  
  "type_e vte xs fte (EFunCall f es) = (
    case (lm_get (fte @ builtin_fte) f) of
      Some (FType ptl rtl) \<Rightarrow> (
        if length ptl = length es then
          (let es_no_elist = (foldl (\<lambda>acc e. (acc \<and> (not_elist e))) True es) in 
           let es_pts = zip es ptl in 
           \<comment> \<open> type-check the arguments \<close>
           let es_res =   
            (foldl (\<lambda>acc (e, t). 
              (if acc then type_e vte xs fte e = ETypable (DataType [t]) vte else False))
              True es_pts) in
           (if es_no_elist \<and> es_res then 
             (if length rtl = 0 then 
                ETypable StmtType vte
              else ETypable (DataType rtl) vte)
            else 
              EUntypable
           )) 
        else 
          EUntypable
      )
    | _ \<Rightarrow> EUntypable
    )" |
  \<comment> \<open> that f is not in the domain of fte cannot be checked here. this is because the type of
       f might be previously added to fte due to the existence of the function def in a block \<close>
  "type_e vte xs fte (EFunDef f pl rl blk) = (
    if (f \<notin> lm_dom builtin_fte \<and> distinct (pl @ rl)) then
      (
      let vte1' = (zip (map fst pl) (map (\<lambda>(x,tn). (VType tn)) pl)) ;
          vte2' = (zip (map fst rl) (map (\<lambda>(x,tn). (VType tn)) rl)) in 
      (\<comment> \<open>ids already in the scope cannot be used as formal parameters or return variables\<close>
        case (get_a_func_types_blk blk) of 
          Some fte' \<Rightarrow> (
            if (lm_dom vte \<union> xs) \<inter> (lm_dom vte1' \<union> lm_dom vte2') = {}
                \<and> (lm_dom builtin_fte \<union> lm_dom fte \<union> {f}) \<inter> lm_dom fte' = {} 
                \<and> (type_b (vte1' @ vte2') (xs \<union> lm_dom vte) 
                          (fte @ fte' @ [(f, FType (map snd pl) (map snd rl))]) blk) 
            then 
              ETypable StmtType vte
            else 
              EUntypable
          ) 
        | _ \<Rightarrow> EUntypable
      ))
    else 
      EUntypable)
  " |
  "type_e vte xs fte (EVarDecl txs e) = (
    if (foldl (\<lambda>acc tx. acc \<and> (lm_get vte (fst tx)) = None \<and> ((fst tx) \<notin> xs) 
                            \<and> lm_get fte (fst tx) = None) 
              True txs) 
        \<and> distinct (map fst txs) 
    then (
      case (type_e vte xs fte e) of 
        (ETypable (DataType tns) vte') \<Rightarrow> 
         (if length txs = length tns then (
            let txs_tns = zip txs tns in (
            if (foldl (\<lambda>acc ((x, tn1), tn2). acc \<and> tn1 = tn2) True txs_tns) then (
              let vte'' = vte @ ((zip (map fst txs) (map ((\<lambda>tn. (VType tn)) \<circ> snd) txs)))
              in (ETypable StmtType vte'')
            ) else EUntypable
            )
          ) else 
            EUntypable)
      | _ \<Rightarrow> EUntypable
    ) 
    else 
      EUntypable
   )
  " | 
  "type_e vte xs fte (EEmptyVarDecl txs) = (
    if (foldl (\<lambda>acc tx. acc \<and> (lm_get vte (fst tx)) = None \<and> ((fst tx) \<notin> xs) 
                            \<and> lm_get fte (fst tx) = None) 
              True txs) 
        \<and> distinct (map fst txs) 
    then (
      let vte' = vte @ (zip (map fst txs) (map (\<lambda>(x, tn). (VType tn)) txs)) in 
        ETypable StmtType vte'
    )
    else 
      EUntypable
  )
  " | 
  "type_e vte xs0 fte (EAssg xs e) = (
    case (type_e vte xs0 fte e) of
      (ETypable (DataType tns) vte') \<Rightarrow> (
        if length xs = length tns then
          let xs_tns = zip xs tns in (
            if (foldl (\<lambda>acc (x, tn). acc \<and> (lm_get vte x = Some (VType tn))) True xs_tns)
                \<and> distinct xs
            then
              ETypable StmtType vte
            else 
              EUntypable
          )
        else 
          EUntypable
        )
    | _ \<Rightarrow> EUntypable
  )
  " | 
  "type_e vte xs fte (EIf e blk) = (
    case (type_e vte xs fte e) of 
      (ETypable (DataType [Bool]) vte') \<Rightarrow> (
        if not_elist e then (
          case (get_a_func_types_blk blk) of 
            Some fte' \<Rightarrow> 
              (if (lm_dom builtin_fte \<union> lm_dom fte) \<inter> lm_dom fte' = {} 
                   \<and> type_b vte xs (fte @ fte') blk 
               then (ETypable StmtType vte) 
               else EUntypable)
          | _ \<Rightarrow> EUntypable
        ) else
          EUntypable
      ) 
    | _ \<Rightarrow> EUntypable
    )
  " |

  "type_e vte xs fte (ECond e blk) = (
    case (type_e vte xs fte e) of 
      (ETypable (DataType [Bool]) vte') \<Rightarrow> (
        if not_elist e then (
          case (get_a_func_types_blk blk) of 
            Some fte' \<Rightarrow> 
              (if (lm_dom builtin_fte \<union> lm_dom fte) \<inter> lm_dom fte' = {}
                  \<and> type_b vte xs (fte @ fte') blk then 
                (ETypable StmtType vte) 
               else 
                EUntypable)
          | _ \<Rightarrow> EUntypable
        ) else 
          EUntypable
      )
    | _ \<Rightarrow> EUntypable
    )
  " |

  "type_e vte xs fte (ESwitch e cases blk_opt) = (
    case (type_e vte xs fte e) of 
      (ETypable (DataType [tn]) _) \<Rightarrow> (
        if not_elist e then (
          if (foldl 
              (\<lambda>acc (lit, blk). 
                (case (lit) of 
                  (Literal lkind tn') \<Rightarrow> 
                    acc \<and> tn = tn' \<and> (
                      case (get_a_func_types_blk blk) of 
                        Some fte' \<Rightarrow> 
                          (lm_dom builtin_fte \<union> lm_dom fte) \<inter> lm_dom fte' = {} 
                           \<and> type_b vte xs (fte @ fte') blk
                      | _ \<Rightarrow> False
                    ))) True cases) 
          then 
            (
              case blk_opt of 
                Some blk \<Rightarrow> (
                  case (get_a_func_types_blk blk) of 
                    Some fte' \<Rightarrow> (
                      if (lm_dom builtin_fte \<union> lm_dom fte) \<inter> lm_dom fte' = {} 
                          \<and> type_b vte xs (fte @ fte') blk then 
                        ETypable StmtType vte
                      else 
                        EUntypable)
                  | _ \<Rightarrow> EUntypable
                )
              | None \<Rightarrow> (ETypable StmtType vte)
            )
          else 
            EUntypable
        ) else 
          EUntypable
      )
   |  _ \<Rightarrow> EUntypable
   )
  " |
  "type_e vte xs fte (EFor blk1 e blk2 blk) = (
    case blk1 of 
      (Blk es1) \<Rightarrow> (
        case get_a_func_types es1 of \<comment> \<open>forbit function definition inside the init block\<close>
          Some [] \<Rightarrow> (
          \<comment> \<open> variables in the outer scope can all be used in blk1 \<close>
          case (type_es vte xs fte es1) of
            (True, vte') \<Rightarrow> (
            case (type_e vte' xs fte e) of
               ETypable (DataType [Bool]) vte'' \<Rightarrow> (
                if not_elist e then (
                \<comment> \<open>variables declared in one of blk and blk2 cannot be used in the other, 
                    but can be declared in the other\<close>
                case (get_a_func_types_blk blk2, get_a_func_types_blk blk) of 
                  (Some fte2', Some fte') \<Rightarrow> (
                    if (lm_dom builtin_fte \<union> lm_dom fte) \<inter> lm_dom fte2' = {} 
                        \<and> type_b vte' xs (fte @ fte2') blk2 
                        \<and> (lm_dom builtin_fte \<union> lm_dom fte) \<inter> lm_dom fte' = {}
                        \<and> type_b vte' xs (fte @ fte') blk then
                      ETypable StmtType vte
                    else 
                      EUntypable)
                | _ \<Rightarrow> EUntypable
                ) else 
                  EUntypable
               )
            | _ \<Rightarrow> EUntypable
            )
          | _ \<Rightarrow> EUntypable 
          )
        | _ \<Rightarrow> EUntypable
      )
   )
  " | 
  "type_e vte xs fte (ERetId xt) = ETypable (DataType [snd xt]) vte" |
  "type_e vte xs fte (EImFunCall f es) = (
    case (lm_get (fte @ builtin_fte) f) of 
      Some (FType ptl rtl) \<Rightarrow> (
        if length ptl = length es then
          (let es_no_elist = (foldl (\<lambda>acc e. (acc \<and> (not_elist e))) True es) in 
           let es_pts = zip es ptl in 
           \<comment> \<open> type-check the arguments \<close>
           let es_res =   
            (foldl (\<lambda>acc (e, t). 
              (if acc then type_e vte xs fte e = ETypable (DataType [t]) vte else False))
              True es_pts) in
           (if es_no_elist \<and> es_res then 
             (if length rtl = 0 then 
                ETypable StmtType vte
              else ETypable (DataType rtl) vte)
            else 
              EUntypable
           )) 
        else 
          EUntypable
      )
    | _ \<Rightarrow> EUntypable
    )" |
  "type_e vte xs fte (EList es) = (
      let es_ret_lit = (foldl (\<lambda>acc e. acc \<and> ret_or_lit e) True es) in (
      if es_ret_lit then (
        foldl (\<lambda>acc e. (
                case acc of (ETypable (DataType tns) _) \<Rightarrow> (
                  case type_e vte xs fte e of 
                    (ETypable (DataType [tn]) _) \<Rightarrow> ETypable (DataType (tns @ [tn])) vte 
                  | _ \<Rightarrow> EUntypable) 
                | _ \<Rightarrow> EUntypable))
        (ETypable (DataType []) vte) es
      ) else 
        EUntypable
      )
  )" |
  "type_e vte xs fte STOP = ETypable StmtType vte" |
  "type_e vte xs fte EGasJump = ETypable StmtType vte" |
  "type_e vte xs fte EGasPush = ETypable StmtType vte" |
  "type_e vte xs fte EGasJumpDest = ETypable StmtType vte" |
  "type_e vte xs fte EGasPop = ETypable StmtType vte" |
  "type_e vte xs fte EGasSwap = ETypable StmtType vte"

  by pat_completeness auto

termination proof-
  show ?thesis
  apply(relation  
  "measure 
    (\<lambda>x. (case x of 
           (Inl (_::type_env, xs:: id0 set, fte::ftype_env, es::expr list)) \<Rightarrow> size_of_es es
         | (Inr (Inl (vte::type_env, xs:: id0 set, fte::ftype_env, blk::block))) \<Rightarrow> size_of_blk blk
         | (Inr (Inr (vte::type_env, xs:: id0 set, fte::ftype_env, e::expr))) \<Rightarrow> size_of_expr e
         ))
  ")
  apply auto 
      apply (simp add: less_SucI set_zip_leftD)
        using in_cases_impl_sz_lt apply fastforce
        by (simp add: less_SucI set_zip_leftD) 
qed

end
