(******
Formalization of ERC20 token contract
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

theory "MyToken"

imports 
  HOL.Option 
  Main "../Syntax" "../Typing" "../SmallStep" "../utils/Keccak"
  (*"$ISABELLE_HOME/src/HOL/Word/Word"*)

begin
fun func_map_blk :: "block \<Rightarrow> ((id0,fvalue) Map.map)" and
    func_map_exp :: "expr \<Rightarrow> ((id0,fvalue) Map.map)"  where
  "func_map_blk (Blk []) = Map.empty" |  
  "func_map_blk (Blk (e#es)) =  
      (func_map_exp e ++ func_map_blk (Blk es))" |
  "func_map_exp (FUN f params rets IS (Blk blk)) = 
      (Map.empty)( f \<mapsto> (FunctionV f params rets (Blk blk)) )" | 
  "func_map_exp _ = (Map.empty)" 

(* IDs for user-defined functions *)
definition f_selector_id :: int where "f_selector_id = 1100" 
definition f_return_uint_id :: int where "f_return_uint_id = 1101" 
definition f_balance_offset_id :: int where "f_balance_offset_id = 1102"  
definition f_decode_as_uint_id :: int where "f_decode_as_uint_id = 1103" 
definition f_decode_as_address_id :: int where "f_decode_as_address_id = 1104" 
definition f_safe_add_id :: int where "f_safe_add_id = 1105"  
definition f_owner_id :: int where "f_owner_id = 1106" 
definition f_total_supply_id :: int where "f_total_supply_id = 1107" 
definition f_balance_of_id :: int where "f_balance_of_id = 1108" 
definition f_add_to_balance_id :: int where "f_add_to_balance_id = 1109" 
definition f_deduct_from_balance_id :: int where "f_deduct_from_balance_id = 1110" 
definition f_called_by_owner_id :: int where "f_called_by_owner_id = 1111"
definition f_transfer_id :: int where "f_transfer_id = 1112" 
definition f_allowed_offset_id :: int where "f_allowed_offset_id = 1113" 
definition f_mapping_ele_offset_id :: int where "f_mapping_ele_offset_id = 1114" 
definition f_allowance_id :: int where "f_allowance_id = 1115" 
definition f_transfer_from_id :: int where "f_transfer_from_id = 1116" 
definition f_approve_id :: int where "f_approve_id = 1117" 
definition f_increase_approval_id :: int where "f_increase_approval_id = 1118" 
definition f_log_id :: int where "f_log_id = 1119"

(* IDs for variables *) 
definition s_id :: int where "s_id = 0" 
definition v_id :: int where "v_id = -1"
definition offset_id :: int where "offset_id = -2" 
definition account_id :: int where "account_id = -3" 
definition a_id :: int where "a_id = -4"
definition b_id :: int where "b_id = -5" 
definition r_id :: int where "r_id = -6" 
definition o_id :: int where "o_id = -7" 
definition supply_id :: int where "supply_id = -8" 
definition bal_id :: int where "bal_id = -9" 
definition amount_id :: int where "amount_id = -10" 
definition cbo_id :: int where "cbo_id = -11" 
definition to_id :: int where "to_id = -12" 
definition sender_id :: int where "sender_id = -13"  
definition from_id :: int where "from_id = -14"
definition by_id :: int where "by_id = -15" 
definition key_id :: int where "key_id = -16"
definition base_id :: int where "base_id = -17" 
definition allowance_id :: int where "allowance_id = -18" 
definition spender_id :: int where "spender_id = -19" 
definition topic_id :: int where "topic_id = -20"
definition p1_id :: int where "p1_id = -21"
definition p2_id :: int where "p2_id = -22" 
definition p3_id :: int where "p3_id = -23" 

definition lit_zero :: expr where "lit_zero = EImLit ((NL 0) :L U256)"
definition lit_one :: expr where "lit_one = EImLit ((NL 1) :L U256)"
definition lit_two :: expr where "lit_two = EImLit ((NL 2) :L U256)" 

definition balance_base where "balance_base = lit_two"
definition allowance_base where "allowance_base = EImLit (Literal (NumberLiteral 3) U256)"

definition revert_zz_call :: expr where 
  "revert_zz_call = (CALL b_revert_id [lit_zero, lit_zero])" 

definition max_uint256 :: expr where 
  "max_uint256 = EImLit (Literal (NumberLiteral (2^256 - 1)) U256)" 

(* retrive the first 4 bytes from the 32 bytes call data, and store the 4 bytes in s_id*)  
definition selector_func :: expr where 
  "selector_func = 
      FUN f_selector_id [] [(s_id, U256)] IS
        BEGIN[(
            [s_id] ::= (CALL b_div_id 
                [CALL b_calldataload_id [lit_zero], 
                  EImLit (Literal 
                    (NumberLiteral 0x100000000000000000000000000000000000000000000000000000000) 
                    U256) ]
            )
        )]END" 

definition return_uint_func :: expr where
  "return_uint_func = 
    FUN f_return_uint_id [(v_id, U256)] [] IS
      BEGIN[           
            (CALL b_mstore_id 
                          [lit_zero, (EId v_id)]),            
            (CALL b_return_id 
                          [lit_zero, EImLit (Literal (NumberLiteral 32) U256)])
      ]END"

definition decode_as_uint_func :: expr where 
  "decode_as_uint_func = 
    FUN f_decode_as_uint_id 
      [(offset_id, U256)] [(v_id, U256)] IS
     BEGIN [(
          [v_id] ::=
          (CALL b_calldataload_id 
            [(CALL b_add_id 
                [EImLit (Literal (NumberLiteral 4) U256), 
                 (CALL b_mul_id 
                    [(EId offset_id), EImLit(Literal (NumberLiteral 32) U256)])])]) 
      )]END"  

  (*if iszero(iszero(and(v,
	                not(0xffff ffff ffff ffff ffff ffff ffff ffff ffff ffff)))) *)
definition decode_as_address_func :: expr where 
  "decode_as_address_func = 
    FUN f_decode_as_address_id 
      [(offset_id, U256)] [(v_id, U256)] IS              
       BEGIN
        [
          ([v_id] ::= (CALL f_decode_as_uint_id [EId offset_id])), 
          IF  
            (CALL b_lnot_id 
              [CALL b_iszero_id 
                [CALL b_and_id 
                  [EId v_id, 
                   CALL b_not_id 
                    [EImLit (Literal 
                      (NumberLiteral 0xffffffffffffffffffffffffffffffffffffffff) 
                      U256)]]]])
           THEN(Blk[revert_zz_call])  
        ]END
      "

definition mapping_ele_offset_func :: expr where 
  "
  mapping_ele_offset_func = 
    FUN f_mapping_ele_offset_id  
    [(base_id, U256), (key_id, U256)] [(offset_id, U256)] IS    
    BEGIN[      
        (CALL b_mstore_id [lit_zero, (EId key_id)]),  
        (CALL b_mstore_id
          [EImLit (Literal (NumberLiteral 32) U256), (EId base_id)]),  
       [offset_id] ::=
        (CALL b_keccak256_id [lit_zero, EImLit(Literal (NumberLiteral 64) U256)]) 
    ]END    
  "

definition balance_offset_func :: expr where 
  "
  balance_offset_func = 
    FUN f_balance_offset_id
      [(account_id, U256)] [(offset_id, U256)] IS
      BEGIN[([offset_id] ::= 
        (CALL f_mapping_ele_offset_id 
          [balance_base, (EId account_id)]))]END 
  "

definition allowed_offset_func :: expr where 
  "allowed_offset_func = 
    FUN f_allowed_offset_id  
      [(from_id, U256), (by_id, U256)]
      [(offset_id, U256)] IS
      BEGIN[(
        [offset_id] ::= 
          (CALL f_mapping_ele_offset_id 
            [CALL f_mapping_ele_offset_id [allowance_base, EId from_id], 
             EId by_id])
      )]END
  "

definition safe_add_func :: expr where 
  "safe_add_func = 
    FUN f_safe_add_id 
      [(a_id, U256), (b_id, U256)] [(r_id, U256)] IS
       BEGIN
        [
          (
            [r_id] ::= 
            (CALL b_add_id [EId a_id, EId b_id])), 
          IF 
            (CALL b_lor_id 
              [(CALL b_lt_id [EId r_id, EId a_id]), 
               (CALL b_lt_id [EId r_id, EId b_id])])
           THEN (Blk [revert_zz_call])
        ]END
       
  " 

definition owner_func :: expr where 
  "owner_func = 
    FUN f_owner_id [] [(o_id, U256)] IS 
    BEGIN[(
      [o_id] ::= (CALL b_sload_id [lit_zero])
    )]END
  "

definition total_supply_func :: expr where
  "total_supply_func = 
    FUN f_total_supply_id [] [(supply_id, U256)] IS
      BEGIN[(
        [supply_id] ::= (CALL b_sload_id [lit_one]) 
      )]END
  " 

definition balance_of_func :: expr where 
  "balance_of_func = 
    FUN f_balance_of_id [(account_id, U256)] [(bal_id, U256)] IS
    BEGIN[(
        [bal_id] ::=
        (CALL b_sload_id 
          [CALL f_balance_offset_id 
            [EId account_id]]) 
    )]END
  "

definition allowance_func :: expr where
  "
  allowance_func = 
    FUN f_allowance_id 
      [(from_id, U256), (by_id, U256)] [(amount_id, U256)] IS
      BEGIN[(
          [amount_id] ::=
          (CALL b_sload_id
            [CALL f_allowed_offset_id
              [EId from_id, EId by_id]]) 
      )]END
  "

definition log_func :: expr where 
  "log_func = 
    FUN f_log_id 
      [(topic_id, U256), (p1_id, U256), (p2_id, U256), (p3_id, U256)] [] IS    
    BEGIN[
      (CALL b_mstore_id [lit_zero, EId topic_id]),       
       (CALL b_mstore_id [EImLit (Literal (NumberLiteral 32) U256), EId p1_id]),  
        (CALL b_mstore_id [EImLit (Literal (NumberLiteral 64) U256), EId p2_id]), 
         (CALL b_mstore_id [EImLit (Literal (NumberLiteral 96) U256), EId p3_id]), 
          (CALL b_log0_id [lit_zero, EImLit (Literal (NumberLiteral 128) U256)])
    ]END
    "

definition approve_func :: expr where 
  "approve_func = 
    FUN f_approve_id
      [(spender_id, U256), (amount_id, U256)] [] IS      
      BEGIN[
        VAR [(sender_id, U256)] ::- (CALL b_caller_id []), 
          (CALL b_sstore_id 
            [CALL f_allowed_offset_id [EId sender_id, EId spender_id], 
             EId amount_id]), 
          (CALL f_log_id 
            [lit_zero, EId sender_id, EId spender_id, EId amount_id]) 
      ]END      
  "

definition add_to_balance_func :: expr where 
  "add_to_balance_func = 
    FUN f_add_to_balance_id 
      [(account_id, U256), (amount_id, U256)] [] IS      
        BEGIN
        [
          VAR [(offset_id, U256)] ::- 
            (CALL f_balance_offset_id [EId account_id])
          , 
          (
            CALL b_sstore_id 
              [EId offset_id, 
               CALL f_safe_add_id 
                [(CALL b_sload_id [EId offset_id]), EId amount_id]
              ] 
          )
        ]END
     "

definition deduct_from_balance_func :: expr where 
  "deduct_from_balance_func = 
    FUN f_deduct_from_balance_id 
      [(account_id, U256), (amount_id, U256)] [] IS      
      BEGIN
      [
        VAR [(offset_id, U256)] ::- 
          (CALL f_balance_offset_id [EId account_id])
        ,
        VAR [(bal_id, U256)] ::-
          (CALL b_sload_id [EId offset_id]) 
        ,
        IF 
          (CALL b_lt_id [EId bal_id, EId amount_id]) 
        THEN(Blk [revert_zz_call])  
        ,
          (CALL b_sstore_id   
            [EId offset_id, 
             CALL b_sub_id 
              [(EId bal_id), (EId amount_id)] ]) 
      ]END      
  "

definition called_by_owner_func :: expr where
  "called_by_owner_func = 
    FUN f_called_by_owner_id 
      [] [(cbo_id, Bool)] IS
     BEGIN[(
       [cbo_id] ::=
        (CALL b_eq_id 
          [CALL f_owner_id [], CALL b_caller_id []])
      )]END
  "

definition transfer_func :: expr where 
  "transfer_func = 
    FUN f_transfer_id 
      [(to_id, U256), (amount_id, U256)] [] IS
      BEGIN 
        [ 
            (CALL f_deduct_from_balance_id 
              [CALL b_caller_id [], (EId amount_id)]), 
            (CALL f_add_to_balance_id 
              [EId to_id, EId amount_id]), 
          \<comment> \<open>emit Transfer(msg.sender, _to, _value);\<close>
            (CALL f_log_id 
              [lit_one, CALL b_caller_id [], EId to_id, EId amount_id]) 
        ]END
  "

definition transfer_from_func :: expr where
  "transfer_from_func = 
    FUN f_transfer_from_id
      [(from_id, U256), (to_id, U256), (amount_id, U256)] [] IS      
      BEGIN
        [ 
          VAR [(sender_id, U256)] ::- (CALL b_caller_id []), 
          VAR [(allowance_id, U256)] ::- 
            (CALL f_allowance_id [EId from_id, EId sender_id]), 
          IF 
            (CALL b_lt_id [max_uint256, EId allowance_id])
          THEN (Blk [revert_zz_call]), 
          IF 
            (CALL b_lt_id [EId allowance_id, EId amount_id]) 
          THEN (Blk [revert_zz_call]), 
            (CALL f_deduct_from_balance_id 
              [(EId from_id), (EId amount_id)]), 
            (CALL f_add_to_balance_id 
              [EId to_id, EId amount_id]), 
              (CALL b_sstore_id 
                [CALL f_allowed_offset_id [EId from_id, EId sender_id], 
                 CALL b_sub_id [EId allowance_id, EId amount_id]
                ]
            ), 
          \<comment> \<open>emit Transfer(_from, _to, _value);\<close>
            (CALL f_log_id 
              [lit_two, EId from_id, EId to_id, EId amount_id]) 
        ]END      
  "

(* It seems that there is no "if" expr in the Yul formalization *)
definition dispatch_logic_my_token :: "expr list" where
  "dispatch_logic_my_token =   
    [
      IF 
        (CALL b_gt_id [CALL b_callvalue_id [], lit_zero])
       THEN(Blk [revert_zz_call]) 
      ,
      SWITCH (CALL f_selector_id [])
       CASES [( ((NL 0x70a08231) :L U256), 
                BEGIN[(CALL f_return_uint_id 
                  [CALL f_balance_of_id 
                    [CALL f_decode_as_address_id [lit_zero]]])]END ), 
        ( ((NL 0x18160ddd) :L U256),             
              BEGIN[(CALL f_return_uint_id
                [CALL f_total_supply_id []])]END ), 
        ( ((NL 0x095ea7b3) :L U256),              
              BEGIN[(CALL f_approve_id
                [CALL f_decode_as_address_id [lit_zero], 
                 CALL f_decode_as_uint_id [lit_one]])]END ), 
        ( ((NL 0xdd62ed3e) :L U256),              
             BEGIN[(CALL f_return_uint_id 
                [(CALL f_allowance_id
                  [CALL f_decode_as_address_id [lit_zero], 
                   CALL f_decode_as_address_id [lit_one]])])]END ),
        ( ((NL 0xa9059cbb) :L U256),              
             BEGIN[(CALL f_transfer_id 
                [CALL f_decode_as_address_id [lit_zero], 
                 CALL f_decode_as_uint_id [lit_one]])]END ), 
        ( ((NL 0x23b872dd) :L U256),              
             BEGIN[(CALL f_transfer_from_id
                [CALL f_decode_as_address_id [lit_zero], 
                 CALL f_decode_as_address_id [lit_one], 
                 CALL f_decode_as_uint_id [lit_two]])]END )] 
       DEFAULT (Some (Blk [revert_zz_call]))
    ]
  "



(*****************************************************************************
                            check typing in the Token contract                              
 *****************************************************************************)
value "get_a_func_types ([
        selector_func, 
        return_uint_func, 
        decode_as_uint_func, 
        decode_as_address_func, 
        mapping_ele_offset_func, 
        balance_offset_func, 
        safe_add_func, 
        owner_func, 
        total_supply_func, 
        balance_of_func,
        approve_func, 
        add_to_balance_func, 
        deduct_from_balance_func, 
        called_by_owner_func,
        allowed_offset_func, 
        allowance_func,  
        transfer_func, 
        transfer_from_func, 
        log_func        
    ]@dispatch_logic_my_token)"

definition mytoken_code :: block where 
  "mytoken_code = 
    Blk([
        selector_func, 
        return_uint_func, 
        decode_as_uint_func, 
        decode_as_address_func, 
        mapping_ele_offset_func, 
        balance_offset_func, 
        safe_add_func, 
        owner_func, 
        total_supply_func, 
        balance_of_func,
        approve_func, 
        add_to_balance_func, 
        deduct_from_balance_func, 
        called_by_owner_func,
        allowed_offset_func, 
        allowance_func,  
        transfer_func, 
        transfer_from_func, 
        log_func        
    ] @ dispatch_logic_my_token) "

definition fte_blk_mytoken where
  "fte_blk_mytoken = (case get_a_func_types_blk mytoken_code of Some fte \<Rightarrow> fte)"

value "type_b [] {} fte_blk_mytoken mytoken_code"
value "type_b [] {} fte_blk_mytoken (Blk(dispatch_logic_my_token @
       [selector_func, 
        return_uint_func, 
        decode_as_uint_func, 
        decode_as_address_func, 
        mapping_ele_offset_func, 
        balance_offset_func, 
        safe_add_func, 
        owner_func, 
        total_supply_func, 
        balance_of_func,
        approve_func, 
        add_to_balance_func, 
        deduct_from_balance_func, 
        called_by_owner_func,
        allowed_offset_func, 
        allowance_func,  
        transfer_func, 
        transfer_from_func, 
        log_func        
      ]))"

(*****************************************************************************
                               utility functions                             
 *****************************************************************************)
(* get the storage address for the allowance of transfer from the account at from_addr 
   by the account at by_addr *)
definition get_allowance_offset :: "address \<Rightarrow> address \<Rightarrow> 256 word" where 
  "get_allowance_offset from_addr by_addr = 
    keccak 
     ((int_to_byte_lst (uint by_addr) 32) @
        (int_to_byte_lst
          (uint (keccak ((int_to_byte_lst (uint from_addr) 32) @ (int_to_byte_lst 0x3 32))))
          32))" 

definition get_balance_offset :: "address \<Rightarrow> 256 word" where
  "get_balance_offset account_addr =
    (keccak ((int_to_byte_lst (uint account_addr) 32) @ (int_to_byte_lst 0x2 32))) "

value "get_balance_offset 0x1234"

(* retrieval of the value at a specified storage address, from a gstate *)
definition get_val_from_gs :: "gstate \<Rightarrow> 256 word \<Rightarrow> (256 word) option" where 
  "get_val_from_gs gs st_addr = (
    case (accs_of gs) (addr_of gs) of 
     Some acc \<Rightarrow> Some ((store_of acc) st_addr)
    | _ \<Rightarrow> None
  )"

(* retrieval of the value at a specified storage address, from the top frame of a gstack *)
fun get_val_from_storage :: "gstack \<Rightarrow> 256 word \<Rightarrow> (256 word) option" where 
  "get_val_from_storage ((GFrmNormal _ gs _) # gstk') st_addr = get_val_from_gs gs st_addr" | 
  "get_val_from_storage ((GFrmHalt gs _ _) # gstk') st_addr = get_val_from_gs gs st_addr" |
  "get_val_from_storage _ st_addr = None" 

definition storeV :: "(256 word) \<Rightarrow> (256 word)" where
  "storeV a = (
    if a = 56430757919374560884025706976084491821627146992534107071153636802618420959980 
    then (99 :: 256 word)
    else 0
  )"

definition check_gs_gas_stp :: "gstack \<Rightarrow> 256 word \<Rightarrow> bool" where 
  "check_gs_gas_stp gstk left_gas = (
    case gstk of 
      [GFrmNormal [LFrm_E (STOP, _, _)] gs _] \<Rightarrow> 
        (if left_gas = (gas_of gs) then (True) else (False))
    | (GFrmHalt gs _ _) # gstk \<Rightarrow>
        (if left_gas = (gas_of gs) then (True) else (False))
    | [GFrmNormal [LFrm_B (_, _, _, _)] gs _] \<Rightarrow>
        (if left_gas = (gas_of gs) then (True) else (False))
    | _ \<Rightarrow> False
    )"

(*(\<lambda>x . (case x of _ => (0x0 :: (256 word))))*)
definition to_account  :: "account"  where 
  "to_account = \<lparr>
    code_of = None,
    store_of = (\<lambda>x . (case x of _ => (0xff :: (256 word)))),
    bal_of = (0x0 :: 256 word),
    nonce_of = (0x0 :: 256 word)
  \<rparr>"

definition account1  :: "account"  where 
  "account1 = \<lparr>
    code_of = None,
    store_of = (\<lambda>x. (if x = (43633114540367443769613365612029762689758420575593515939555225863214374745012::256 word) then 88 
                     else (if (x = (88929718368862085017632553938105747069421452613002850438713401306652574497725::256 word))
                           then 99
                            else (
                              if (x = (85260039250880668175711268157064721600773280203878117927422354864779945824589::256 word))
                              then 33 else 30)))),
    bal_of = (0xfff4 :: 256 word),
    nonce_of = (0x0 :: 256 word)
  \<rparr>"

definition gs1_bfun :: gstate where
  "gs1_bfun = 
  \<lparr>
    addr_of =  0x0DCd2F752394c41875e259e00bb44fd505297caF,
    saddr_of = 0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c, 
    money_of = (0x2f :: 256 word),
    input_of = [(0x26 :: 8 word), (0x12 :: 8 word), (0x1f :: 8 word), (0xf0 :: 8 word)],
    mem_of = (\<lambda>x. 0x01), 
    naws_of = 3, 
    gas_of = 3000000, 
    ct_of = 10,
    accs_of = (\<lambda>x. (if x = (0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c::address) then 
                      (Some to_account)
                    else
                      (Some account1))),  
    refund_of = (0x0 :: 256 word), 
    logs_of = [], 
    ss_of = {}
  \<rparr>"

value "size(fill_zero (input_of gs1_bfun) (32 - int(size(input_of gs1_bfun))))"
value "eval_rbuiltin gs1_bfun CalldataLoad [NL 3]"

definition gs_bfun :: gstate where
  "gs_bfun = 
  \<lparr>
    addr_of =  0x0DCd2F752394c41875e259e00bb44fd505297caF,
    saddr_of = 0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c, 
    money_of = (0x0 :: 256 word), 
    input_of = [(0x0 :: 8 word), (0x20 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), 
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x01 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), 
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), 
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),(0x0 :: 8 word)], 
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

definition tre0_ex1 :: trans_env where 
  "
    tre0_ex1 = 
    \<lparr>
      oaddr_of = 0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c, 
      gprice_of = (0xa2 :: 256 word), 
      bheader_of = blk_hdr_ex1
    \<rparr>
  "

value "map (func_map_blk mytoken_code) 
        [f_selector_id,f_return_uint_id,f_balance_offset_id]" 

definition x_id where "x_id = -134" 
definition h_id where "h_id = -118"
definition ls_ex_x0 where "ls_ex_x0 = [(x_id, (NL 0) :L U256)]" 
definition ls_ex_v0 where "ls_ex_v0 = [(v_id, (NL 0) :L U256)]" 
definition ls_ex_s0 where "ls_ex_s0 = [(s_id, (NL 0) :L U256)]" 

end