(******
Tests for type system of Yul language
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

theory "Tests_Typing"

imports Main "../Syntax" "../LMap" "../Typing"

begin

definition a_id where "a_id = -45" 
definition b_id where "b_id = -46"

value "type_e [(a_id, VType U256)] {} [] (EId a_id)"            (* typable *)
value "type_e [] {a_id} [] (EId a_id)"                          (* untypable *)
value "type_e [(a_id, VType U256)] {a_id} [] (EId a_id)"  
      (* typable but a_id should not exist in the set when actually typing an expression *)

value "type_e [] {} [] (EImLit ((NL 10) :L U256))" (* typable *)
value "type_e [] {} [] (EImLit ((NL 10) :L Bool))" (* untypable *)
value "type_e [] {} [] (EImLit (FL :L U256))"      (* untypable *)

value "type_e [] {} [] (ELit ((NL 10) :L U256))"  (* typable *)
value "type_e [] {} [] (ELit ((NL 10) :L Bool))"  (* untypable *)
value "type_e [] {} [] (ELit (FL :L U256))"       (* untypable *) 

value "type_e [] {} [] (VAR [(a_id, U256)])"                                  (* typable *)
value "type_e [(a_id, VType U256)] {} [] (VAR [(a_id, U256)])"                (* untypable *)
value "type_e [] {} [] (VAR [(a_id, U256)] ::- (EImLit ((NL 2) :L U256)))"      (* typable *)
value "type_e [(a_id, VType U256)] {} [] 
              (VAR [(a_id, U256)] ::- (EImLit ((NL 2) :L U256)))"               (* untypable *)
value "type_e [] {a_id} [] (VAR [(a_id, U256)] ::- (EImLit ((NL 2) :L U256)))"  (* untypable*)
value "type_e [] {} [] (VAR [(a_id, U256)] ::- (EImLit (TL :L Bool)))"          (* untypable *)

value "type_e [(a_id, VType U256)] {} [] ([a_id] ::= (EImLit ((NL 2) :L U256)))" (* typable *)
value "type_e [] {a_id} [] ([a_id] ::= (EImLit ((NL 2) :L U256)))" (* untypable *)
value "type_e [(a_id, VType U256)] {} [] ([a_id] ::= (EImLit (TL :L Bool)))" (* untypable *)

value "type_e [] {} [] (EList [ERetId (10, U256), ERetId (11, Bool)])"        (* tyapble *)
value "type_e [] {} [] (EList [EImLit ((NL 20) :L U256), EImLit (FL :L Bool)])"   (* typable *)
value "type_e [] {} [] (EList [EId 20])"                                      (* untypable *)

definition sum_id where "sum_id = -1"
definition f_add_id where "f_add_id = -2"

(*
definition add_func :: expr where 
  "add_func = (
    FUN f_add_id [] [(sum_id, U256)] IS
    BEGIN
      [[sum_id] ::= 
        CALL b_add_id [EImLit ((NL 3) :L U256), 
          CALL b_add_id [EImLit ((NL 2) :L U256), EImLit ((NL 1) :L U256)]]]
    END
  )"
*)

definition add_func :: expr where 
  "add_func = (
    FUN f_add_id [] [(sum_id, U256)] IS
    BEGIN
      [[sum_id] ::= EImLit ((NL 3) :L U256)
        ]
    END
  )"

value "type_e [(sum_id, VType U256)] {} [] ([sum_id] ::= EImLit ((NL 3) :L U256))"
value "type_b [(sum_id, VType U256)] {} [] 
                (BEGIN [[sum_id] ::= EImLit ((NL 3) :L U256)] END)"
value "type_e [] {} [] add_func"

definition data_id where "data_id = -11"
definition difference_id where "difference_id = -12"
definition f_sub_id where "f_sub_id = -13" 

definition sub_func :: expr where 
  "sub_func = (
    FUN f_sub_id [(data_id, U256)] [(difference_id, U256)] IS
    BEGIN
      [[difference_id] ::= 
          CALL b_sub_id [CALL b_add_id [EId data_id, EImLit ((NL 3) :L U256)], 
                         EImLit ((NL 2) :L U256)]]
    END
  )"

value "type_e [] {} [] sub_func"

definition data1_id where "data1_id = -21"
definition data2_id where "data2_id = -22"
definition pro_id where "pro_id = -23" 
definition f_mul_id where "f_mul_id = -24" 

definition mul_func :: expr where 
  "mul_func = (
    FUN f_mul_id [(data1_id, U256), (data2_id, U256)] [(pro_id, U256)] IS 
    BEGIN
      [[pro_id] ::= 
        CALL b_mul_id [EId data1_id, EId data2_id]]
    END
  )
  "

value "type_e [] {} [] mul_func"
value "type_e [(data2_id, VType U256)] {} [] mul_func" (* EUntypable *)
value "type_e [] {data2_id} [] mul_func" (* EUntypable !! *)

(*
pragma solidity ^0.5.0;
contract Code4{
    function DivAssem(uint _data) public pure returns (uint r) {
            assembly {
                switch _data
                case 0 
                {_data := 1 
                    r := 0
                }
                default
                {r := div(mul(10,_data),2)}
            }
    }
}
*)

definition data4_id where "data4_id = -31"
definition r_id where "r_id = -32"
definition f_div_id where "f_div_id = -33"

definition div_func :: expr where 
  "div_func = (
    FUN f_div_id [(data4_id, U256)] [(r_id, U256)] IS 
    BEGIN
      [
       SWITCH (EId data4_id)
       CASES
       [
        ((NL 0) :L U256,
          BEGIN
            [[data4_id] ::= EImLit ((NL 1) :L U256), 
             [r_id] ::= EImLit ((NL 0) :L U256)]
          END)
       ]
       DEFAULT
        Some (
          BEGIN
            [[r_id] ::= CALL b_div_id 
                          [CALL b_mul_id [EImLit ((NL 10) :L U256), EId data4_id], 
                           EImLit ((NL 2) :L U256)]]
          END)
      ]
    END
  )"

value "type_e [(data2_id, VType U256)] {} [] div_func"
value "type_e [] {data2_id} [] div_func"

(*
pragma solidity ^0.5.0;
contract Code5{
    function Code5Assem(uint _data) public pure returns (uint r) {
      assembly {
          r := add( _data ,sub(mul(div(_data,2),3),1))
          if gt(r,10) {r := 0}
      }
    }
}
*)

definition data6_id where "data6_id = -41" 
definition r6_id where "r6_id = -42" 
definition f_if_id where "f_if_id = -43" 

definition if_func :: expr where 
  "if_func = (
    FUN f_if_id [(data6_id, U256)] [(r6_id, U256)] IS 
    BEGIN
      [[r6_id] ::= CALL b_add_id 
                    [EId data6_id, 
                     CALL b_sub_id 
                          [CALL b_mul_id 
                                [CALL b_div_id [EId data6_id, EImLit ((NL 2) :L U256)],  
                                EImLit ((NL 3) :L U256)], 
                           EImLit ((NL 1) :L U256)]],
       IF CALL b_gt_id [EId r6_id, EImLit ((NL 10) :L U256)] 
       THEN 
         (BEGIN [[r6_id] ::= EImLit ((NL 0) :L U256)]  END)
      ]
    END
  )
  "

value "type_e [] {} [] if_func"

value "type_b [] {} [] (Blk [])" 

definition blk_nested :: block where 
  "blk_nested = 
    BEGIN [
      VAR [(a_id, U256)] ::- (EImLit ((NL 12) :L U256)), 
      IF (EImLit (TL :L Bool)) THEN
       (BEGIN [
          VAR [(b_id, U256)] ::- (CALL b_add_id [EId a_id, EImLit ((NL 2) :L U256)])
        ] END)
    ] END"

definition fte_blk_nested where 
  "fte_blk_nested = (case get_a_func_types_blk blk_nested of Some fte \<Rightarrow> fte)"

value "type_b [] {} [] blk_nested"

definition ff_id where "ff_id = -47"
definition gg_id where "gg_id = -48" 
definition x_id where "x_id = -49"

definition blk_nested2 :: block where 
  "blk_nested2 = 
    BEGIN [
      VAR [(a_id, U256)], 
      FUN ff_id [(b_id, U256)] [] IS 
      (BEGIN [
        VAR [(a_id, U256)]
      ] END)
    ] END"

definition fte_blk_nested2 where 
  "fte_blk_nested2 = (case get_a_func_types_blk blk_nested2 of Some fte \<Rightarrow> fte)"
value "fte_blk_nested2"
(* False, because of the shadowing of a_id *)
value "type_b [] {} fte_blk_nested2 blk_nested2" 

definition blk_nested3 :: block where 
  "blk_nested3 = 
    BEGIN [
      VAR [(a_id, U256)] ::- (EImLit ((NL 2) :L U256)), 
      FUN ff_id [(b_id, U256)] [(x_id, U256)] IS 
      (BEGIN [
        [x_id] ::= EId a_id
       ] END)
    ] END"

definition fte_blk_nested3 where 
  "fte_blk_nested3 = (case get_a_func_types_blk blk_nested3 of Some fte \<Rightarrow> fte)"
value "fte_blk_nested3"
(* False, because a_id cannot be accessed in the function body *)
value "type_b [] {} fte_blk_nested3 blk_nested3" 

definition blk_nested4 :: block where 
  "blk_nested4 = 
    BEGIN [
      FUN ff_id [] [] IS 
      (BEGIN [ 
          FUN ff_id [] [] IS (Blk [])
       ] END)
    ] END"

definition fte_blk_nested4 where 
  "fte_blk_nested4 = (case get_a_func_types_blk blk_nested4 of Some fte \<Rightarrow> fte)"
value "fte_blk_nested4"
(* False, due to re-use of function id ff_id *)
value "type_b [] {} [] blk_nested4"

definition expr_blk_nested :: expr where 
  "expr_blk_nested = 
    FUN ff_id [] [] IS 
      (BEGIN [ 
          FUN ff_id [] [] IS (Blk [])
       ] END)"

(* EUntypable due to re-use of function id ff_id *)
value "type_e [] {} [] expr_blk_nested"

definition offset1_id where "offset1_id = -51"
definition v1_id where "v1_id = -52" 
definition f_decode_as_uint1_id where "f_decode_as_uint1_id = -53"

definition decode_as_uint_func1 :: expr where 
  "decode_as_uint_func1 = 
    FUN f_decode_as_uint1_id [(offset1_id, U256)] [(v1_id, U256)] IS
    BEGIN
      [[v1_id] ::= CALL b_calldataload_id 
                       [CALL b_add_id [EImLit ((NL 4) :L U256), 
                                       CALL b_mul_id [(EId offset1_id), EImLit ((NL 32) :L U256)]]]]
    END"
  
value "type_e [] {} [] decode_as_uint_func1"

definition f_selector_id where "f_selector_id = 501"
definition f_return_uint_id where "f_return_uint_id = 502"
definition v_id where "v_id = 503"
definition s_id where "s_id = 504" 

definition return_uint_func :: expr where 
  "return_uint_func = 
    (FUN f_return_uint_id [(v_id, U256)] [] IS 
      (BEGIN
          [CALL b_mstore_id [EImLit ((NL 0) :L U256), EId v_id], 
           CALL b_return_id [EImLit ((NL 0) :L U256), EImLit ((NL 0x20) :L U256)]]
       END)
    )"

definition selector_func :: expr where 
  "selector_func = 
    (FUN f_selector_id [] [(s_id, U256)] IS
     BEGIN 
       [[s_id] ::= (CALL b_div_id 
                    [CALL b_calldataload_id [EImLit ((NL 0) :L U256)],
                     EImLit ((NL 0x100000000000000000000000000000000000000000000000000000000):L U256)]
                   )
        ]
     END
    )
  "

definition arith_contract :: block where 
  "arith_contract = (
    BEGIN
    [
      SWITCH CALL f_selector_id [] 
      CASES
      [
        ((NL 1) :L U256, 
         BEGIN
          [CALL f_return_uint_id [CALL f_add_id []]]
         END), 
        ((NL 2) :L U256, 
         BEGIN
          [CALL f_return_uint_id 
            [CALL f_sub_id [CALL f_decode_as_uint1_id [EImLit ((NL 0) :L U256)]]]]
         END), 
        ((NL 3) :L U256, 
         BEGIN
          [CALL f_return_uint_id 
            [CALL f_mul_id [CALL f_decode_as_uint1_id [EImLit ((NL 0) :L U256)], 
                            CALL f_decode_as_uint1_id [EImLit ((NL 1) :L U256)]]]]
         END), 
        ((NL 4) :L U256, 
         BEGIN
          [CALL f_return_uint_id 
            [CALL f_div_id [CALL f_decode_as_uint1_id [EImLit ((NL 0) :L U256)]]]]
         END)
      ]
      DEFAULT 
       Some (BEGIN [CALL b_revert_id [EImLit ((NL 0) :L U256), EImLit ((NL 0) :L U256)]] END), 

      selector_func, 
      decode_as_uint_func1, 
      return_uint_func, 
      add_func, 
      sub_func, 
      mul_func, 
      div_func
    ]
    END
  )
  "

value "get_a_func_types ([
      SWITCH CALL f_selector_id [] 
      CASES
      [
        ((NL 1) :L U256, 
         BEGIN
          []
         END)
      ]
      DEFAULT 
       Some (BEGIN [CALL b_revert_id [EImLit ((NL 0) :L U256), EImLit ((NL 0) :L U256)]] END), 
      selector_func, 
      decode_as_uint_func1, 
      return_uint_func, 
      add_func, 
      sub_func, 
      mul_func, 
      div_func])"

definition fte_arith_ctr where 
  "fte_arith_ctr = (case get_a_func_types_blk arith_contract of Some fte \<Rightarrow> fte)"

value "type_b [] {} fte_arith_ctr arith_contract"

end