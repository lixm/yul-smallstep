(******
Execution of the ERC20 token contract with input that invokes transfer_func
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

theory "RunToken"

imports 
 HOL.Option
  Main "../Syntax" "../Typing" "../SmallStep" MyToken "../utils/Keccak" 
  (*"$ISABELLE_HOME/src/HOL/Word/Word"*)

begin

definition caller_account  :: "account"  where 
  "caller_account = \<lparr>
    code_of = None,
    store_of = (\<lambda>x . (case x of _ => (0xff :: (256 word)))),
    bal_of = (0x0 :: 256 word),
    nonce_of = (0x0 :: 256 word)
  \<rparr>"

definition mytoken_account  :: "account"  where 
  "mytoken_account = \<lparr>
    code_of = Some mytoken_code,
    store_of = 
      (\<lambda>x. (if x = (43633114540367443769613365612029762689758420575593515939555225863214374745012 :: 256 word) 
            then 99999999999 
            else (
              if (x = (77889682276648159348121498188387380826073215901308117747004906171223545284475 :: 256 word))
              then 10000000000
              else 0))),
    bal_of = (0xfff4 :: 256 word), \<comment> \<open> this is the ether balance that does not have to do with this demo\<close>
    nonce_of = (0x0 :: 256 word)
  \<rparr>"

definition gs1_bfun :: gstate where
  "gs1_bfun = 
  \<lparr>
    addr_of =  0x0DCd2F752394c41875e259e00bb44fd505297caF,
    saddr_of = 0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c, 
    money_of = (0x0 :: 256 word), 
    input_of = [(0xa9 :: 8 word), (0x05 :: 8 word), (0x9c :: 8 word), (0xbb :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), 
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), 
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word), (0x0 :: 8 word),
                (0x0 :: 8 word), (0x1 :: 8 word)],
    mem_of = (\<lambda>x. 0x01), 
    naws_of = 3, 
    gas_of = 3000000, 
    ct_of = 10,
    accs_of = (\<lambda>x. (if x = (0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c::address) then 
                      (Some caller_account)
                    else (
                      if x = (0x0DCd2F752394c41875e259e00bb44fd505297caF :: address) then 
                        (Some mytoken_account)
                      else 
                        None))),
    refund_of = (0x0 :: 256 word),
    logs_of = [], 
    ss_of = {}
  \<rparr>"
(*
value "eval_rbuiltin gs1_bfun CalldataLoad [NL 3]"
*)



definition gstk_total_contract where
  "gstk_total_contract = ((GFrmNormal 
    ([LFrm_B (mytoken_code, ls_ex_s0, (get_func_values mytoken_code), None)]) 
      gs1_bfun CKDummy) # [])" 

(*
value "multi_step tre0_ex1 gstk_total_contract 1 20"
value "multi_step tre0_ex1 gstk_total_contract 2 20"
value "multi_step tre0_ex1 gstk_total_contract 3 20"
value "multi_step tre0_ex1 gstk_total_contract 4 20"
value "multi_step tre0_ex1 gstk_total_contract 5 20"
value "multi_step tre0_ex1 gstk_total_contract 6 20"
value "multi_step tre0_ex1 gstk_total_contract 7 20"
value "multi_step tre0_ex1 gstk_total_contract 8 20"
value "multi_step tre0_ex1 gstk_total_contract 9 20"
value "multi_step tre0_ex1 gstk_total_contract 10 20"
value "multi_step tre0_ex1 gstk_total_contract 11 20"
value "multi_step tre0_ex1 gstk_total_contract 12 20"
value "multi_step tre0_ex1 gstk_total_contract 13 20"
value "multi_step tre0_ex1 gstk_total_contract 14 20"
value "multi_step tre0_ex1 gstk_total_contract 15 20"
value "multi_step tre0_ex1 gstk_total_contract 16 20"
value "multi_step tre0_ex1 gstk_total_contract 17 20"
value "multi_step tre0_ex1 gstk_total_contract 18 20"
value "multi_step tre0_ex1 gstk_total_contract 19 20"
value "multi_step tre0_ex1 gstk_total_contract 20 20"
value "multi_step tre0_ex1 gstk_total_contract 21 20"
value "multi_step tre0_ex1 gstk_total_contract 22 20"
value "multi_step tre0_ex1 gstk_total_contract 23 20"
value "multi_step tre0_ex1 gstk_total_contract 24 20"
value "multi_step tre0_ex1 gstk_total_contract 25 20"
value "multi_step tre0_ex1 gstk_total_contract 26 20"
value "multi_step tre0_ex1 gstk_total_contract 27 20"
value "multi_step tre0_ex1 gstk_total_contract 28 20"
value "multi_step tre0_ex1 gstk_total_contract 29 20"
value "multi_step tre0_ex1 gstk_total_contract 30 20"
value "multi_step tre0_ex1 gstk_total_contract 31 20"
value "multi_step tre0_ex1 gstk_total_contract 32 20"
value "multi_step tre0_ex1 gstk_total_contract 33 20"
value "multi_step tre0_ex1 gstk_total_contract 34 20"
value "multi_step tre0_ex1 gstk_total_contract 35 20"
value "multi_step tre0_ex1 gstk_total_contract 36 20"
value "multi_step tre0_ex1 gstk_total_contract 37 20"
value "multi_step tre0_ex1 gstk_total_contract 38 20"
value "multi_step tre0_ex1 gstk_total_contract 39 20"
value "multi_step tre0_ex1 gstk_total_contract 40 20"
value "multi_step tre0_ex1 gstk_total_contract 41 20"
value "multi_step tre0_ex1 gstk_total_contract 42 20"
value "multi_step tre0_ex1 gstk_total_contract 43 20"
value "multi_step tre0_ex1 gstk_total_contract 44 20"
value "multi_step tre0_ex1 gstk_total_contract 45 20"
value "multi_step tre0_ex1 gstk_total_contract 46 20"
value "multi_step tre0_ex1 gstk_total_contract 47 20"
value "multi_step tre0_ex1 gstk_total_contract 48 20"
value "multi_step tre0_ex1 gstk_total_contract 49 20"
value "multi_step tre0_ex1 gstk_total_contract 50 20"
value "multi_step tre0_ex1 gstk_total_contract 53 20"
value "multi_step tre0_ex1 gstk_total_contract 54 20"
value "multi_step tre0_ex1 gstk_total_contract 55 20"
value "multi_step tre0_ex1 gstk_total_contract 56 20"
value "multi_step tre0_ex1 gstk_total_contract 57 20"
value "multi_step tre0_ex1 gstk_total_contract 58 20"
value "multi_step tre0_ex1 gstk_total_contract 59 20"
value "multi_step tre0_ex1 gstk_total_contract 60 20"
value "multi_step tre0_ex1 gstk_total_contract 61 20"
value "multi_step tre0_ex1 gstk_total_contract 63 20"
value "multi_step tre0_ex1 gstk_total_contract 64 20"
value "multi_step tre0_ex1 gstk_total_contract 65 20"
value "multi_step tre0_ex1 gstk_total_contract 66 20"
value "multi_step tre0_ex1 gstk_total_contract 67 20"
value "multi_step tre0_ex1 gstk_total_contract 68 20"
value "multi_step tre0_ex1 gstk_total_contract 69 20"
value "multi_step tre0_ex1 gstk_total_contract 70 20"
value "multi_step tre0_ex1 gstk_total_contract 71 20"
value "multi_step tre0_ex1 gstk_total_contract 72 20"
value "multi_step tre0_ex1 gstk_total_contract 73 20"
value "multi_step tre0_ex1 gstk_total_contract 74 20"
value "multi_step tre0_ex1 gstk_total_contract 75 20"
value "multi_step tre0_ex1 gstk_total_contract 76 20"
value "multi_step tre0_ex1 gstk_total_contract 77 20"
value "multi_step tre0_ex1 gstk_total_contract 78 20"
value "multi_step tre0_ex1 gstk_total_contract 79 20"
value "multi_step tre0_ex1 gstk_total_contract 81 20"
value "multi_step tre0_ex1 gstk_total_contract 82 20"
value "multi_step tre0_ex1 gstk_total_contract 83 20"
value "multi_step tre0_ex1 gstk_total_contract 84 20"
value "multi_step tre0_ex1 gstk_total_contract 86 20"
value "multi_step tre0_ex1 gstk_total_contract 87 20"
value "multi_step tre0_ex1 gstk_total_contract 88 20"
value "multi_step tre0_ex1 gstk_total_contract 89 20"
value "multi_step tre0_ex1 gstk_total_contract 90 20"
value "multi_step tre0_ex1 gstk_total_contract 91 20"
value "multi_step tre0_ex1 gstk_total_contract 92 20"
value "multi_step tre0_ex1 gstk_total_contract 93 20"
value "multi_step tre0_ex1 gstk_total_contract 94 20"
value "multi_step tre0_ex1 gstk_total_contract 95 20"
value "multi_step tre0_ex1 gstk_total_contract 96 20"
value "multi_step tre0_ex1 gstk_total_contract 97 20"
value "multi_step tre0_ex1 gstk_total_contract 98 20"
value "multi_step tre0_ex1 gstk_total_contract 101 20"
value "multi_step tre0_ex1 gstk_total_contract 102 20"
value "multi_step tre0_ex1 gstk_total_contract 103 20"
value "multi_step tre0_ex1 gstk_total_contract 104 20"
value "multi_step tre0_ex1 gstk_total_contract 105 20"
value "multi_step tre0_ex1 gstk_total_contract 106 20"
value "multi_step tre0_ex1 gstk_total_contract 108 20"
value "multi_step tre0_ex1 gstk_total_contract 109 20"
value "multi_step tre0_ex1 gstk_total_contract 110 20"
value "multi_step tre0_ex1 gstk_total_contract 111 20"
value "multi_step tre0_ex1 gstk_total_contract 112 20"
value "multi_step tre0_ex1 gstk_total_contract 113 20"
value "multi_step tre0_ex1 gstk_total_contract 114 20"
value "multi_step tre0_ex1 gstk_total_contract 115 20"
value "multi_step tre0_ex1 gstk_total_contract 116 20"
value "multi_step tre0_ex1 gstk_total_contract 117 20"
value "multi_step tre0_ex1 gstk_total_contract 118 20"
value "multi_step tre0_ex1 gstk_total_contract 119 20"
value "multi_step tre0_ex1 gstk_total_contract 122 20"
value "multi_step tre0_ex1 gstk_total_contract 123 20"
value "multi_step tre0_ex1 gstk_total_contract 124 20"
value "multi_step tre0_ex1 gstk_total_contract 126 20"
value "multi_step tre0_ex1 gstk_total_contract 127 20"
value "multi_step tre0_ex1 gstk_total_contract 128 20"
value "multi_step tre0_ex1 gstk_total_contract 129 20"
value "multi_step tre0_ex1 gstk_total_contract 130 20"
value "multi_step tre0_ex1 gstk_total_contract 131 20"
value "multi_step tre0_ex1 gstk_total_contract 132 20"
value "multi_step tre0_ex1 gstk_total_contract 133 20"
value "multi_step tre0_ex1 gstk_total_contract 134 20"
value "multi_step tre0_ex1 gstk_total_contract 135 20"
value "multi_step tre0_ex1 gstk_total_contract 136 20"
value "multi_step tre0_ex1 gstk_total_contract 137 20"
value "multi_step tre0_ex1 gstk_total_contract 138 20"
value "multi_step tre0_ex1 gstk_total_contract 139 20"
value "multi_step tre0_ex1 gstk_total_contract 140 20"
value "multi_step tre0_ex1 gstk_total_contract 141 20"
value "multi_step tre0_ex1 gstk_total_contract 142 20"
value "multi_step tre0_ex1 gstk_total_contract 143 20"
value "multi_step tre0_ex1 gstk_total_contract 144 20"
value "multi_step tre0_ex1 gstk_total_contract 145 20"
value "multi_step tre0_ex1 gstk_total_contract 146 20"
value "multi_step tre0_ex1 gstk_total_contract 147 20"
value "multi_step tre0_ex1 gstk_total_contract 149 20"
value "multi_step tre0_ex1 gstk_total_contract 150 20"
value "multi_step tre0_ex1 gstk_total_contract 151 20"
value "multi_step tre0_ex1 gstk_total_contract 152 20"
value "multi_step tre0_ex1 gstk_total_contract 153 20"
value "multi_step tre0_ex1 gstk_total_contract 154 20"
value "multi_step tre0_ex1 gstk_total_contract 156 20"
value "multi_step tre0_ex1 gstk_total_contract 157 20"
value "multi_step tre0_ex1 gstk_total_contract 158 20"
value "multi_step tre0_ex1 gstk_total_contract 159 20"
value "multi_step tre0_ex1 gstk_total_contract 160 20"
value "multi_step tre0_ex1 gstk_total_contract 163 20"
value "multi_step tre0_ex1 gstk_total_contract 164 20"
value "multi_step tre0_ex1 gstk_total_contract 165 20"
value "multi_step tre0_ex1 gstk_total_contract 166 20"
value "multi_step tre0_ex1 gstk_total_contract 167 20"
value "multi_step tre0_ex1 gstk_total_contract 168 20"
value "multi_step tre0_ex1 gstk_total_contract 170 20"
value "multi_step tre0_ex1 gstk_total_contract 171 20"
value "multi_step tre0_ex1 gstk_total_contract 172 20"
value "multi_step tre0_ex1 gstk_total_contract 173 20"
value "multi_step tre0_ex1 gstk_total_contract 174 20"
value "multi_step tre0_ex1 gstk_total_contract 175 20"
value "multi_step tre0_ex1 gstk_total_contract 176 20"
value "multi_step tre0_ex1 gstk_total_contract 177 20"
value "multi_step tre0_ex1 gstk_total_contract 178 20"
value "multi_step tre0_ex1 gstk_total_contract 179 20"
value "multi_step tre0_ex1 gstk_total_contract 180 20"
value "multi_step tre0_ex1 gstk_total_contract 183 20"
value "multi_step tre0_ex1 gstk_total_contract 184 20"
value "multi_step tre0_ex1 gstk_total_contract 185 20"
value "multi_step tre0_ex1 gstk_total_contract 186 20"
value "multi_step tre0_ex1 gstk_total_contract 188 20"
value "multi_step tre0_ex1 gstk_total_contract 189 20"
value "multi_step tre0_ex1 gstk_total_contract 190 20"
value "multi_step tre0_ex1 gstk_total_contract 191 20"
value "multi_step tre0_ex1 gstk_total_contract 192 20"
value "multi_step tre0_ex1 gstk_total_contract 193 20"
value "multi_step tre0_ex1 gstk_total_contract 194 20"
value "multi_step tre0_ex1 gstk_total_contract 195 20"
value "multi_step tre0_ex1 gstk_total_contract 196 20"
value "multi_step tre0_ex1 gstk_total_contract 197 20"
value "multi_step tre0_ex1 gstk_total_contract 198 20"
value "multi_step tre0_ex1 gstk_total_contract 200 20"
value "multi_step tre0_ex1 gstk_total_contract 201 20"
value "multi_step tre0_ex1 gstk_total_contract 202 20"
value "multi_step tre0_ex1 gstk_total_contract 203 20"
value "multi_step tre0_ex1 gstk_total_contract 204 20"
value "multi_step tre0_ex1 gstk_total_contract 205 20"
value "multi_step tre0_ex1 gstk_total_contract 206 20"
value "multi_step tre0_ex1 gstk_total_contract 207 20"
value "multi_step tre0_ex1 gstk_total_contract 208 20"
value "multi_step tre0_ex1 gstk_total_contract 209 20"
value "multi_step tre0_ex1 gstk_total_contract 210 20"
value "multi_step tre0_ex1 gstk_total_contract 211 20"
value "multi_step tre0_ex1 gstk_total_contract 212 20"
value "multi_step tre0_ex1 gstk_total_contract 213 20"
value "multi_step tre0_ex1 gstk_total_contract 214 20"
value "multi_step tre0_ex1 gstk_total_contract 215 20"
value "multi_step tre0_ex1 gstk_total_contract 216 20"
value "multi_step tre0_ex1 gstk_total_contract 217 20"
value "multi_step tre0_ex1 gstk_total_contract 218 20"
value "multi_step tre0_ex1 gstk_total_contract 219 20"
value "multi_step tre0_ex1 gstk_total_contract 220 20"
value "multi_step tre0_ex1 gstk_total_contract 223 20"
value "multi_step tre0_ex1 gstk_total_contract 224 20"
value "multi_step tre0_ex1 gstk_total_contract 225 20"
value "multi_step tre0_ex1 gstk_total_contract 226 20"
value "multi_step tre0_ex1 gstk_total_contract 227 20"
value "multi_step tre0_ex1 gstk_total_contract 228 20"
value "multi_step tre0_ex1 gstk_total_contract 229 20"
value "multi_step tre0_ex1 gstk_total_contract 230 20"
value "multi_step tre0_ex1 gstk_total_contract 231 20"
value "multi_step tre0_ex1 gstk_total_contract 232 20"
value "multi_step tre0_ex1 gstk_total_contract 233 20"
value "multi_step tre0_ex1 gstk_total_contract 234 20"
value "multi_step tre0_ex1 gstk_total_contract 235 20"
value "multi_step tre0_ex1 gstk_total_contract 236 20"
value "multi_step tre0_ex1 gstk_total_contract 238 20"
value "multi_step tre0_ex1 gstk_total_contract 239 20"
value "multi_step tre0_ex1 gstk_total_contract 240 20"
value "multi_step tre0_ex1 gstk_total_contract 241 20"
value "multi_step tre0_ex1 gstk_total_contract 242 20"
value "multi_step tre0_ex1 gstk_total_contract 243 20"
value "multi_step tre0_ex1 gstk_total_contract 244 20"
value "multi_step tre0_ex1 gstk_total_contract 245 20"
value "multi_step tre0_ex1 gstk_total_contract 246 20"
value "multi_step tre0_ex1 gstk_total_contract 247 20"
value "multi_step tre0_ex1 gstk_total_contract 248 20"
value "multi_step tre0_ex1 gstk_total_contract 249 20"
value "multi_step tre0_ex1 gstk_total_contract 250 20"
value "multi_step tre0_ex1 gstk_total_contract 251 20"
value "multi_step tre0_ex1 gstk_total_contract 252 20"
value "multi_step tre0_ex1 gstk_total_contract 253 20"
value "multi_step tre0_ex1 gstk_total_contract 256 20"
value "multi_step tre0_ex1 gstk_total_contract 257 20"
value "multi_step tre0_ex1 gstk_total_contract 258 20"
value "multi_step tre0_ex1 gstk_total_contract 259 20"
value "multi_step tre0_ex1 gstk_total_contract 260 20"
value "multi_step tre0_ex1 gstk_total_contract 261 20"
value "multi_step tre0_ex1 gstk_total_contract 262 20"
value "multi_step tre0_ex1 gstk_total_contract 264 20"
value "multi_step tre0_ex1 gstk_total_contract 265 20"
value "multi_step tre0_ex1 gstk_total_contract 266 20"
value "multi_step tre0_ex1 gstk_total_contract 268 20"
value "multi_step tre0_ex1 gstk_total_contract 269 20"
value "multi_step tre0_ex1 gstk_total_contract 270 20"
*)

value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 0 20)
         (get_balance_offset
           0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c)"
value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 165 20)
         (get_balance_offset
           0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c)"
value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 166 20)
         (get_balance_offset
           0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c)"

value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 0 20) 
          (get_balance_offset 0x0)"
value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 245 20) 
          (get_balance_offset 0x0)"
value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 246 20) 
          (get_balance_offset 0x0)"

value "get_balance_offset 0x0"
value "get_balance_offset 0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c"

end