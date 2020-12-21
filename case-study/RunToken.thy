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
value "multi_step tre0_ex1 gstk_total_contract 1"
value "multi_step tre0_ex1 gstk_total_contract 2"
value "multi_step tre0_ex1 gstk_total_contract 3"
value "multi_step tre0_ex1 gstk_total_contract 4"
value "multi_step tre0_ex1 gstk_total_contract 5"
value "multi_step tre0_ex1 gstk_total_contract 6"
value "multi_step tre0_ex1 gstk_total_contract 7"
value "multi_step tre0_ex1 gstk_total_contract 8"
value "multi_step tre0_ex1 gstk_total_contract 9"
value "multi_step tre0_ex1 gstk_total_contract 10"
value "multi_step tre0_ex1 gstk_total_contract 11"
value "multi_step tre0_ex1 gstk_total_contract 12"
value "multi_step tre0_ex1 gstk_total_contract 13"
value "multi_step tre0_ex1 gstk_total_contract 14"
value "multi_step tre0_ex1 gstk_total_contract 15"
value "multi_step tre0_ex1 gstk_total_contract 16"
value "multi_step tre0_ex1 gstk_total_contract 17"
value "multi_step tre0_ex1 gstk_total_contract 18"
value "multi_step tre0_ex1 gstk_total_contract 19"
value "multi_step tre0_ex1 gstk_total_contract 20"
value "multi_step tre0_ex1 gstk_total_contract 21"
value "multi_step tre0_ex1 gstk_total_contract 22"
value "multi_step tre0_ex1 gstk_total_contract 23"
value "multi_step tre0_ex1 gstk_total_contract 24"
value "multi_step tre0_ex1 gstk_total_contract 25"
value "multi_step tre0_ex1 gstk_total_contract 26"
value "multi_step tre0_ex1 gstk_total_contract 27"
value "multi_step tre0_ex1 gstk_total_contract 28"
value "multi_step tre0_ex1 gstk_total_contract 29"
value "multi_step tre0_ex1 gstk_total_contract 30"
value "multi_step tre0_ex1 gstk_total_contract 31"
value "multi_step tre0_ex1 gstk_total_contract 32"
value "multi_step tre0_ex1 gstk_total_contract 33"
value "multi_step tre0_ex1 gstk_total_contract 34"
value "multi_step tre0_ex1 gstk_total_contract 35"
value "multi_step tre0_ex1 gstk_total_contract 36"
value "multi_step tre0_ex1 gstk_total_contract 37"
value "multi_step tre0_ex1 gstk_total_contract 38"
value "multi_step tre0_ex1 gstk_total_contract 39"
value "multi_step tre0_ex1 gstk_total_contract 40"
value "multi_step tre0_ex1 gstk_total_contract 41"
value "multi_step tre0_ex1 gstk_total_contract 42"
value "multi_step tre0_ex1 gstk_total_contract 43"
value "multi_step tre0_ex1 gstk_total_contract 44"
value "multi_step tre0_ex1 gstk_total_contract 45"
value "multi_step tre0_ex1 gstk_total_contract 46"
value "multi_step tre0_ex1 gstk_total_contract 47"
value "multi_step tre0_ex1 gstk_total_contract 48"
value "multi_step tre0_ex1 gstk_total_contract 49"
value "multi_step tre0_ex1 gstk_total_contract 50"
value "multi_step tre0_ex1 gstk_total_contract 53"
value "multi_step tre0_ex1 gstk_total_contract 54"
value "multi_step tre0_ex1 gstk_total_contract 55"
value "multi_step tre0_ex1 gstk_total_contract 56"
value "multi_step tre0_ex1 gstk_total_contract 57"
value "multi_step tre0_ex1 gstk_total_contract 58"
value "multi_step tre0_ex1 gstk_total_contract 59"
value "multi_step tre0_ex1 gstk_total_contract 60"
value "multi_step tre0_ex1 gstk_total_contract 61"
value "multi_step tre0_ex1 gstk_total_contract 63"
value "multi_step tre0_ex1 gstk_total_contract 64"
value "multi_step tre0_ex1 gstk_total_contract 65"
value "multi_step tre0_ex1 gstk_total_contract 66"
value "multi_step tre0_ex1 gstk_total_contract 67"
value "multi_step tre0_ex1 gstk_total_contract 68"
value "multi_step tre0_ex1 gstk_total_contract 69"
value "multi_step tre0_ex1 gstk_total_contract 70"
value "multi_step tre0_ex1 gstk_total_contract 71"
value "multi_step tre0_ex1 gstk_total_contract 72"
value "multi_step tre0_ex1 gstk_total_contract 73"
value "multi_step tre0_ex1 gstk_total_contract 74"
value "multi_step tre0_ex1 gstk_total_contract 75"
value "multi_step tre0_ex1 gstk_total_contract 76"
value "multi_step tre0_ex1 gstk_total_contract 77"
value "multi_step tre0_ex1 gstk_total_contract 78"
value "multi_step tre0_ex1 gstk_total_contract 79"
value "multi_step tre0_ex1 gstk_total_contract 81"
value "multi_step tre0_ex1 gstk_total_contract 82"
value "multi_step tre0_ex1 gstk_total_contract 83"
value "multi_step tre0_ex1 gstk_total_contract 84"
value "multi_step tre0_ex1 gstk_total_contract 86"
value "multi_step tre0_ex1 gstk_total_contract 87"
value "multi_step tre0_ex1 gstk_total_contract 88"
value "multi_step tre0_ex1 gstk_total_contract 89"
value "multi_step tre0_ex1 gstk_total_contract 90"
value "multi_step tre0_ex1 gstk_total_contract 91"
value "multi_step tre0_ex1 gstk_total_contract 92"
value "multi_step tre0_ex1 gstk_total_contract 93"
value "multi_step tre0_ex1 gstk_total_contract 94"
value "multi_step tre0_ex1 gstk_total_contract 95"
value "multi_step tre0_ex1 gstk_total_contract 96"
value "multi_step tre0_ex1 gstk_total_contract 97"
value "multi_step tre0_ex1 gstk_total_contract 98"
value "multi_step tre0_ex1 gstk_total_contract 101"
value "multi_step tre0_ex1 gstk_total_contract 102"
value "multi_step tre0_ex1 gstk_total_contract 103"
value "multi_step tre0_ex1 gstk_total_contract 104"
value "multi_step tre0_ex1 gstk_total_contract 105"
value "multi_step tre0_ex1 gstk_total_contract 106"
value "multi_step tre0_ex1 gstk_total_contract 108"
value "multi_step tre0_ex1 gstk_total_contract 109"
value "multi_step tre0_ex1 gstk_total_contract 110"
value "multi_step tre0_ex1 gstk_total_contract 111"
value "multi_step tre0_ex1 gstk_total_contract 112"
value "multi_step tre0_ex1 gstk_total_contract 113"
value "multi_step tre0_ex1 gstk_total_contract 114"
value "multi_step tre0_ex1 gstk_total_contract 115"
value "multi_step tre0_ex1 gstk_total_contract 116"
value "multi_step tre0_ex1 gstk_total_contract 117"
value "multi_step tre0_ex1 gstk_total_contract 118"
value "multi_step tre0_ex1 gstk_total_contract 119"
value "multi_step tre0_ex1 gstk_total_contract 122"
value "multi_step tre0_ex1 gstk_total_contract 123"
value "multi_step tre0_ex1 gstk_total_contract 124"
value "multi_step tre0_ex1 gstk_total_contract 126"
value "multi_step tre0_ex1 gstk_total_contract 127"
value "multi_step tre0_ex1 gstk_total_contract 128"
value "multi_step tre0_ex1 gstk_total_contract 129"
value "multi_step tre0_ex1 gstk_total_contract 130"
value "multi_step tre0_ex1 gstk_total_contract 131"
value "multi_step tre0_ex1 gstk_total_contract 132"
value "multi_step tre0_ex1 gstk_total_contract 133"
value "multi_step tre0_ex1 gstk_total_contract 134"
value "multi_step tre0_ex1 gstk_total_contract 135"
value "multi_step tre0_ex1 gstk_total_contract 136"
value "multi_step tre0_ex1 gstk_total_contract 137"
value "multi_step tre0_ex1 gstk_total_contract 138"
value "multi_step tre0_ex1 gstk_total_contract 139"
value "multi_step tre0_ex1 gstk_total_contract 140"
value "multi_step tre0_ex1 gstk_total_contract 141"
value "multi_step tre0_ex1 gstk_total_contract 142"
value "multi_step tre0_ex1 gstk_total_contract 143"
value "multi_step tre0_ex1 gstk_total_contract 144"
value "multi_step tre0_ex1 gstk_total_contract 145"
value "multi_step tre0_ex1 gstk_total_contract 146"
value "multi_step tre0_ex1 gstk_total_contract 147"
value "multi_step tre0_ex1 gstk_total_contract 149"
value "multi_step tre0_ex1 gstk_total_contract 150"
value "multi_step tre0_ex1 gstk_total_contract 151"
value "multi_step tre0_ex1 gstk_total_contract 152"
value "multi_step tre0_ex1 gstk_total_contract 153"
value "multi_step tre0_ex1 gstk_total_contract 154"
value "multi_step tre0_ex1 gstk_total_contract 156"
value "multi_step tre0_ex1 gstk_total_contract 157"
value "multi_step tre0_ex1 gstk_total_contract 158"
value "multi_step tre0_ex1 gstk_total_contract 159"
value "multi_step tre0_ex1 gstk_total_contract 160"
value "multi_step tre0_ex1 gstk_total_contract 163"
value "multi_step tre0_ex1 gstk_total_contract 164"
value "multi_step tre0_ex1 gstk_total_contract 165"
value "multi_step tre0_ex1 gstk_total_contract 166"
value "multi_step tre0_ex1 gstk_total_contract 167"
value "multi_step tre0_ex1 gstk_total_contract 168"
value "multi_step tre0_ex1 gstk_total_contract 170"
value "multi_step tre0_ex1 gstk_total_contract 171"
value "multi_step tre0_ex1 gstk_total_contract 172"
value "multi_step tre0_ex1 gstk_total_contract 173"
value "multi_step tre0_ex1 gstk_total_contract 174"
value "multi_step tre0_ex1 gstk_total_contract 175"
value "multi_step tre0_ex1 gstk_total_contract 176"
value "multi_step tre0_ex1 gstk_total_contract 177"
value "multi_step tre0_ex1 gstk_total_contract 178"
value "multi_step tre0_ex1 gstk_total_contract 179"
value "multi_step tre0_ex1 gstk_total_contract 180"
value "multi_step tre0_ex1 gstk_total_contract 183"
value "multi_step tre0_ex1 gstk_total_contract 184"
value "multi_step tre0_ex1 gstk_total_contract 185"
value "multi_step tre0_ex1 gstk_total_contract 186"
value "multi_step tre0_ex1 gstk_total_contract 188"
value "multi_step tre0_ex1 gstk_total_contract 189"
value "multi_step tre0_ex1 gstk_total_contract 190"
value "multi_step tre0_ex1 gstk_total_contract 191"
value "multi_step tre0_ex1 gstk_total_contract 192"
value "multi_step tre0_ex1 gstk_total_contract 193"
value "multi_step tre0_ex1 gstk_total_contract 194"
value "multi_step tre0_ex1 gstk_total_contract 195"
value "multi_step tre0_ex1 gstk_total_contract 196"
value "multi_step tre0_ex1 gstk_total_contract 197"
value "multi_step tre0_ex1 gstk_total_contract 198"
value "multi_step tre0_ex1 gstk_total_contract 200"
value "multi_step tre0_ex1 gstk_total_contract 201"
value "multi_step tre0_ex1 gstk_total_contract 202"
value "multi_step tre0_ex1 gstk_total_contract 203"
value "multi_step tre0_ex1 gstk_total_contract 204"
value "multi_step tre0_ex1 gstk_total_contract 205"
value "multi_step tre0_ex1 gstk_total_contract 206"
value "multi_step tre0_ex1 gstk_total_contract 207"
value "multi_step tre0_ex1 gstk_total_contract 208"
value "multi_step tre0_ex1 gstk_total_contract 209"
value "multi_step tre0_ex1 gstk_total_contract 210"
value "multi_step tre0_ex1 gstk_total_contract 211"
value "multi_step tre0_ex1 gstk_total_contract 212"
value "multi_step tre0_ex1 gstk_total_contract 213"
value "multi_step tre0_ex1 gstk_total_contract 214"
value "multi_step tre0_ex1 gstk_total_contract 215"
value "multi_step tre0_ex1 gstk_total_contract 216"
value "multi_step tre0_ex1 gstk_total_contract 217"
value "multi_step tre0_ex1 gstk_total_contract 218"
value "multi_step tre0_ex1 gstk_total_contract 219"
value "multi_step tre0_ex1 gstk_total_contract 220"
value "multi_step tre0_ex1 gstk_total_contract 223"
value "multi_step tre0_ex1 gstk_total_contract 224"
value "multi_step tre0_ex1 gstk_total_contract 225"
value "multi_step tre0_ex1 gstk_total_contract 226"
value "multi_step tre0_ex1 gstk_total_contract 227"
value "multi_step tre0_ex1 gstk_total_contract 228"
value "multi_step tre0_ex1 gstk_total_contract 229"
value "multi_step tre0_ex1 gstk_total_contract 230"
value "multi_step tre0_ex1 gstk_total_contract 231"
value "multi_step tre0_ex1 gstk_total_contract 232"
value "multi_step tre0_ex1 gstk_total_contract 233"
value "multi_step tre0_ex1 gstk_total_contract 234"
value "multi_step tre0_ex1 gstk_total_contract 235"
value "multi_step tre0_ex1 gstk_total_contract 236"
value "multi_step tre0_ex1 gstk_total_contract 238"
value "multi_step tre0_ex1 gstk_total_contract 239"
value "multi_step tre0_ex1 gstk_total_contract 240"
value "multi_step tre0_ex1 gstk_total_contract 241"
value "multi_step tre0_ex1 gstk_total_contract 242"
value "multi_step tre0_ex1 gstk_total_contract 243"
value "multi_step tre0_ex1 gstk_total_contract 244"
value "multi_step tre0_ex1 gstk_total_contract 245"
value "multi_step tre0_ex1 gstk_total_contract 246"
value "multi_step tre0_ex1 gstk_total_contract 247"
value "multi_step tre0_ex1 gstk_total_contract 248"
value "multi_step tre0_ex1 gstk_total_contract 249"
value "multi_step tre0_ex1 gstk_total_contract 250"
value "multi_step tre0_ex1 gstk_total_contract 251"
value "multi_step tre0_ex1 gstk_total_contract 252"
value "multi_step tre0_ex1 gstk_total_contract 253"
value "multi_step tre0_ex1 gstk_total_contract 256"
value "multi_step tre0_ex1 gstk_total_contract 257"
value "multi_step tre0_ex1 gstk_total_contract 258"
value "multi_step tre0_ex1 gstk_total_contract 259"
value "multi_step tre0_ex1 gstk_total_contract 260"
value "multi_step tre0_ex1 gstk_total_contract 261"
value "multi_step tre0_ex1 gstk_total_contract 262"
value "multi_step tre0_ex1 gstk_total_contract 264"
value "multi_step tre0_ex1 gstk_total_contract 265"
value "multi_step tre0_ex1 gstk_total_contract 266"
value "multi_step tre0_ex1 gstk_total_contract 268"
value "multi_step tre0_ex1 gstk_total_contract 269"
value "multi_step tre0_ex1 gstk_total_contract 270"
*)

value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 0)
         (get_balance_offset
           0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c)"
value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 165)
         (get_balance_offset
           0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c)"
value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 166)
         (get_balance_offset
           0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c)"

value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 0) 
          (get_balance_offset 0x0)"
value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 245) 
          (get_balance_offset 0x0)"
value "get_val_from_storage (multi_step tre0_ex1 gstk_total_contract 246) 
          (get_balance_offset 0x0)"

value "get_balance_offset 0x0"
value "get_balance_offset 0xCA35b7d915458EF540aDe6068dFe2F44E8fa733c"

end
