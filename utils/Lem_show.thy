(*** This file is part of Lem.  eth-isabelle project just uses it.  See lem-license. ***)

(* Yoichi Hirai has anually modified this file for Isabelle2016-1 *)

chapter {* Generated by Lem from show.lem. *}

theory "Lem_show" 

imports 
 	 Main
	 "Lem_string" 
	 "Lem_maybe" 
	 "Lem_num" 
	 "Lem_basic_classes" 

begin 



(*open import String Maybe Num Basic_classes*)

(*open import {hol} `lemTheory`*)

record 'a Show_class=

  show_method::" 'a \<Rightarrow> string "

(* 
definition instance_Show_Show_string_dict  :: "(string)Show_class "  where 
     " instance_Show_Show_string_dict = ((|

  show_method = (\<lambda> s. ([(Char (num_of_nat 34))]) @ (s @ ([(Char (num_of_nat 34))])))|) )"
 *)

definition instance_Show_Show_string_dict  :: "(string)Show_class "  where 
     " instance_Show_Show_string_dict = ((|

  show_method = (\<lambda> s. ([(char_of_nat 34)]) @ (s @ ([(char_of_nat 34)])))|) )"


(*val stringFromMaybe : forall 'a. ('a -> string) -> maybe 'a -> string*)
fun stringFromMaybe  :: "('a \<Rightarrow> string)\<Rightarrow> 'a option \<Rightarrow> string "  where 
     " stringFromMaybe showX (Some x) = ( (''Just ('') @ (showX x @ ('')'')))"
|" stringFromMaybe showX None = ( (''Nothing''))" 
declare stringFromMaybe.simps [simp del]


definition instance_Show_Show_Maybe_maybe_dict  :: " 'a Show_class \<Rightarrow>('a option)Show_class "  where 
     " instance_Show_Show_Maybe_maybe_dict dict_Show_Show_a = ((|

  show_method = (\<lambda> x_opt. stringFromMaybe 
  (show_method   dict_Show_Show_a) x_opt)|) )"


(*val stringFromListAux : forall 'a. ('a -> string) -> list 'a -> string*)
function (sequential,domintros)  stringFromListAux  :: "('a \<Rightarrow> string)\<Rightarrow> 'a list \<Rightarrow> string "  where 
     " stringFromListAux showX ([]) = ( (''''))"
|" stringFromListAux showX (x # xs') = (
      (case  xs' of
        [] => showX x
      | _ => showX x @ ((''; '') @ stringFromListAux showX xs')
      ))" 
by pat_completeness auto


(*val stringFromList : forall 'a. ('a -> string) -> list 'a -> string*)
definition stringFromList  :: "('a \<Rightarrow> string)\<Rightarrow> 'a list \<Rightarrow> string "  where 
     " stringFromList showX xs = (
  (''['') @ (stringFromListAux showX xs @ ('']'')))"


definition instance_Show_Show_list_dict  :: " 'a Show_class \<Rightarrow>('a list)Show_class "  where 
     " instance_Show_Show_list_dict dict_Show_Show_a = ((|

  show_method = (\<lambda> xs. stringFromList 
  (show_method   dict_Show_Show_a) xs)|) )"


(*val stringFromPair : forall 'a 'b. ('a -> string) -> ('b -> string) -> ('a * 'b) -> string*)
fun stringFromPair  :: "('a \<Rightarrow> string)\<Rightarrow>('b \<Rightarrow> string)\<Rightarrow> 'a*'b \<Rightarrow> string "  where 
     " stringFromPair showX showY (x,y) = (
  (''('') @ (showX x @ (('', '') @ (showY y @ ('')'')))))" 
declare stringFromPair.simps [simp del]


definition instance_Show_Show_tup2_dict  :: " 'a Show_class \<Rightarrow> 'b Show_class \<Rightarrow>('a*'b)Show_class "  where 
     " instance_Show_Show_tup2_dict dict_Show_Show_a dict_Show_Show_b = ((|

  show_method = (stringFromPair 
  (show_method   dict_Show_Show_a) (show_method   dict_Show_Show_b))|) )"


definition instance_Show_Show_bool_dict  :: "(bool)Show_class "  where 
     " instance_Show_Show_bool_dict = ((|

  show_method = (\<lambda> b. if b then (''true'') else (''false''))|) )"

end
