chapter {* Generated by Lem from lem/keccak.lem. *}

theory "KeccakAuxiliary" 

imports 
 	 Main
	 "/Users/lixm/Documents/lem/library/Lem_pervasives" 
	 "Word8" 
	 "Word256" 
	 "Word64" 
	 "Keccak" 

begin 


(****************************************************)
(*                                                  *)
(* Termination Proofs                               *)
(*                                                  *)
(****************************************************)

termination sha3_update by lexicographic_order


(****************************************************)
(*                                                  *)
(* Lemmata                                          *)
(*                                                  *)
(****************************************************)

lemma word_rsplit_def_lemma:
" ((\<forall> w. word_rsplit_aux (to_bl w) (( 8 :: nat)) = word_rsplit w)) "
(* Theorem: word_rsplit_def_lemma*)(* try *) by auto

lemma word_of_bytes_def_lemma:
" ((\<forall> lst.
   of_bl
     (list_fill_left False (( 256 :: nat)) (List.concat (List.map to_bl lst)))
     = Word.word_rcat lst)) "
(* Theorem: word_of_bytes_def_lemma*)(* try *) by auto



end