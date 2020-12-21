(******
Map implemented using list
Copyright (C) 2020  Ximeng Li

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Library General Public
License as published by the Free Software Foundation; either
version 2 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Library General Public License for more details.
******)

theory "LMap" 

imports Main

begin

type_synonym 'a list_map = "(int \<times> 'a) list"

definition lm_get :: "'a list_map \<Rightarrow> int \<Rightarrow> 'a option" where 
  "lm_get lm i = (
    let res = filter (\<lambda>(i', a). i' = i) lm in 
    if res = [] then None else Some (snd (last res))
   )"

definition lm_dom :: "'a list_map \<Rightarrow> int set" where 
  "lm_dom = set \<circ> (map fst)"

lemma in_lm_dom_left: "x \<in> lm_dom mp1 \<Longrightarrow> x \<in> lm_dom (mp1 @ mp2)" 
  by (simp add: lm_dom_def)

lemma in_lm_dom_right: "x \<in> lm_dom mp2 \<Longrightarrow> x \<in> lm_dom (mp1 @ mp2)" 
  by (simp add: lm_dom_def)

lemma in_lm_dom_n_right: "\<lbrakk> x \<in> lm_dom (mp1 @ mp2); x \<notin> lm_dom mp2 \<rbrakk> \<Longrightarrow> x \<in> lm_dom mp1 " 
  by (simp add: lm_dom_def)

lemma lm_get_right0: "lm_get mp x = Some v \<Longrightarrow> lm_get (a # mp) x = Some v" 
  using lm_get_def by (smt filter.simps(2) last_ConsR list.distinct(1) option.distinct(1))

lemma lm_get_right: "lm_get mp2 x = Some v \<Longrightarrow> lm_get (mp1 @ mp2) x = Some v" 
  using lm_get_def by (smt Nil_is_append_conv filter_append last_appendR option.simps(3))

lemma lm_get_right_effectless0: "x \<notin> lm_dom mp \<Longrightarrow> lm_get (a # mp) x = lm_get [a] x"  
proof(induct mp)
  case Nil
  then show ?case by auto
next
  case (Cons a' mp)
  have "x \<noteq> fst a'" using Cons.prems by (simp add: lm_dom_def)
  hence "lm_get (a # a' # mp) x = lm_get (a # mp) x" 
    using lm_get_def by (smt filter.simps(2) prod.case_eq_if)
  then show ?case 
    by (metis Cons.hyps Cons.prems insert_iff list.map(2) list.set(2) lm_dom_def o_apply)
qed

lemma lm_get_right_effectless: "x \<notin> lm_dom mp2 \<Longrightarrow> lm_get (mp1 @ mp2) x = lm_get mp1 x" 
proof(induct mp2)
  case Nil
  then show ?case by auto
next
  case (Cons a' mp2')
  have "x \<noteq> fst a'" using Cons.prems by (simp add: lm_dom_def)
  hence "lm_get (mp1 @ a' # mp2') x = lm_get (mp1 @ mp2') x" 
    using lm_get_def by (smt filter.simps(2) filter_append prod.case_eq_if)
  then show ?case 
    by (metis Cons.hyps Cons.prems insert_iff list.map(2) list.set(2) lm_dom_def o_apply)
qed

lemma lm_get_in_dom: "x \<in> lm_dom mp \<Longrightarrow> \<exists>v. lm_get mp x = Some v"
proof(induct mp)
case Nil
then show ?case by (simp add: lm_dom_def)
next
  case (Cons a mp)
  thus ?case
  proof(cases "x \<in> lm_dom mp")
    case True
    hence "\<exists>v. lm_get mp x = Some v" by (simp add: Cons.hyps)
    then show ?thesis using lm_get_right0 by metis
  next
    case False
    hence "x = fst a" using Cons.prems by (simp add: lm_dom_def)
    moreover have "lm_get (a # mp) x = lm_get [a] x" 
      using lm_get_right_effectless0 False by blast 
    ultimately show ?thesis by (simp add: lm_get_def split_beta)
  qed
qed

lemma lm_get_some_in_dom: "lm_get mp x = Some v \<Longrightarrow> x \<in> lm_dom mp" 
proof(induct mp arbitrary: v)
  case Nil
  then show ?case by (simp add: lm_get_def)
next
  case (Cons a mp)
  then show ?case
  proof(cases "\<exists>v. lm_get (mp) x = Some v")
    case True
    then obtain v0 where "lm_get mp x = Some v0" by auto
    hence "x \<in> lm_dom mp" using Cons.hyps by auto
    then show ?thesis by (simp add: lm_dom_def)
  next
    case False
    hence "x \<notin> lm_dom mp" using False lm_get_in_dom by blast
    hence "lm_get [a] x = Some v" using lm_get_right_effectless0 by (metis Cons.prems)
    hence "x = fst a" using lm_get_def 
      by (smt filter.simps(1) filter.simps(2) option.distinct(1) prod.case_eq_if)    
    then show ?thesis by (simp add: lm_dom_def)
  qed
qed


end
