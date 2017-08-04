(* Victor B. F. Gomes, University of Cambridge
   Martin Kleppmann, University of Cambridge
   Dominic P. Mulligan, University of Cambridge
   Alastair R. Beresford, University of Cambridge
*)

section\<open>Observed-Remove Set\<close>
 
text\<open>The ORSet is a well-known CRDT for implementing replicated sets, supporting two operations:
     the \emph{insertion} and \emph{deletion} of an arbitrary element in the shared set.\<close>

theory
  ORSet1
imports
  Network
begin

datatype ('id, 'a) operation = Add "'id" "'a" | Rem "'id set" "'a" | Append "'id" "'a"

type_synonym ('id, 'a) state = "'a \<Rightarrow> ('id set \<times> 'id set)"

definition op_elem :: "('id, 'a) operation \<Rightarrow> 'a" where
  "op_elem oper \<equiv> case oper of Add i e \<Rightarrow> e | Rem is e \<Rightarrow> e | Append i e \<Rightarrow> e"

definition interpret_op :: "('id, 'a) operation \<Rightarrow> ('id, 'a) state \<rightharpoonup> ('id, 'a) state" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_op oper state \<equiv>
     let metadata = fst (state (op_elem oper));
				 files = snd (state (op_elem oper));
         after  = case oper of 
				   Add i e \<Rightarrow> (metadata \<union> {i}, files) |
					 Rem is e \<Rightarrow> (metadata - is, files - is) |
					 Append i e \<Rightarrow> (metadata, files \<union> {i})
     in  Some (state ((op_elem oper) := after))"
  
definition valid_behaviours :: "('id, 'a) state \<Rightarrow> 'id \<times> ('id, 'a) operation \<Rightarrow> bool" where
  "valid_behaviours state msg \<equiv>
     case msg of
       (i, Add j  e) \<Rightarrow> i = j |
       (i, Rem is e) \<Rightarrow> is = fst (state e) \<union> snd (state e) |
			 (i, Append j e) \<Rightarrow> i = j"

locale orset = network_with_constrained_ops _ interpret_op "\<lambda>x. ({},{})" valid_behaviours

lemma (in orset) add_add_commute:
  shows "\<langle>Add i1 e1\<rangle> \<rhd> \<langle>Add i2 e2\<rangle> = \<langle>Add i2 e2\<rangle> \<rhd> \<langle>Add i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) add_rem_commute:
  assumes "i \<notin> is"
  shows "\<langle>Add i e1\<rangle> \<rhd> \<langle>Rem is e2\<rangle> = \<langle>Rem is e2\<rangle> \<rhd> \<langle>Add i e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)
  	
lemma (in orset) add_append_commute:
  shows "\<langle>Add i1 e1\<rangle> \<rhd> \<langle>Append i2 e2\<rangle> = \<langle>Append i2 e2\<rangle> \<rhd> \<langle>Add i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)
  	
lemma (in orset) rem_rem_commute:
  shows "\<langle>Rem i1 e1\<rangle> \<rhd> \<langle>Rem i2 e2\<rangle> = \<langle>Rem i2 e2\<rangle> \<rhd> \<langle>Rem i1 e1\<rangle>"
  by(unfold interpret_op_def op_elem_def kleisli_def, fastforce)
  
lemma (in orset) rem_append_commute:
	assumes "i \<notin> is"
  shows "\<langle>Rem is e1\<rangle> \<rhd> \<langle>Append i e2\<rangle> = \<langle>Append i e2\<rangle> \<rhd> \<langle>Rem is e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)
  	
lemma (in orset) append_append_commute:
  shows "\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Append i2 e2\<rangle> = \<langle>Append i2 e2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) apply_operations_never_fails:
  assumes "xs prefix of i"
  shows "apply_operations xs \<noteq> None"
using assms proof(induction xs rule: rev_induct, clarsimp)
  case (snoc x xs) thus ?case
  proof (cases x)
    case (Broadcast e) thus ?thesis
      using snoc by force
  next
    case (Deliver e) thus ?thesis
      using snoc apply clarsimp unfolding interp_msg_def apply_operations_def
      by (metis (no_types, lifting) bind.bind_lunit interpret_op_def prefix_of_appendD)
  qed
qed

lemma (in orset) add_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Add i2 e) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Add i2 e)"
    using assms deliver_in_prefix_is_valid by blast
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed

definition (in orset) added_ids :: "('id \<times> ('id, 'b) operation) event list \<Rightarrow> 'b \<Rightarrow> 'id list" where
  "added_ids es p \<equiv> List.map_filter (\<lambda>x. case x of Deliver (i, Add j e) \<Rightarrow> if e = p then Some j else None | _ \<Rightarrow> None) es"
  
definition (in orset) added_files :: "('id \<times> ('id, 'b) operation) event list \<Rightarrow> 'b \<Rightarrow> 'id list" where
  "added_files es p \<equiv> List.map_filter (\<lambda>x. case x of Deliver (i, Append j e) \<Rightarrow> if e = p then Some j else None | _ \<Rightarrow> None) es"

  (*
lemma full_davai [simp]:
	shows "set (added_ids xs e) \<inter> set (added_files xs e) = {} "
		unfolding added_ids_def added_files_def map_filter_def  nitpick *)
  
-- {* added files simplifier *}

lemma (in orset) [simp]:
	shows "added_files [] e = []"
	by (auto simp: added_files_def map_filter_def)
		  	
lemma (in orset) [simp]:
  shows "added_files (xs @ ys) e = added_files xs e @ added_files ys e"
    by (auto simp: added_files_def map_filter_append)

lemma (in orset) added_files_Broadcast_collapse [simp]:
  shows "added_files ([Broadcast e]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)
    
lemma (in orset) added_files_Deliver_Rem_collapse [simp]:
  shows "added_files ([Deliver (i, Rem is e)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)
    
lemma (in orset) added_files_Deliver_Add_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_files ([Deliver (i, Append j e)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)
    
lemma (in orset) added_files_Deliver_Add_same_collapse [simp]:
  shows "added_files ([Deliver (i, Append j e)]) e = [j]"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in orset) added_files_not_in_set:
  assumes "i1 \<notin> set (added_files [Deliver (i, Append i2 e)] e)"
  shows "i1 \<noteq> i2"
  using assms by simp
  	
-- {* added ids simplifier *}
  
lemma (in orset) [simp]:
  shows "added_ids [] e = []"
  by (auto simp: added_ids_def map_filter_def)
  	
lemma (in orset) [simp]:
  shows "added_ids (xs @ ys) e = added_ids xs e @ added_ids ys e"
    by (auto simp: added_ids_def map_filter_append)

lemma (in orset) added_ids_Broadcast_collapse [simp]:
  shows "added_ids ([Broadcast e]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Rem_collapse [simp]:
  shows "added_ids ([Deliver (i, Rem is e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Add_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_ids ([Deliver (i, Add j e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Add_same_collapse [simp]:
  shows "added_ids ([Deliver (i, Add j e)]) e = [j]"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in orset) added_id_not_in_set:
  assumes "i1 \<notin> set (added_ids [Deliver (i, Add i2 e)] e)"
  shows "i1 \<noteq> i2"
  using assms by simp

lemma (in orset) apply_operations_added_ids:
  assumes "es prefix of j"
    and "apply_operations es = Some f"
  shows "fst (f x) \<subseteq> set (added_ids es x)"
using assms proof (induct es arbitrary: f rule: rev_induct, force)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case (Deliver e)
    moreover obtain a b where "e = (a, b)" by force
    ultimately show ?thesis
      using snoc by(case_tac b; clarsimp simp: interp_msg_def split: bind_splits,
                    force split: if_split_asm simp add: op_elem_def interpret_op_def)
  qed
qed
	
lemma (in orset) apply_operations_added_files:
  assumes "es prefix of j"
    and "apply_operations es = Some f"
  shows "snd (f x) \<subseteq> set (added_files es x)"
  using assms proof (induct es arbitrary: f rule: rev_induct, force)
  case (snoc x xs) 
  thus ?case
  proof (cases x, force)
    case (Deliver e)
    moreover obtain a b where "e = (a, b)" by force           
    ultimately show ?thesis
      using snoc by(case_tac b; clarsimp simp: interp_msg_def split: bind_splits,
                    force split: if_split_asm simp add: op_elem_def interpret_op_def) 
  qed
qed
	
	(*
lemma (in orset) ids_not_files:
  assumes "es prefix of j"
    and "apply_operations es = Some f"
  shows "set (added_ids es e) \<inter> set (added_files es e) = {}"
  using assms proof (induct es arbitrary: f rule: rev_induct, force)
  case (snoc x xs) 
  thus ?case
  proof (cases x, force)
    case (Deliver e')
    moreover obtain a b where "e' = (a, b)" by force                 
    ultimately show ?thesis by (metis inf_bot_right orset.added_ids_def orset.added_files_def orset_axioms set_empty)
      
  qed
qed *)

(*
lemma (in orset) metadata_not_files:
  assumes "es prefix of j"
    and "apply_operations es = Some f"
  shows "snd (f e) \<inter> set (added_files es e) = {}"
  using assms proof (induct es arbitrary: f rule: rev_induct, force)
  case (snoc x xs) 
  thus ?case
  proof (cases x, force)
    case (Deliver e')
    moreover obtain a b where "e' = (a, b)" by force           
    ultimately show ?thesis
      using snoc by(case_tac b; clarsimp simp: interp_msg_def split: bind_splits,
                    force split: if_split_asm simp add: op_elem_def interpret_op_def) 
  qed
qed *)
	

	
(*	
lemma (in orset) metadata_not_files2:
  assumes "es prefix of j"
    and "apply_operations es = Some f"
  shows "snd (f e) \<inter> fst (f e) = {}"
  using assms proof (induct es arbitrary: f rule: rev_induct, force)
  case (snoc x xs) 
  thus ?case
  proof (cases x, force)
    case A1: (Deliver e')
    moreover obtain a b where B2: "e' = (a, b)" by force           
    ultimately show ?thesis
      using snoc proof (cases b)
      case (Add x11 x12)
      have "\<exists> u . apply_operations xs = Some u" using A1 bind_eq_Some_conv snoc(3) by fastforce
    	then obtain r where  R: "apply_operations xs = Some r" by force
      hence A5: "snd (r x12) \<inter> fst (r x12) = {}" using snoc
      	apply (simp add: added_files_def empty_set inf_bot_right inf_commute le_iff_inf apply_operations_added_files prefix_of_appendD)
    	hence "interpret_op (Add x11 x12) r = Some f" using snoc A1 B2 R by (simp add: Add interp_msg_def)
    	then show ?thesis unfolding interpret_op_def op_elem_def apply (simp add: Add) using A5
    		by (metis added_files_def empty_set inf_bot_right inf_commute le_iff_inf apply_operations_added_files snoc(2) snoc(3))
    next
    	case (Rem x21 x22)
    	have "xs prefix of j" using snoc by auto
    	have "\<exists> u . apply_operations xs = Some u" using A1 bind_eq_Some_conv snoc(3) by fastforce
    	then obtain r where  R: "apply_operations xs = Some r" by force
    	hence A5: "snd (r e) \<inter> fst (r e) = {}" using snoc by auto
    	hence "interpret_op (Rem x21 x22) r = Some f" using snoc A1 B2 R by (simp add: Rem interp_msg_def)
    	then show ?thesis unfolding interpret_op_def using A5
    		by (smt Int_Diff fst_conv fun_upd_other fun_upd_same inf_bot_right inf_commute operation.simps(6) option.inject snd_conv)
    qed
  qed
qed 
*)
lemma (in orset) Deliver_added_ids:
  assumes "xs prefix of j"
    and "i \<in> set (added_ids xs e)"
  shows "Deliver (i, Add i e) \<in> set xs"
using assms proof (induct xs rule: rev_induct, clarsimp)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case (Deliver e')
    moreover obtain a b where "e' = (a, b)" by force
    ultimately show ?thesis
      using snoc apply (case_tac b; clarsimp)
       apply (metis added_ids_Deliver_Add_diff_collapse added_ids_Deliver_Add_same_collapse
              empty_iff list.set(1) set_ConsD add_id_valid in_set_conv_decomp prefix_of_appendD)
       apply force
      done  
  qed
qed

lemma (in orset) Broadcast_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (r, Rem ix e)] prefix of j"
    and "i \<in> ix"
  shows "Deliver (i, Add i e) \<in> set xs"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence A1: "ix = fst (y e) \<union> snd (y e)"
    using assms(1) broadcast_only_valid_msgs operation.case(2) option.simps(1)
      case_prodD apply simp unfolding valid_behaviours_def unfolding apply_operations_def
    using case_prodD by fastforce
  have "xs prefix of j" using assms by auto
  hence "fst (y e) \<subseteq> set (added_ids xs e)" using apply_operations_added_ids [of xs j y e] assms A1
  	using calculation by linarith
  hence "fst (y e) \<inter> snd (y e) = {}" using A1 metadata_not_files2 
  	using \<open>xs prefix of j\<close> calculation by blast  		
  ultimately show ?thesis
    using assms A1 Deliver_added_ids[of xs j "i" e] apply_operations_added_ids [of xs j y e] 
    by (metis (no_types, lifting) Int_subset_iff Un_iff \<open>xs prefix of j\<close> added_files_def empty_set metadata_not_files3 sup_absorb1)
qed

lemma (in orset) Broadcast_Deliver_prefix_closed2:
  assumes "xs prefix of j"
    and "Broadcast (r, Rem ix e) \<in> set xs"
    and "i \<in> ix"
  shows "Deliver (i, Add i e) \<in> set xs"
using assms Broadcast_Deliver_prefix_closed by (induction xs rule: rev_induct; force)

lemma (in orset) concurrent_add_remove_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Add i e) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Add i e) (ir, Rem is e)"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Add i e) \<in> set pre"
    using Broadcast_Deliver_prefix_closed assms(1) by auto
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed

lemma (in orset) Deliver_Add_same_id_same_message:
  assumes "Deliver (i, Add i e1) \<in> set (history j)" and "Deliver (i, Add i e2) \<in> set (history j)"
  shows "e1 = e2"
proof -
  obtain pre1 pre2 k1 k2 where *: "pre1@[Broadcast (i, Add i e1)] prefix of k1" "pre2@[Broadcast (i, Add i e2)] prefix of k2"
    using assms delivery_has_a_cause events_before_exist by meson
  moreover hence "Broadcast (i, Add i e1) \<in> set (history k1)" "Broadcast (i, Add i e2) \<in> set (history k2)"
    using node_histories.prefix_to_carriers node_histories_axioms by force+
  ultimately show ?thesis
    using msg_id_unique by fastforce
qed

lemma (in orset) ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Add i e2) \<in> set pre"
    using Broadcast_Deliver_prefix_closed assms(1) by blast
  moreover have "Deliver (i, Add i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms operation.inject(1)
        prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed

corollary (in orset) concurrent_add_remove_independent:
  assumes "\<not> hb (i, Add i e1) (ir, Rem is e2)" and "\<not> hb (ir, Rem is e2) (i, Add i e1)"
    and "xs prefix of j"
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms ids_imply_messages_same concurrent_add_remove_independent_technical by fastforce

lemma (in orset) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"                     
proof -
  { fix a b x y
    assume "(a, b) \<in> set (node_deliver_messages xs)"
           "(x, y) \<in> set (node_deliver_messages xs)"
           "hb.concurrent (a, b) (x, y)"
    hence "interp_msg (a, b) \<rhd> interp_msg (x, y) = interp_msg (x, y) \<rhd> interp_msg (a, b)"
      apply(unfold interp_msg_def, case_tac "b"; case_tac "y"; simp add: add_add_commute rem_rem_commute hb.concurrent_def)
       apply (metis add_id_valid add_rem_commute assms concurrent_add_remove_independent hb.concurrentD1 hb.concurrentD2 prefix_contains_msg)+
      done
  } thus ?thesis
    by(fastforce simp: hb.concurrent_ops_commute_def)
qed

theorem (in orset) convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
      and "xs prefix of i" and "ys prefix of j"
    shows "apply_operations xs = apply_operations ys"
using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext concurrent_operations_commute
                node_deliver_messages_distinct hb_consistent_prefix)
              
context orset begin

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "\<lambda>x.({},{})"
  apply(standard; clarsimp simp add: hb_consistent_prefix node_deliver_messages_distinct
        concurrent_operations_commute)
   apply(metis (no_types, lifting) apply_operations_def bind.bind_lunit not_None_eq
     hb.apply_operations_Snoc kleisli_def apply_operations_never_fails interp_msg_def)
  using drop_last_message apply blast
done

end
end

  