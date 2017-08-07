(* Victor B. F. Gomes, University of Cambridge
   Martin Kleppmann, University of Cambridge
   Dominic P. Mulligan, University of Cambridge
   Alastair R. Beresford, University of Cambridge
*)

section\<open>Observed-Remove Set\<close>
 
text\<open>The ORSet is a well-known CRDT for implementing replicated sets, supporting two operations:
     the \emph{insertion} and \emph{deletion} of an arbitrary element in the shared set.\<close>

theory
  ORSet3
imports
  Network
begin

datatype ('id, 'a) operation = Add "'id" "'a" | Rem "'id set" "'a" | Append "'id" "'a" | Expunge "'a" "'id" "'id" | Store "'a" "'id" "'id"

type_synonym ('id, 'a) state = "'a \<Rightarrow> ('id set \<times> 'id set)"

definition op_elem :: "('id, 'a) operation \<Rightarrow> 'a" where
  "op_elem oper \<equiv> case oper of Add i e \<Rightarrow> e | Rem is e \<Rightarrow> e | Append i e \<Rightarrow> e | Expunge e mo i \<Rightarrow> e | Store e mo i \<Rightarrow> e"

definition interpret_op :: "('id, 'a) operation \<Rightarrow> ('id, 'a) state \<rightharpoonup> ('id, 'a) state" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_op oper state \<equiv>
     let metadata = fst (state (op_elem oper));
				 files = snd (state (op_elem oper));
         after  = case oper of 
				   Add i e \<Rightarrow> (metadata \<union> {i}, files) |
					 Rem is e \<Rightarrow> (metadata - is, files - is) |
					 Append i e \<Rightarrow> (metadata, files \<union> {i}) |
				   Expunge e mo i \<Rightarrow> (metadata \<union> {i}, files - {mo}) |
					 Store e mo i \<Rightarrow> (metadata, insert i (files - {mo}))
     in  Some (state ((op_elem oper) := after))"
  
definition valid_behaviours :: "('id, 'a) state \<Rightarrow> 'id \<times> ('id, 'a) operation \<Rightarrow> bool" where
  "valid_behaviours state msg \<equiv>
     case msg of
       (i, Add j  e) \<Rightarrow> i = j |
       (i, Rem is e) \<Rightarrow> is = fst (state e) \<union> snd (state e) |
			 (i, Append j e) \<Rightarrow> i = j |
			 (i, Expunge e mo j) \<Rightarrow> i = j \<and> mo \<in> snd (state e) |
		   (i, Store e mo j) \<Rightarrow> i = j \<and> mo \<in> snd (state e)"

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
  	
lemma (in orset) add_expunge_commute:
  shows "\<langle>Add i1 e1\<rangle> \<rhd> \<langle>Expunge e2 mo i2\<rangle> = \<langle>Expunge e2 mo i2\<rangle> \<rhd> \<langle>Add i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)
  	
lemma (in orset) add_store_commute:
  shows "\<langle>Add i1 e1\<rangle> \<rhd> \<langle>Store e2 mo i2\<rangle> = \<langle>Store e2 mo i2\<rangle> \<rhd> \<langle>Add i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) rem_rem_commute:
  shows "\<langle>Rem i1 e1\<rangle> \<rhd> \<langle>Rem i2 e2\<rangle> = \<langle>Rem i2 e2\<rangle> \<rhd> \<langle>Rem i1 e1\<rangle>"
  by(unfold interpret_op_def op_elem_def kleisli_def, fastforce)
  
lemma (in orset) rem_append_commute:
	assumes "i \<notin> is"
  shows "\<langle>Rem is e1\<rangle> \<rhd> \<langle>Append i e2\<rangle> = \<langle>Append i e2\<rangle> \<rhd> \<langle>Rem is e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)
  	
lemma (in orset) rem_expunge_commute:
	assumes "i \<notin> is"
  shows "\<langle>Rem is e1\<rangle> \<rhd> \<langle>Expunge e2 mo i\<rangle> = \<langle>Expunge e2 mo i\<rangle> \<rhd> \<langle>Rem is e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)
  	
lemma (in orset) rem_store_commute:
	assumes "i \<notin> is"
  shows "\<langle>Rem is e1\<rangle> \<rhd> \<langle>Store e2 mo i\<rangle> = \<langle>Store e2 mo i\<rangle> \<rhd> \<langle>Rem is e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)
  	
lemma (in orset) append_append_commute:
  shows "\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Append i2 e2\<rangle> = \<langle>Append i2 e2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)
  	
lemma (in orset) append_expunge_commute:
  assumes "i1 \<noteq> mo"
  shows "(\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Expunge e2 mo i2\<rangle>) = (\<langle>Expunge e2 mo i2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>)"
proof
	fix x
	show "(\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Expunge e2 mo i2\<rangle>) x = (\<langle>Expunge e2 mo i2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>) x"
		using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def)
qed
	
lemma (in orset) append_store_commute:
  assumes "i1 \<noteq> mo"
  shows "(\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Store e2 mo i2\<rangle>) = (\<langle>Store e2 mo i2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>)"
proof
	fix x
	show "(\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Store e2 mo i2\<rangle>) x = (\<langle>Store e2 mo i2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>) x"
		using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def)
qed

lemma (in orset) expunge_expunge_commute:
  shows "(\<langle>Expunge e1 mo1 i1\<rangle> \<rhd> \<langle>Expunge e2 mo2 i2\<rangle>) = (\<langle>Expunge e2 mo2 i2\<rangle> \<rhd> \<langle>Expunge e1 mo1 i1\<rangle>)"
proof
	fix x
	show "(\<langle>Expunge e1 mo1 i1\<rangle> \<rhd> \<langle>Expunge e2 mo2 i2\<rangle>) x = (\<langle>Expunge e2 mo2 i2\<rangle> \<rhd> \<langle>Expunge e1 mo1 i1\<rangle>) x"
		by(auto simp add: interpret_op_def kleisli_def op_elem_def) qed
	
lemma  expunge_store_commute:
	assumes "i1 \<noteq> mo2" and "i2 \<noteq> mo1"
  shows "(\<langle>Expunge e1 mo1 i1\<rangle> \<rhd> \<langle>Store e2 mo2 i2\<rangle>) = (\<langle>Store e2 mo2 i2\<rangle> \<rhd> \<langle>Expunge e1 mo1 i1\<rangle>)"
proof
	fix x
	show "(\<langle>Expunge e1 mo1 i1\<rangle> \<rhd> \<langle>Store e2 mo2 i2\<rangle>) x = (\<langle>Store e2 mo2 i2\<rangle> \<rhd> \<langle>Expunge e1 mo1 i1\<rangle>) x"
		unfolding  interpret_op_def kleisli_def op_elem_def using assms(2) by (simp, fastforce)
qed
	
lemma (in orset) store_store_commute:
	assumes "i1 \<noteq> mo2" and "i2 \<noteq> mo1"
  shows "(\<langle>Store e1 mo1 i1\<rangle> \<rhd> \<langle>Store e2 mo2 i2\<rangle>) = (\<langle>Store e2 mo2 i2\<rangle> \<rhd> \<langle>Store e1 mo1 i1\<rangle>)"
proof
	fix x
	show "(\<langle>Store e1 mo1 i1\<rangle> \<rhd> \<langle>Store e2 mo2 i2\<rangle>) x = (\<langle>Store e2 mo2 i2\<rangle> \<rhd> \<langle>Store e1 mo1 i1\<rangle>) x"
		unfolding  interpret_op_def kleisli_def op_elem_def using assms by (simp, fastforce)
qed

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
	
lemma (in orset) append_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Append i2 e) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Append i2 e)"
    using assms deliver_in_prefix_is_valid by blast
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed
	
lemma (in orset) expunge_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Expunge e mo i2) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Expunge e mo i2)"
    using assms deliver_in_prefix_is_valid by blast
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed
	
lemma (in orset) store_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Store e mo i2) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Store e mo i2)"
    using assms deliver_in_prefix_is_valid by blast
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed

definition (in orset) added_ids :: "('id \<times> ('id, 'b) operation) event list \<Rightarrow> 'b \<Rightarrow> 'id list" where
  "added_ids es p \<equiv> List.map_filter (\<lambda>x. case x of 
		Deliver (i, Add j e) \<Rightarrow> if e = p then Some j else None | 
    Deliver (i, Expunge e mo j) \<Rightarrow> if e = p then Some j else None |
		_ \<Rightarrow> None) es"
	
definition (in orset) added_files :: "('id \<times> ('id, 'b) operation) event list \<Rightarrow> 'b \<Rightarrow> 'id list" where
    "added_files es p \<equiv> List.map_filter (\<lambda>x. case x of 
		Deliver (i, Append j e) \<Rightarrow> if e = p then Some j else None |
    Deliver (i, Store e mo j) \<Rightarrow> if e = p then Some j else None |
		_ \<Rightarrow> None) es"
		
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
    
lemma (in orset) added_files_Deliver_Add_collapse [simp]:
  shows "added_files ([Deliver (i, Add j e)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in orset) added_files_Deliver_Expunge_collapse [simp]:
  shows "added_files ([Deliver (i, Expunge e mo j)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)
    
lemma (in orset) added_files_Deliver_Append_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_files ([Deliver (i, Append j e)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)
    
lemma (in orset) added_files_Deliver_Append_same_collapse [simp]:
  shows "added_files ([Deliver (i, Append j e)]) e = [j]"
  by (auto simp: added_files_def map_filter_append map_filter_def)
  	
lemma (in orset) added_files_Deliver_Store_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_files ([Deliver (i, Store e mo j)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)
    
lemma (in orset) added_files_Deliver_Store_same_collapse [simp]:
  shows "added_files ([Deliver (i, Store e mo j)]) e = [j]"
  by (auto simp: added_files_def map_filter_append map_filter_def)
  	
 
-- {* added ids simplifier *}
  
lemma (in orset) [simp]:
  shows "added_ids [] e = []"
  by (auto simp: added_ids_def map_filter_def)
  	
lemma (in orset) split_ids [simp]:
  shows "added_ids (xs @ ys) e = added_ids xs e @ added_ids ys e"
    by (auto simp: added_ids_def map_filter_append)

lemma (in orset) added_ids_Broadcast_collapse [simp]:
  shows "added_ids ([Broadcast e]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Rem_collapse [simp]:
  shows "added_ids ([Deliver (i, Rem is e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Append_collapse [simp]:
  shows "added_ids ([Deliver (i, Append j e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
  	
lemma (in orset) added_ids_Deliver_Store_collapse [simp]:
  shows "added_ids ([Deliver (i, Store e mo j)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Add_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_ids ([Deliver (i, Add j e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
  	
lemma (in orset) added_ids_Deliver_Expunge_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_ids ([Deliver (i, Expunge e mo j)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
    
lemma (in orset) added_ids_Deliver_Add_same_collapse [simp]:
  shows "added_ids ([Deliver (i, Add j e)]) e = [j]"
  by (auto simp: added_ids_def map_filter_append map_filter_def)
  	
lemma (in orset) added_ids_Deliver_Expunge_same_collapse [simp]:
  shows "added_ids ([Deliver (i, Expunge e mo j)]) e = [j]"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

-- "probably unused"
lemma (in orset) expunge_id_not_in_set:
  assumes "i1 \<notin> set (added_ids [Deliver (i, Expunge e mo i2)] e)"
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
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case (Deliver e)
    moreover obtain a b where "e = (a, b)" by force
    ultimately show ?thesis
      using snoc by(case_tac b; clarsimp simp: interp_msg_def split: bind_splits,
                    force split: if_split_asm simp add: op_elem_def interpret_op_def)
  qed
qed

lemma (in orset) Deliver_added_files:
  assumes "xs prefix of j"
    and "i \<in> set (added_files xs e)"
  shows "Deliver (i, Append i e) \<in> set xs \<or> (\<exists> mo . Deliver (i, Store e mo i) \<in> set xs)"
using assms proof (induct xs rule: rev_induct, clarsimp)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case X: (Deliver e')
    moreover obtain a b where E: "e' = (a, b)" by force
    ultimately show ?thesis
      using snoc apply (case_tac b; clarify)
       apply (simp,metis prefix_of_appendD)
        apply force using  append_id_valid
        apply simp using E 
      apply (metis added_files_Deliver_Append_diff_collapse added_files_Deliver_Append_same_collapse empty_iff in_set_conv_decomp list.set(1) prefix_of_appendD set_ConsD)
      	apply simp using E apply_operations_added_files
      apply blast apply simp using E apply_operations_added_files 
      by (metis Un_iff added_files_Deliver_Store_diff_collapse added_files_Deliver_Store_same_collapse empty_iff empty_set list.set_intros(1) prefix_of_appendD set_ConsD set_append store_id_valid)
  qed
qed
  

lemma (in orset) Broadcast_Expunge_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (i, Expunge e mo i)] prefix of j"
  shows "Deliver (mo, Append mo e) \<in> set xs \<or> (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set xs)"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "mo \<in> snd (y e)"
    using broadcast_only_valid_msgs[of xs "(i, Expunge e mo i)" j] valid_behaviours_def[of y "(i, Expunge e mo i)"] using assms by auto
  ultimately show ?thesis
    using assms Deliver_added_files apply_operations_added_files by blast
qed
	
lemma (in orset) Broadcast_Store_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (i, Store e mo i)] prefix of j"
  shows "Deliver (mo, Append mo e) \<in> set xs \<or> (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set xs)"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "mo \<in> snd (y e)"
    using broadcast_only_valid_msgs[of xs "(i, Store e mo i)" j] valid_behaviours_def[of y "(i, Store e mo i)"] using assms by auto
  ultimately show ?thesis
    using assms Deliver_added_files apply_operations_added_files by blast
qed
            
lemma (in orset) Deliver_added_ids:
  assumes "xs prefix of j"
    and "i \<in> set (added_ids xs e)"
  shows "Deliver (i, Add i e) \<in> set xs \<or> (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set xs)"
using assms proof (induct xs rule: rev_induct, clarsimp)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case X: (Deliver e')
    moreover obtain a b where "e' = (a, b)" by force
    ultimately show ?thesis
      using snoc apply (case_tac b; clarify)
       apply (simp,metis added_ids_Deliver_Add_diff_collapse added_ids_Deliver_Add_same_collapse
              empty_iff list.set(1) set_ConsD add_id_valid in_set_conv_decomp prefix_of_appendD)
       apply force using  append_id_valid 
      	
       apply (simp, metis (no_types, lifting)  prefix_of_appendD)
      
      apply (simp)
       apply (metis Un_iff added_ids_Deliver_Expunge_diff_collapse added_ids_Deliver_Expunge_same_collapse empty_iff expunge_id_valid list.set(1) list.set_intros(1) prefix_of_appendD set_ConsD set_append)
        by (simp, blast)
  qed
qed

lemma (in orset) Broadcast_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (r, Rem ix e)] prefix of j"
    and "i \<in> ix"
  shows "Deliver (i, Add i e) \<in> set xs \<or> Deliver (i, Append i e) \<in> set xs \<or> (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set xs) \<or> (\<exists> mo . Deliver (i, Store e mo i) \<in> set xs)"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "ix = fst (y e) \<union> snd (y e)"
    by (metis (mono_tags, lifting) assms(1) broadcast_only_valid_msgs operation.case(2) option.simps(1)
     valid_behaviours_def case_prodD)
  ultimately show ?thesis
    using assms Deliver_added_ids apply_operations_added_ids
    by (metis Deliver_added_files Un_iff apply_operations_added_files le_iff_sup prefix_of_appendD)
qed
  
lemma (in orset) ids_are_unique:
    assumes "xs prefix of j"
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" 
    and "(l, Append l e2) \<in> set (node_deliver_messages xs)"
    and "(k, Expunge e3 mo k) \<in> set (node_deliver_messages xs)"
    and "(m, Store e4 mo2 m) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> l \<and> i \<noteq> k \<and> l \<noteq> k \<and> i \<noteq> m \<and> l \<noteq> m \<and> k \<noteq> m"
  	using assms delivery_has_a_cause events_before_exist prefix_msg_in_history
  	by (metis fst_conv msg_id_unique operation.distinct(15) operation.distinct(17) operation.distinct(19) operation.distinct(3) operation.distinct(5) operation.distinct(7) prod.inject) 
	
lemma (in orset) concurrent_add_remove_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Add i e) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Add i e) (ir, Rem is e)"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Add i e) \<in> set pre \<or> Deliver (i, Append i e) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto    	
  hence "Deliver (i, Add i e) \<in> set pre" using assms(2) assms(3) ids_are_unique
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD)
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed
	
lemma (in orset) concurrent_append_remove_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (ir, Rem is e)"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Add i e) \<in> set pre \<or> Deliver (i, Append i e) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto
    	
  hence "Deliver (i, Append i e) \<in> set pre" using assms(2) assms(3) ids_are_unique
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD)
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed
	
lemma (in orset) concurrent_append_expunge_independent_technical:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" and "(r, Expunge e mo r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (r, Expunge e mo r)"
proof -
  obtain pre k where "pre@[Broadcast (r, Expunge e mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (mo, Append mo e) \<in> set pre \<or> (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) by auto
    	
  hence "Deliver (i, Append i e) \<in> set pre" using assms(2) assms(3) ids_are_unique
  	using assms(1)
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD)
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed
	
lemma (in orset) concurrent_append_store_independent_technical:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" and "(r, Store e mo r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (r, Store e mo r)"
proof -
  obtain pre k where "pre@[Broadcast (r, Store e mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (mo, Append mo e) \<in> set pre \<or> (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1) by auto
    	
  hence "Deliver (i, Append i e) \<in> set pre" using assms(2) assms(3) ids_are_unique
  	using assms(1)
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD)
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed
  
lemma (in orset) concurrent_expunge_remove_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Expunge e mo i) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Expunge e mo i) (ir, Rem is e)"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Add i e) \<in> set pre \<or> Deliver (i, Append i e) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto
    	
  hence "Deliver (i, Expunge e mo i) \<in> set pre" using assms(2) assms(3) ids_are_unique
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD)
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed
	
lemma (in orset) concurrent_store_remove_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Store e mo i) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Store e mo i) (ir, Rem is e)"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Add i e) \<in> set pre \<or> Deliver (i, Append i e) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto
    	
  hence "Deliver (i, Store e mo i) \<in> set pre" using assms(2) assms(3) ids_are_unique
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD)
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed
	
lemma (in orset) concurrent_store_expunge_independent_technical:
    assumes "xs prefix of j"
    and "(i, Store e mo i) \<in> set (node_deliver_messages xs)" and "(r, Expunge e i r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Store e mo i) (r, Expunge e i r)"
proof -
  obtain pre k where "pre@[Broadcast (r, Expunge e i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Append i e) \<in> set pre \<or> (\<exists> mo2 . Deliver (i, Store e mo2 i) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) by auto
    	
  hence "Deliver (i, Store e mo i) \<in> set pre" using assms(2) assms(3) ids_are_unique
  	by (smt assms(1) calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms node_histories.prefix_of_appendD node_histories_axioms prefix_elem_to_carriers prefix_msg_in_history)
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed
  
lemma (in orset) expunge_rem_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Expunge e1 mo i) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  
   moreover hence "Deliver (i, Add i e2) \<in> set pre \<or> Deliver (i, Append i e2) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e2 mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e2 mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1)
    by (meson orset.Broadcast_Deliver_prefix_closed orset_axioms)
    	
  hence "Deliver (i, Expunge e2 mo i) \<in> set pre" using assms(2) assms(3) assms(1) ids_are_unique 
  	by (smt added_files_Deliver_Append_same_collapse added_files_Deliver_Expunge_collapse added_files_Deliver_Store_same_collapse calculation delivery_has_a_cause empty_iff fst_conv list.set(1) list.set_intros(1) msg_id_unique node_histories.prefix_of_appendD node_histories_axioms operation.simps(10) operation.simps(4) prefix_elem_to_carriers prefix_msg_in_history prod.inject)
  	moreover have "Deliver(i, Expunge e1 mo i) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
    by (metis (no_types, lifting) delivery_has_a_cause fst_conv network.msg_id_unique network_axioms operation.inject(4) prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed
	
lemma (in orset) store_rem_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  
   moreover hence "Deliver (i, Add i e2) \<in> set pre \<or> Deliver (i, Append i e2) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e2 mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e2 mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1)
    by (meson orset.Broadcast_Deliver_prefix_closed orset_axioms)
    	
  hence "Deliver (i, Store e2 mo i) \<in> set pre" using assms(2) assms(3) assms(1) ids_are_unique
  	by (smt added_files_Deliver_Store_diff_collapse added_files_Deliver_Store_same_collapse added_ids_Deliver_Expunge_same_collapse calculation empty_iff empty_set expunge_id_not_in_set fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.distinct(17) operation.distinct(19) operation.distinct(7) prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD prod.sel(2))
  	moreover have "Deliver(i, Store e1 mo i) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
  	by (smt delivery_has_a_cause fst_conv network.msg_id_unique network_axioms operation.inject(5) prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed

lemma (in orset) add_rem_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Add i e2) \<in> set pre \<or> Deliver (i, Append i e2) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e2 mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e2 mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) ids_are_unique by blast
  hence "Deliver (i, Add i e2) \<in> set pre" using assms(1) assms(2) assms(3) ids_are_unique 
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.distinct(3) operation.distinct(5) operation.distinct(7) prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD prod.inject)
  moreover have "Deliver (i, Add i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms operation.inject(1)
        prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed
	
lemma (in orset) append_rem_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  
   moreover hence "Deliver (i, Add i e2) \<in> set pre \<or> Deliver (i, Append i e2) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e2 mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e2 mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1)
    by (meson orset.Broadcast_Deliver_prefix_closed orset_axioms)
    	
  hence "Deliver (i, Append i e2) \<in> set pre" using assms(2) assms(3) assms(1) ids_are_unique
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.distinct(15) operation.distinct(17) operation.distinct(3) prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD prod.inject)
      
      
  	moreover have "Deliver (i, Append i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
    by (metis (no_types, lifting) fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.inject(3) prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed

lemma (in orset) append_expunge_ids_imply_messages_same:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" and "(r, Expunge e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (r, Expunge e2 mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  
   moreover hence "Deliver (mo, Append mo e2) \<in> set pre \<or> (\<exists> mo2 . Deliver (mo, Store e2 mo2 mo) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1)
    by (meson orset.Broadcast_Deliver_prefix_closed orset_axioms)
    	
  hence "Deliver (i, Append i e2) \<in> set pre" using assms(2) assms(3) assms(1) ids_are_unique 
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.distinct(17) prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD prod.inject)      
      
  	moreover have "Deliver (i, Append i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
    by (metis (no_types, lifting) fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.inject(3) prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed
	
lemma (in orset) append_store_ids_imply_messages_same:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" and "(r, Store e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (r, Store e2 mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  
   moreover hence "Deliver (mo, Append mo e2) \<in> set pre \<or> (\<exists> mo2 . Deliver (mo, Store e2 mo2 mo) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1)
    by (meson orset.Broadcast_Deliver_prefix_closed orset_axioms)
    	
  hence "Deliver (i, Append i e2) \<in> set pre" using assms(2) assms(3) assms(1) ids_are_unique 
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.distinct(17) prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD prod.inject)      
      
  	moreover have "Deliver (i, Append i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
    by (metis (no_types, lifting) fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.inject(3) prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed
	
lemma (in orset) expunge_store_ids_imply_messages_same:
    assumes "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" and "(r, Expunge e2 i r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (r, Expunge e2 i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  
   moreover hence "Deliver (i, Append i e2) \<in> set pre \<or> (\<exists> mo2 . Deliver (i, Store e2 mo2 i) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) by blast
    	
  hence "Deliver (i, Store e1 mo i) \<in> set pre" using assms(2) assms(3) assms(1) ids_are_unique 
  	by (smt calculation fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms operation.distinct(17) prefix_elem_to_carriers prefix_msg_in_history prefix_of_appendD prod.inject)      
      
  	moreover have "Deliver (i, Store e1 mo i) \<in> set (history j)"
    using assms(1) assms(2) prefix_msg_in_history by auto
  ultimately show ?thesis 
  	by (smt Broadcast_Expunge_Deliver_prefix_closed fst_conv network.delivery_has_a_cause network.msg_id_unique network_axioms node_histories.prefix_of_appendD node_histories_axioms operation.distinct(17) operation.inject(5) prefix_elem_to_carriers prod.inject)
qed
	
corollary (in orset) concurrent_add_remove_independent:
  assumes "\<not> hb (i, Add i e1) (ir, Rem is e2)" and "\<not> hb (ir, Rem is e2) (i, Add i e1)"
    and "xs prefix of j"
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms add_rem_ids_imply_messages_same concurrent_add_remove_independent_technical by fastforce
  	
corollary (in orset) concurrent_append_remove_independent:
  assumes "\<not> hb (i, Append i e1) (ir, Rem is e2)" and "\<not> hb (ir, Rem is e2) (i, Append i e1)"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms append_rem_ids_imply_messages_same concurrent_append_remove_independent_technical by fastforce
  	
corollary (in orset) concurrent_append_expunge_independent:
  assumes "\<not> hb (i, Append i e1) (r, Expunge e2 mo r)" and "\<not> hb (r, Expunge e2 mo r) (i, Append i e1)"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" and "(r, Expunge e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> mo"
  using assms append_expunge_ids_imply_messages_same concurrent_append_expunge_independent_technical by fastforce
  	
corollary (in orset) concurrent_append_store_independent:
  assumes "\<not> hb (i, Append i e1) (r, Store e2 mo r)" and "\<not> hb (r, Store e2 mo r) (i, Append i e1)"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" and "(r, Store e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> mo"
  using assms append_store_ids_imply_messages_same concurrent_append_store_independent_technical by fastforce
    
corollary (in orset) concurrent_expunge_remove_independent:
  assumes "\<not> hb (i, Expunge e1 mo i) (ir, Rem is e2)" and "\<not> hb (ir, Rem is e2) (i, Expunge e1 mo i)"
    and "xs prefix of j"
    and "(i, Expunge e1 mo i) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms expunge_rem_ids_imply_messages_same concurrent_expunge_remove_independent_technical by fastforce
  	
corollary (in orset) concurrent_store_remove_independent:
  assumes "\<not> hb (i, Store e1 mo i) (ir, Rem is e2)" and "\<not> hb (ir, Rem is e2) (i, Store e1 mo i)"
    and "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms store_rem_ids_imply_messages_same concurrent_store_remove_independent_technical by fastforce
  	
corollary (in orset) concurrent_store_expunge_independent:
  assumes "\<not> hb (i, Store e1 mo i) (r, Expunge e2 mo2 r)" and "\<not> hb (r, Expunge e2 mo2 r) (i, Store e1 mo i)"
    and "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" and "(r, Expunge e2 mo2 r) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> mo2 \<and> r \<noteq> mo"
  using assms expunge_store_ids_imply_messages_same concurrent_store_expunge_independent_technical
  
  by (smt Pair_inject delivery_has_a_cause events_before_exist fst_conv msg_id_unique node_histories.prefix_of_appendD node_histories_axioms operation.distinct(15) operation.simps(25) orset.Broadcast_Store_Deliver_prefix_closed orset_axioms prefix_elem_to_carriers prefix_msg_in_history)
  	
lemma (in orset) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"                     
proof -
  { fix a b x y
    assume "(a, b) \<in> set (node_deliver_messages xs)"
           "(x, y) \<in> set (node_deliver_messages xs)"
           "hb.concurrent (a, b) (x, y)"
    hence "interp_msg (a, b) \<rhd> interp_msg (x, y) = interp_msg (x, y) \<rhd> interp_msg (a, b)" 
      apply(unfold interp_msg_def, case_tac "b"; case_tac "y"; simp add: add_add_commute rem_rem_commute append_append_commute add_append_commute add_expunge_commute add_store_commute expunge_expunge_commute hb.concurrent_def)
      								apply (metis (full_types) add_id_valid add_rem_commute assms concurrent_add_remove_independent prefix_contains_msg)+
      	
            apply (metis append_id_valid append_rem_ids_imply_messages_same assms concurrent_append_remove_independent_technical prefix_contains_msg rem_append_commute)
        
            		 apply (metis assms concurrent_expunge_remove_independent expunge_id_valid network.prefix_contains_msg network_axioms orset.rem_expunge_commute orset_axioms)
        
        apply (metis assms concurrent_store_remove_independent prefix_contains_msg rem_store_commute store_id_valid)
        
          apply (metis append_id_valid append_rem_ids_imply_messages_same assms concurrent_append_remove_independent_technical prefix_contains_msg rem_append_commute)
          apply (metis append_id_valid expunge_id_valid append_expunge_ids_imply_messages_same assms concurrent_append_expunge_independent_technical prefix_contains_msg append_expunge_commute)
        
          	 apply (metis append_id_valid append_store_commute assms concurrent_append_store_independent prefix_contains_msg store_id_valid)
        
          	apply (metis assms concurrent_expunge_remove_independent expunge_id_valid prefix_contains_msg rem_expunge_commute)
           apply (metis append_expunge_commute append_id_valid assms concurrent_append_expunge_independent expunge_id_valid prefix_contains_msg)
        
          
          apply (metis assms expunge_id_valid expunge_store_commute orset.concurrent_store_expunge_independent orset_axioms prefix_contains_msg store_id_valid)
        
         apply (metis assms concurrent_store_remove_independent prefix_contains_msg rem_store_commute store_id_valid)
  
        apply (metis append_id_valid append_store_commute assms orset.concurrent_append_store_independent orset_axioms prefix_contains_msg store_id_valid)
        
       apply (metis assms expunge_id_valid expunge_store_commute orset.concurrent_store_expunge_independent orset_axioms prefix_contains_msg store_id_valid)
        
        by (smt assms events_in_local_order network.delivery_has_a_cause network.hb.intros(2) network.msg_id_unique network_axioms node_histories.events_before_exist node_histories.prefix_elem_to_carriers node_histories_axioms orset.Broadcast_Store_Deliver_prefix_closed orset_axioms prefix_contains_msg prefix_of_appendD prod.sel(1) store_id_valid store_store_commute)
              
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

  