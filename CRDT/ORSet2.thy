(* Victor B. F. Gomes, University of Cambridge
   Martin Kleppmann, University of Cambridge
   Dominic P. Mulligan, University of Cambridge
   Alastair R. Beresford, University of Cambridge
*)

section\<open>Observed-Remove Set\<close>
 
text\<open>The ORSet is a well-known CRDT for implementing replicated sets, supporting two operations:
     the \emph{insertion} and \emph{deletion} of an arbitrary element in the shared set.\<close>

theory
  ORSet2
imports
  Network
begin

datatype ('id, 'a, 'b) operation = Add "'id" "'a" | Rem "'id set" "'a" "'b set" | Append "'a" "'b" |
	Store "'a" "'b" "'b"

type_synonym ('id, 'a, 'b) state = "('a \<Rightarrow> 'id set) \<times> ('a \<rightharpoonup> 'b set)"

definition op_elem :: "('id, 'a, 'b) operation \<Rightarrow> 'a" where
  "op_elem oper \<equiv> case oper of Add i e \<Rightarrow> e | Rem is e m \<Rightarrow> e | Append e m \<Rightarrow> e | Store e mo mn \<Rightarrow> e"
		
definition interpret_op :: "('id, 'a, 'b) operation \<Rightarrow> ('id, 'a, 'b) state \<rightharpoonup> ('id, 'a, 'b) state" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_op oper state \<equiv>
     let before = ((fst state) (op_elem oper));
         after  = case oper of Add i e \<Rightarrow> before \<union> {i} | Rem is e m \<Rightarrow> before - is | Append e m \<Rightarrow> before | Store e mo mn \<Rightarrow> before;
         filesystem = case oper of 
           Add i e \<Rightarrow> (case snd state e of None \<Rightarrow> Some {} | Some f \<Rightarrow> Some f) | 
           Rem is e m \<Rightarrow> (case snd state e of None \<Rightarrow> None | Some f \<Rightarrow> Some (f - m)) |
					 Append e m \<Rightarrow> (case snd state e of None \<Rightarrow> None | Some f \<Rightarrow> Some (insert m f)) |
					 Store e mo mn \<Rightarrow> (case snd state e of None \<Rightarrow> None | Some f \<Rightarrow> Some (insert mn (f - {mo})))
     in  Some ((fst state) ((op_elem oper) := after), (snd state) ((op_elem oper) := filesystem))"
  
definition valid_behaviours :: "('id, 'a, 'b) state \<Rightarrow> 'id \<times> ('id, 'a, 'b) operation \<Rightarrow> bool" where
  "valid_behaviours state msg \<equiv>
     case msg of
       (i, Add j e) \<Rightarrow> i = j|
       (i, Rem is e m) \<Rightarrow> is = fst state e"

locale orset = network_with_constrained_ops _ interpret_op "(\<lambda>x. {}, \<lambda>y. None)" valid_behaviours

lemma (in orset) add_add_commute:
  shows "\<langle>Add i1 e1\<rangle> \<rhd> \<langle>Add i2 e2\<rangle> = \<langle>Add i2 e2\<rangle> \<rhd> \<langle>Add i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in orset) add_rem_commute2:
  fixes s
  assumes "i \<notin> is"  and "e1 \<noteq> e2"
  shows " (\<langle>Add i e1\<rangle> \<rhd> \<langle>Rem is e2 m\<rangle>) s = (\<langle>Rem is e2 m\<rangle> \<rhd> \<langle>Add i e1\<rangle>) s"
  	unfolding interpret_op_def op_elem_def kleisli_def using assms apply simp
  	by (smt fun_upd_other fun_upd_twist snd_conv)
 
lemma (in orset) add_rem_commute3:
  fixes s
  assumes "i \<notin> is"
  shows " (\<langle>Add i e\<rangle> \<rhd> \<langle>Rem is e m\<rangle>) s = (\<langle>Rem is e m\<rangle> \<rhd> \<langle>Add i e\<rangle>) s"
  	unfolding interpret_op_def op_elem_def kleisli_def using assms apply simp
  	by (simp add: insert_Diff_if option.case_eq_if)
  	
lemma (in orset) add_rem_commute:
  assumes "i \<notin> is" 
  shows "\<langle>Add i e1\<rangle> \<rhd> \<langle>Rem is e2 m\<rangle> = \<langle>Rem is e2 m\<rangle> \<rhd> \<langle>Add i e1\<rangle>"
proof 
	fix x
	show "(\<langle>Add i e1\<rangle> \<rhd> \<langle>Rem is e2 m\<rangle>) x = (\<langle>Rem is e2 m\<rangle> \<rhd> \<langle>Add i e1\<rangle>) x "
		using assms add_rem_commute3[of "i" "is" "e1" "m" x] add_rem_commute2 [of "i" "is" "e1" "e2" "m" "x"]
		by auto
qed
  	
lemma rem_rem_commute1:
assumes "e1 \<noteq> e2"
shows " (\<langle>Rem i1 e1 m1\<rangle> \<rhd> \<langle>Rem i2 e2 m2\<rangle>) s = (\<langle>Rem i2 e2 m2\<rangle> \<rhd> \<langle>Rem i1 e1 m1\<rangle>) s"
unfolding interpret_op_def kleisli_def op_elem_def using assms by (simp add: fun_upd_twist)
  	
lemma rem_rem_commute2:
assumes "(snd s) e1 = None"
shows " (\<langle>Rem i1 e1 m1\<rangle> \<rhd> \<langle>Rem i2 e1 m2\<rangle>) s = (\<langle>Rem i2 e1 m2\<rangle> \<rhd> \<langle>Rem i1 e1 m1\<rangle>) s"
unfolding interpret_op_def kleisli_def op_elem_def using assms apply simp by fastforce
    	
lemma rem_rem_commute3:
assumes "(snd s) e1 \<noteq> None"
shows " (\<langle>Rem i1 e1 m1\<rangle> \<rhd> \<langle>Rem i2 e1 m2\<rangle>) s = (\<langle>Rem i2 e1 m2\<rangle> \<rhd> \<langle>Rem i1 e1 m1\<rangle>) s"
unfolding interpret_op_def kleisli_def op_elem_def apply simp 
proof
	show "(fst s)(e1 := fst s e1 - i1 - i2) = (fst s)(e1 := fst s e1 - i2 - i1)" by fastforce
	show "(snd s)(e1 := case case snd s e1 of None \<Rightarrow> None | Some f \<Rightarrow> Some (f - m1) of None \<Rightarrow> None | Some f \<Rightarrow> Some (f - m2)) = (snd s)
		(e1 := case case snd s e1 of None \<Rightarrow> None | Some f \<Rightarrow> Some (f - m2) of None \<Rightarrow> None | Some f \<Rightarrow> Some (f - m1))" 
		using assms apply simp by auto 
qed
	
lemma rem_rem_commute:
shows " \<langle>Rem i1 e1 m1\<rangle> \<rhd> \<langle>Rem i2 e2 m2\<rangle> = \<langle>Rem i2 e2 m2\<rangle> \<rhd> \<langle>Rem i1 e1 m1\<rangle>"
proof
	fix x
	show "(\<langle>Rem i1 e1 m1\<rangle> \<rhd> \<langle>Rem i2 e2 m2\<rangle>) x = (\<langle>Rem i2 e2 m2\<rangle> \<rhd> \<langle>Rem i1 e1 m1\<rangle>) x"
		using rem_rem_commute1[of e1 e2 i1 m1 i2 m2 x] 
				  rem_rem_commute2[of x e1 i1 m1 i2 m2] 
          rem_rem_commute3[of x e1 i1 m1 i2 m2]
    by auto
qed 

lemma append_append_commute:
shows " \<langle>Append e1 m1\<rangle> \<rhd> \<langle>Append e2 m2\<rangle> = \<langle>Append e2 m2\<rangle> \<rhd> \<langle>Append e1 m1\<rangle>"
proof
	fix x
	show "(\<langle>Append e1 m1\<rangle> \<rhd> \<langle>Append e2 m2\<rangle>) x = (\<langle>Append e2 m2\<rangle> \<rhd> \<langle>Append e1 m1\<rangle>) x"
		unfolding interpret_op_def kleisli_def op_elem_def apply simp
		by (simp add: fun_upd_twist insert_commute option.case_eq_if)
qed  

lemma add_append_commute:
	assumes "(snd x) e2 \<noteq> None"
	shows " (\<langle>Add i e1\<rangle> \<rhd> \<langle>Append e2 m2\<rangle>) x = (\<langle>Append e2 m2\<rangle> \<rhd> \<langle>Add i e1\<rangle>) x"
		unfolding interpret_op_def kleisli_def op_elem_def apply simp
		by (simp add: assms fun_upd_twist option.case_eq_if)
			
lemma rem_append_commute:
	assumes  "m2 \<notin> m1"
	shows " (\<langle>Rem is e1 m1\<rangle> \<rhd> \<langle>Append e2 m2\<rangle>) x = (\<langle>Append e2 m2\<rangle> \<rhd> \<langle>Rem is e1 m1\<rangle>) x"
		unfolding interpret_op_def kleisli_def op_elem_def apply simp using assms
		by (simp add: assms(1) fun_upd_twist insert_Diff_if option.case_eq_if)
			
lemma store_store_commute:
	assumes "mn1 \<noteq> mo1" and "mn1 \<noteq> mo2" and "mn2 \<noteq> mo1" and "mn2 \<noteq> mo2"
shows " (\<langle>Store e1 mo1 mn1\<rangle> \<rhd> \<langle>Store e2 mo2 mn2\<rangle>) x = (\<langle>Store e2 mo2 mn2\<rangle> \<rhd> \<langle>Store e1 mo1 mn1\<rangle>) x"
	unfolding interpret_op_def kleisli_def op_elem_def apply (case_tac "e1=e2") apply simp apply auto using assms
	by (smt Diff_insert insert_Diff_if insert_commute option.case_eq_if option.discI option.sel singletonD)
		
lemma store_add_commute:
	assumes  "(snd x) e2 \<noteq> None"
shows " (\<langle>Add i e1\<rangle> \<rhd> \<langle>Store e2 mo2 mn2\<rangle>) x = (\<langle>Store e2 mo2 mn2\<rangle> \<rhd> \<langle>Add i e1\<rangle>) x"
	unfolding interpret_op_def kleisli_def op_elem_def apply (case_tac "e1=e2") apply simp apply auto
	by (simp add: assms option.case_eq_if)

lemma store_rem_commute:
	assumes "mn2 \<notin> m"
shows " (\<langle>Rem is e1 m\<rangle> \<rhd> \<langle>Store e2 mo2 mn2\<rangle>) x = (\<langle>Store e2 mo2 mn2\<rangle> \<rhd> \<langle>Rem is e1 m\<rangle>) x"
	unfolding interpret_op_def kleisli_def op_elem_def apply (case_tac "e1=e2") apply simp apply auto
	using assms by (smt Diff_insert Diff_insert2 insert_Diff_if option.case_eq_if option.simps(5))
		
lemma store_append_commute:
	assumes "m \<noteq> mo2"
shows " (\<langle>Append e1 m\<rangle> \<rhd> \<langle>Store e2 mo2 mn2\<rangle>) x = (\<langle>Store e2 mo2 mn2\<rangle> \<rhd> \<langle>Append e1 m\<rangle>) x"
	unfolding interpret_op_def kleisli_def op_elem_def apply (case_tac "e1=e2") apply simp apply auto
	by (simp add: assms insert_Diff_if insert_commute option.case_eq_if)
		

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
      using snoc by (simp, metis (no_types, lifting) bind.simps(2) interp_msg_def interpret_op_def prefix_of_appendD)
  qed
qed

lemma (in orset) add_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Add i2 e) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Add i2 e)"
    using assms deliver_in_prefix_is_valid unfolding valid_behaviours_def by fastforce
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed

definition (in orset) added_ids :: "('id \<times> ('id, 'b, 'c) operation) event list \<Rightarrow> 'b \<Rightarrow> 'id list" where
  "added_ids es p \<equiv> List.map_filter (\<lambda>x. case x of Deliver (i, Add j e) \<Rightarrow> if e = p then Some j else None | _ \<Rightarrow> None) es"

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
  shows "added_ids ([Deliver (i, Rem is e m)]) e' = []"
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
  shows "fst f x \<subseteq> set (added_ids es x)"
using assms proof (induct es arbitrary: f rule: rev_induct, force)
  case (snoc x xs) thus ?case
  proof (cases x)
    case (Broadcast e)
    moreover obtain a b where "e = (a, b)" by force
    ultimately show ?thesis using snoc by (simp, blast)
  next
    case (Deliver e)
    moreover obtain a b where "e = (a, b)" by force
    ultimately show ?thesis
      using snoc by(case_tac b; clarsimp simp: interp_msg_def split: bind_splits,
                    force split: if_split_asm simp add: op_elem_def interpret_op_def)
  qed
qed
    
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
        sorry
       (*done *) 
  qed
qed

lemma (in orset) Broadcast_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (r, Rem ix e m)] prefix of j"
    and "i \<in> ix"
  shows "Deliver (i, Add i e) \<in> set xs"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "ix = fst y e"
    by (metis (mono_tags, lifting) assms(1) broadcast_only_valid_msgs operation.case(2) option.simps(1)
     valid_behaviours_def case_prodD)
  ultimately show ?thesis
    using assms Deliver_added_ids apply_operations_added_ids by blast
qed

lemma (in orset) Broadcast_Deliver_prefix_closed2:
  assumes "xs prefix of j"
    and "Broadcast (r, Rem ix e m) \<in> set xs"
    and "i \<in> ix"
  shows "Deliver (i, Add i e) \<in> set xs"
using assms Broadcast_Deliver_prefix_closed by (induction xs rule: rev_induct; force)

lemma (in orset) concurrent_add_remove_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Add i e) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e m) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Add i e) (ir, Rem is e m)"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e m)] prefix of k"
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
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2 m) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (ir, Rem is e2 m)] prefix of k"
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
  assumes "\<not> hb (i, Add i e1) (ir, Rem is e2 m)" and "\<not> hb (ir, Rem is e2 m) (i, Add i e1)"
    and "xs prefix of j"
    and "(i, Add i e1) \<in> set (node_deliver_messages xs)" and "(ir, Rem is e2 m) \<in> set (node_deliver_messages xs)"
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
       apply (metis add_id_valid add_rem_commute assms concurrent_add_remove_independent prefix_contains_msg)+
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
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "(\<lambda>x.{}, \<lambda> x. None)"
  apply(standard; clarsimp simp add: hb_consistent_prefix node_deliver_messages_distinct
        concurrent_operations_commute)
  unfolding hb.apply_operations_def node_deliver_messages_def interp_msg_def apply simp
    apply (meson interpret_op_def)
    by (metis drop_last_message trivial_network.node_deliver_messages_def)
end
end

  