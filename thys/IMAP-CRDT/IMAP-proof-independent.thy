section {* Independence of IMAP Commands *}

text\<open>In this section we show that two concurrent operations that reference to the same tag must be 
identical.\<close>

theory
  "IMAP-proof-independent"
  imports
    "IMAP-def"
    "IMAP-proof-helpers"  
begin

lemma (in imap) Broadcast_Expunge_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (i, Expunge e mo i)] prefix of j"
  shows "Deliver (mo, Append mo e) \<in> set xs \<or> 
    (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set xs)"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "mo \<in> snd (y e)"
    using broadcast_only_valid_msgs[of xs "(i, Expunge e mo i)" j] 
      valid_behaviours_def[of y "(i, Expunge e mo i)"] assms by auto
  ultimately show ?thesis
    using assms Deliver_added_files apply_operations_added_files by blast
qed

lemma (in imap) Broadcast_Store_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (i, Store e mo i)] prefix of j"
  shows "Deliver (mo, Append mo e) \<in> set xs \<or> 
    (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set xs)"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "mo \<in> snd (y e)"
    using broadcast_only_valid_msgs[of xs "(i, Store e mo i)" j] 
      valid_behaviours_def[of y "(i, Store e mo i)"] assms by auto
  ultimately show ?thesis
    using assms Deliver_added_files apply_operations_added_files by blast
qed

lemma (in imap) Deliver_added_ids:
  assumes "xs prefix of j"
    and "i \<in> set (added_ids xs e)"
  shows "Deliver (i, Create i e) \<in> set xs \<or> 
    (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set xs)"
  using assms proof (induct xs rule: rev_induct, clarsimp)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case X: (Deliver e')
    moreover obtain a b where "e' = (a, b)" by force
    ultimately show ?thesis
      using snoc apply (case_tac b; clarify)
          apply (simp)
          apply (metis added_ids_Deliver_Create_diff_collapse added_ids_Deliver_Create_same_collapse
          empty_iff list.set(1) set_ConsD create_id_valid in_set_conv_decomp prefix_of_appendD)
         apply (force)
      using  append_id_valid apply (simp)       
        apply (metis (no_types, lifting)  prefix_of_appendD)
       apply (simp)      
       apply (metis Un_iff added_ids_Deliver_Expunge_diff_collapse 
          added_ids_Deliver_Expunge_same_collapse empty_iff expunge_id_valid list.set(1) 
          list.set_intros(1) prefix_of_appendD set_ConsD set_append)
      by (simp, blast)
  qed
qed

lemma (in imap) Broadcast_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (r, Delete ix e)] prefix of j"
    and "i \<in> ix"
  shows "Deliver (i, Create i e) \<in> set xs \<or> 
    Deliver (i, Append i e) \<in> set xs \<or> 
    (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set xs) \<or> 
    (\<exists> mo . Deliver (i, Store e mo i) \<in> set xs)"
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

lemma (in imap) ids_are_unique:
  assumes "xs prefix of j"
    and "(i, Create i e1) \<in> set (node_deliver_messages xs)" 
    and "(l, Append l e2) \<in> set (node_deliver_messages xs)"
    and "(k, Expunge e3 mo k) \<in> set (node_deliver_messages xs)"
    and "(m, Store e4 mo2 m) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> l \<and> i \<noteq> k \<and> l \<noteq> k \<and> i \<noteq> m \<and> l \<noteq> m \<and> k \<noteq> m"
  using assms delivery_has_a_cause events_before_exist prefix_msg_in_history
  by (metis fst_conv msg_id_unique operation.distinct prod.inject)

lemma (in imap) concurrent_create_delete_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Create i e) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Create i e) (ir, Delete is e)"
proof -
  obtain pre k where history: "pre@[Broadcast (ir, Delete is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  hence "pre prefix of k" by blast
  moreover hence S: "Deliver (i, Create i e) \<in> set pre \<or> 
                  Deliver (i, Append i e) \<in> set pre \<or> 
                  (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> 
                  (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms history by auto      
  hence "Deliver (i, Create i e) \<in> set pre" 
    using network.msg_id_unique network.delivery_has_a_cause assms ids_are_unique history
  proof -
    obtain aa :: 'a and aaa :: 'a where
      f1: "(Deliver (i, Append i e) \<in> set pre \<or> 
          (\<exists>a. Deliver (i, Expunge e a i) \<in> set pre) \<or> 
          (\<exists>a. Deliver (i, Store e a i) \<in> set pre)) = (Deliver (i, Append i e) \<in> set pre \<or> 
          Deliver (i, Expunge e aaa i) \<in> set pre \<or> 
          Deliver (i, Store e aa i) \<in> set pre)"
      by blast
    have f2: "\<forall>p n pa na. Broadcast p \<notin> set (history n) \<or> Broadcast pa \<notin> set (history na) \<or> fst p \<noteq> fst pa \<or> n = na \<and> p = pa"
      using msg_id_unique by presburger
    obtain nn :: "'a \<times> ('a, 'b) operation \<Rightarrow> nat" where
      f3: "\<forall>p n. Deliver p \<notin> set (history n) \<or> Broadcast p \<in> set (history (nn p))"
      by (metis (no_types) delivery_has_a_cause)
    then have f4: "Broadcast (i, Create i e) \<in> set (history (nn (i, Create i e)))"
      using assms(2) assms(3) prefix_msg_in_history by blast
    have f5: "\<forall>es n e. \<not> es prefix of n \<or> e \<notin> set es \<or> e \<in> set (history n)"
      using prefix_elem_to_carriers by blast
    then have f6: "Deliver (i, Append i e) \<in> set pre \<longrightarrow> nn (i, Append i e) = nn (i, Create i e) \<and> (i, Append i e) = (i, Create i e)"
      using f4 f3 f2 by (metis (no_types) calculation fst_conv)
    have f7: "Deliver (i, Expunge e aaa i) \<in> set pre \<longrightarrow> nn (i, Expunge e aaa i) = nn (i, Create i e) \<and> (i, Expunge e aaa i) = (i, Create i e)"
      using f5 f4 f3 f2 by (metis (no_types) calculation fst_conv)
    have "Deliver (i, Store e aa i) \<in> set pre \<longrightarrow> Deliver (i, Create i e) \<in> set pre"
      using f5 f4 f3 f2 by (metis (no_types) calculation fst_conv)
    then show ?thesis
      using f7 f6 f1 \<open>Deliver (i, Create i e) \<in> set pre \<or> Deliver (i, Append i e) \<in> set pre \<or> (\<exists>mo. Deliver (i, Expunge e mo i) \<in> set pre) \<or> (\<exists>mo. Deliver (i, Store e mo i) \<in> set pre)\<close> by blast
  qed   
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order history by blast
qed

lemma (in imap) concurrent_append_delete_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (ir, Delete is e)"
proof -
  obtain pre k where "pre@[Broadcast (ir, Delete is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (i, Create i e) \<in> set pre \<or> Deliver (i, Append i e) \<in> set pre \<or> (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto

  hence "Deliver (i, Append i e) \<in> set pre" using assms ids_are_unique
  proof -
    have "pre prefix of k"
      using calculation by blast
    then have "\<And>e. e \<notin> set pre \<or> e \<in> set (history k)"
      by (simp add: node_histories.prefix_elem_to_carriers node_histories_axioms)
    then have "\<And>p. Deliver p \<notin> set pre \<or> fst p \<noteq> i \<or> p = (i, Append i e)"
      by (metis (no_types) \<open>(i, Append i e) \<in> set (node_deliver_messages xs)\<close> \<open>xs prefix of j\<close> delivery_has_a_cause fst_conv msg_id_unique prefix_msg_in_history)
    then show ?thesis
      using \<open>Deliver (i, Create i e) \<in> set pre \<or> Deliver (i, Append i e) \<in> set pre \<or> (\<exists>mo. Deliver (i, Expunge e mo i) \<in> set pre) \<or> (\<exists>mo. Deliver (i, Store e mo i) \<in> set pre)\<close> by fastforce
  qed 
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed

lemma (in imap) concurrent_append_expunge_independent_technical:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e mo r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (r, Expunge e mo r)"
proof -
  obtain pre k where "pre@[Broadcast (r, Expunge e mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence "Deliver (mo, Append mo e) \<in> set pre \<or> (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) by auto

  hence "Deliver (i, Append i e) \<in> set pre" using assms assms ids_are_unique
  proof -
    obtain aa :: 'a where
      f1: "Deliver (mo, Append mo e) \<in> set pre \<or> Deliver (mo, Store e aa mo) \<in> set pre"
      using \<open>Deliver (mo, Append mo e) \<in> set pre \<or> (\<exists>mo2. Deliver (mo, Store e mo2 mo) \<in> set pre)\<close> by blast
    have f2: "Deliver (mo, Append mo e) \<in> set (history j)"
      using \<open>(i, Append i e) \<in> set (node_deliver_messages xs)\<close> \<open>i = mo\<close> \<open>xs prefix of j\<close> prefix_msg_in_history by blast
    { assume "Deliver (mo, Store e aa mo) \<in> set pre"
      { assume "v2_1 (mo, Store e aa mo) \<noteq> (v2_1 (mo, Append mo e)::nat) \<or> (mo, Store e aa mo) \<noteq> (mo, Append mo e)"
        then have "Deliver (mo, Store e aa mo) \<notin> set pre"
          using f2 by (metis (no_types) calculation delivery_has_a_cause fst_conv msg_id_unique prefix_elem_to_carriers prefix_of_appendD) }
      then have "Deliver (mo, Store e aa mo) \<in> set pre \<longrightarrow> Deliver (i, Append i e) \<in> set pre"
        by blast }
    then show ?thesis
      using f1 \<open>i = mo\<close> by blast
  qed
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed

lemma (in imap) concurrent_store_delete_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Store e mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Store e mo i) (ir, Delete is e)"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence A: "Deliver (i, Create i e) \<in> set pre \<or> 
  Deliver (i, Append i e) \<in> set pre \<or>
  (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> 
  (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto      
  hence "Deliver (i, Store e mo i) \<in> set pre" using assms ids_are_unique P 


  proof -
    have "pre prefix of k"
      using calculation by blast
    then have "\<And>e. \<not> node_histories history \<or> e \<notin> set pre \<or> e \<in> set (history k)"
      by (simp add: node_histories.prefix_elem_to_carriers)
    then have f1: "\<And>e. e \<notin> set pre \<or> e \<in> set (history k)"
      using node_histories_axioms by blast
    have "\<And>f. \<not> network history (f::'a \<times> ('a, 'b) operation \<Rightarrow> 'a) \<or> Deliver (i, Store e mo i) \<in> set (history j)"
      by (meson assms network.prefix_msg_in_history)
    then have f2: "Deliver (i, Store e mo i) \<in> set (history j)"
      using network_axioms by blast
    obtain nn :: "'a \<times> ('a, 'b) operation \<Rightarrow> nat" where
      f3: "\<And>p n. Deliver p \<notin> set (history n) \<or> Broadcast p \<in> set (history (nn p))"
      by (metis delivery_has_a_cause)
    then have f4: "Broadcast (i, Store e mo i) \<in> set (history (nn (i, Store e mo i)))"
      using f2 by blast
    have "\<And>p. Deliver p \<notin> set pre \<or> Broadcast p \<in> set (history (nn p))"
      using f3 f1 by blast
    then show ?thesis
      using f4 by (metis (no_types) A fst_conv msg_id_unique)
  qed      
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed

lemma (in imap) concurrent_store_expunge_independent_technical2:
  assumes "xs prefix of j"
    and "(i, Store e1 mo2 i) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e mo r) \<in> set (node_deliver_messages xs)"
  shows "mo2 \<noteq> r"
proof -
  obtain nn :: "'a \<times> ('a, 'b) operation \<Rightarrow> nat" where
    f1: "\<forall>p n. Deliver p \<notin> set (history n) \<or> Broadcast p \<in> set (history (nn p))"
    by (metis (no_types) delivery_has_a_cause)
  then have f2: "Broadcast (r, Expunge e mo r) \<in> set (history (nn (r, Expunge e mo r)))"
    using assms(1) assms(3) prefix_msg_in_history by blast
  obtain aa :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> ('a, 'b) operation) event list \<Rightarrow> 'a" where
    f3: "\<forall>x1 x2 x4. (\<exists>v6. Deliver (x1, Store x2 v6 x1) \<in> set x4) = (Deliver (x1, Store x2 (aa x1 x2 x4) x1) \<in> set x4)"
    by moura
  obtain ees :: "nat \<Rightarrow> ('a \<times> ('a, 'b) operation) event \<Rightarrow> ('a \<times> ('a, 'b) operation) event list" where
    f4: "\<forall>x0 x1. (\<exists>v2. v2 @ [x1] prefix of x0) = (ees x0 x1 @ [x1] prefix of x0)"
    by moura
  have f5: "Deliver (i, Store e1 mo2 i) \<in> set (history j)"
    by (meson assms(1) assms(2) prefix_msg_in_history)
  obtain ee :: "('a \<times> ('a, 'b) operation) event set \<Rightarrow> ('a \<times> ('a, 'b) operation) event set \<Rightarrow> ('a \<times> ('a, 'b) operation) event" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (ee x0 x1 \<in> x1 \<and> ee x0 x1 \<notin> x0)"
    by moura
  then have f6: "(\<not> set (ees (nn (i, Store e mo2 i)) (Broadcast (i, Store e mo2 i))) \<subseteq> set (history (nn (i, Store e mo2 i))) \<or> (\<forall>ea. ea \<notin> set (ees (nn (i, Store e mo2 i)) (Broadcast (i, Store e mo2 i))) \<or> ea \<in> set (history (nn (i, Store e mo2 i))))) \<and> (set (ees (nn (i, Store e mo2 i)) (Broadcast (i, Store e mo2 i))) \<subseteq> set (history (nn (i, Store e mo2 i))) \<or> ee (set (history (nn (i, Store e mo2 i)))) (set (ees (nn (i, Store e mo2 i)) (Broadcast (i, Store e mo2 i)))) \<in> set (ees (nn (i, Store e mo2 i)) (Broadcast (i, Store e mo2 i))) \<and> ee (set (history (nn (i, Store e mo2 i)))) (set (ees (nn (i, Store e mo2 i)) (Broadcast (i, Store e mo2 i)))) \<notin> set (history (nn (i, Store e mo2 i))))"
    by blast
  have f7: "Deliver (r, Store e (aa r e (ees (nn (i, Store e mo2 i)) (Broadcast (i, Store e mo2 i)))) r) \<notin> set (history (nn (i, Store e mo2 i)))"
    using f2 f1 by (metis (no_types) Pair_inject fst_conv msg_id_unique operation.distinct(19))
  have "Broadcast (r, Append r e) \<notin> set (history (nn (r, Append r e)))"
    using f2 by (metis (no_types) added_files_Deliver_Append_same_collapse added_files_Deliver_Expunge_collapse empty_iff empty_set fst_conv list.set_intros(1) msg_id_unique)
  then show ?thesis
    using f7 f6 f5 f4 f3 f1
  proof -
    obtain aaa :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> ('a, 'b) operation) event list \<Rightarrow> 'a" where
      x1: "\<forall>x1 x2 x4. (\<exists>v6. Deliver (x1, Store x2 v6 x1) \<in> set x4) = (Deliver (x1, Store x2 (aaa x1 x2 x4) x1) \<in> set x4)"
      by moura
    obtain eesa :: "nat \<Rightarrow> ('a \<times> ('a, 'b) operation) event \<Rightarrow> ('a \<times> ('a, 'b) operation) event list" where
      "\<forall>x0 x1. (\<exists>v2. v2 @ [x1] prefix of x0) = (eesa x0 x1 @ [x1] prefix of x0)"
      by moura
    then have x2: "\<forall>e n. e \<notin> set (history n) \<or> eesa n e @ [e] prefix of n"
      using events_before_exist by presburger
    then have x3: "eesa (nn (i, Store e1 mo2 i)) (Broadcast (i, Store e1 mo2 i)) prefix of nn (i, Store e1 mo2 i)"
      using f1 f5 by blast
    have x4: "Deliver (r, Append r e1) \<notin> set (history (nn (i, Store e1 mo2 i)))"
      by (metis (no_types) f1 f2 fst_conv msg_id_unique old.prod.inject operation.distinct(15))
    have "Deliver (r, Store e1 (aaa r e1 (eesa (nn (i, Store e1 mo2 i)) (Broadcast (i, Store e1 mo2 i)))) r) \<notin> set (history (nn (i, Store e1 mo2 i)))"
      by (metis (no_types) f1 f2 fst_conv msg_id_unique old.prod.inject operation.distinct(19))
    then have "r \<noteq> mo2"
      using x4 x3 x2 x1 by (meson f1 f5 imap.Broadcast_Store_Deliver_prefix_closed imap_axioms prefix_elem_to_carriers)
    then show ?thesis
      by meson
  qed 
qed

lemma (in imap) concurrent_append_store_independent_technical:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e mo r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (r, Store e mo r)"
proof -
  obtain pre k where "pre@[Broadcast (r, Store e mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence f1: "Deliver (mo, Append mo e) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1) by auto
  have f2: "Deliver (i, Append i e) \<in> set (history j)"
    by (meson assms network.prefix_msg_in_history network_axioms)
  then show ?thesis using assms f1 
    by (metis  calculation delivery_has_a_cause events_in_local_order fst_conv hb_deliver 
        msg_id_unique node_histories.prefix_of_appendD node_histories_axioms 
        prefix_elem_to_carriers)
qed

lemma (in imap) delete_prefix_options:
  assumes "i \<in> is"
    and "pre@[Broadcast (ir, Delete is e)] prefix of k" 
  shows "Deliver (i, Create i e) \<in> set pre \<or>
  Deliver (i, Append i e) \<in> set pre \<or> 
  (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> 
  (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
proof -
  show ?thesis using Broadcast_Deliver_prefix_closed assms
    by (meson imap.Broadcast_Deliver_prefix_closed imap_axioms)
qed

lemma (in imap) concurrent_store_expunge_independent_technical:
  assumes "xs prefix of j"
    and "(i, Store e mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e i r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Store e mo i) (r, Expunge e i r)"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Expunge e i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence f1: "Deliver (i, Append i e) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (i, Store e mo2 i) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) by auto
  hence f2: "Deliver (i, Append i e) \<notin> set (history k)"
    by (metis Pair_inject assms(1) assms(2) fst_conv msg_id_unique network.delivery_has_a_cause 
        network_axioms operation.distinct(17) prefix_msg_in_history)
  from f1 obtain mo2 :: 'a where
  "Deliver (i, Store e mo2 i) \<in> set (history k)" using f2
    using calculation prefix_elem_to_carriers by blast  
  hence "Deliver (i, Store e mo i) \<in> set (history k)" using assms ids_are_unique f1 f2 P 
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms prefix_msg_in_history)    
  then show ?thesis
    using hb.intros(2) events_in_local_order f1 f2 P
    by (metis delivery_has_a_cause fst_conv msg_id_unique node_histories.prefix_of_appendD 
        node_histories_axioms prefix_elem_to_carriers)
qed

lemma (in imap) concurrent_store_store_independent_technical:
  assumes "xs prefix of j"
    and "(i, Store e mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e i r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Store e mo i) (r, Store e i r)"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Store e i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  hence f1: "\<forall>e. e \<notin> set pre \<or> e \<in> set (history k)"
    using prefix_elem_to_carriers by blast
  have f2: "Deliver (i, Append i e) \<in> set pre \<or> (\<exists> mo2 . Deliver (i, Store e mo2 i) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1) P by auto     
  hence "Deliver (i, Store e mo i) \<in> set pre" using assms ids_are_unique f1 
    by (metis delivery_has_a_cause fst_conv msg_id_unique prefix_msg_in_history)
  then show ?thesis
    using hb.intros(2) events_in_local_order P by blast
qed

lemma (in imap) expunge_delete_tag_causality:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Expunge e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)" 
    and "pre@[Broadcast (ir, Delete is e2)] prefix of k"
  shows "Deliver (i, Expunge e2 mo i) \<in> set (history k)"
proof- 
  have f1: "Deliver (i, Append i e2) \<notin> set (history k)" using assms
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.distinct(15) prefix_msg_in_history)
  have f2: "Deliver (i, Create i e2) \<notin> set (history k)" using assms
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.distinct(5) prefix_msg_in_history)
  have f3: "\<forall> mo. Deliver (i, Store e2 mo i) \<notin> set (history k)" using assms
    by (metis Pair_inject fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
        operation.simps(25) prefix_msg_in_history)
  hence "\<exists> mo1. Deliver (i, Expunge e2 mo1 i) \<in> set (history k)" using assms ids_are_unique f1 f2 
    by (meson imap.Broadcast_Deliver_prefix_closed imap_axioms node_histories.prefix_of_appendD 
        node_histories_axioms prefix_elem_to_carriers)
  then obtain mo1 :: 'a where
    "Deliver (i, Expunge e2 mo1 i) \<in> set (history k)" by blast
  then show ?thesis  using assms f1 f2 f3
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.inject(4) prefix_msg_in_history)
qed


lemma (in imap) expunge_delete_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Expunge e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  hence "Deliver (i, Expunge e2 mo i) \<in> set (history k)" using assms expunge_delete_tag_causality
    by blast
  then show ?thesis using assms
    by (metis delivery_has_a_cause fst_conv network.msg_id_unique network_axioms 
        operation.inject(4) prefix_msg_in_history prod.inject)
qed

lemma (in imap) concurrent_expunge_delete_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Expunge e mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Expunge e mo i) (ir, Delete is e)"
proof -
  obtain pre k where "pre@[Broadcast (ir, Delete is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence A: "Deliver (i, Create i e) \<in> set pre \<or> 
  Deliver (i, Append i e) \<in> set pre \<or> 
  (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> 
  (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto      
  hence "Deliver (i, Expunge e mo i) \<in> set pre" using assms ids_are_unique
  proof -
    have f1: "\<And>e. e \<notin> set pre \<or> e \<in> set (history k)"
      using calculation prefix_elem_to_carriers by blast
    have f2: "Deliver (i, Expunge e mo i) \<in> set (history j)"
      by (meson assms network.prefix_msg_in_history network_axioms)
    then show ?thesis using f1 A 
      by (metis (no_types, lifting) fst_conv msg_id_unique network.delivery_has_a_cause network_axioms)
  qed     
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed

lemma (in imap) store_delete_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast 
  have f1: "Deliver (i, Append i e2) \<notin> set (history k)" using assms
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.distinct(17) prefix_msg_in_history)
  have f2: "\<forall> mo. Deliver (i, Expunge e2 mo i) \<notin> set (history k)" using assms
    by (metis Pair_inject fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
        operation.distinct(19) prefix_msg_in_history)
  have f3: "Deliver (i, Create i e2) \<notin> set (history k)" using assms
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.distinct(8) prefix_msg_in_history)
  hence "(\<exists> mo1. Deliver (i, Store e2 mo1 i) \<in> set pre)" using assms P f1 f2 ids_are_unique imap_axioms 
    by (meson imap.Broadcast_Deliver_prefix_closed prefix_elem_to_carriers prefix_of_appendD)
  then obtain mo1 :: 'a where
    f3: "Deliver (i, Store e2 mo1 i) \<in> set pre" by blast
  then have f4: "Deliver (i, Store e2 mo1 i) \<in> set (history k)"
    using P prefix_elem_to_carriers by blast 
  hence "Deliver (i, Store e2 mo i) \<in> set pre" using f2 f3 assms 
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.inject(5) prefix_msg_in_history)
  moreover have "Deliver(i, Store e1 mo i) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast 
  ultimately show ?thesis using f4
    by (metis delivery_has_a_cause fst_conv msg_id_unique old.prod.inject operation.inject(5))
qed

lemma (in imap) create_delete_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Create i e1) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  have f1: "Deliver (i, Append i e2) \<notin> set (history k)"
    by (metis assms(2) assms(3) delivery_has_a_cause fst_conv network.msg_id_unique 
        network.prefix_msg_in_history network_axioms operation.distinct(3) prod.inject)
  have f2: "\<forall> mo. Deliver (i, Expunge e2 mo i) \<notin> set (history k)"
   by (metis assms(2) assms(3) fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
       old.prod.inject operation.distinct(5) prefix_msg_in_history)
  have f3: "\<forall> mo. Deliver (i, Store e2 mo i) \<notin> set (history k)"
    by (metis Pair_inject assms(2) assms(3) delivery_has_a_cause fst_conv msg_id_unique 
        operation.distinct(7) prefix_msg_in_history)
  hence "Deliver (i, Create i e2) \<in> set pre" using assms ids_are_unique P f2 f1 imap_axioms
    by (meson imap.Broadcast_Deliver_prefix_closed  prefix_elem_to_carriers prefix_of_appendD)
  then show ?thesis using f1 f2 f3
    by (metis (no_types, lifting) P assms(2) assms(3) delivery_has_a_cause fst_conv msg_id_unique 
        node_histories.prefix_of_appendD node_histories_axioms old.prod.inject operation.inject(1) 
        prefix_elem_to_carriers prefix_msg_in_history)
qed

lemma (in imap) append_delete_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  hence f1: "\<forall>e. e \<notin> set pre \<or> e \<in> set (history k)" using prefix_elem_to_carriers by blast
  have f2: "Deliver (i, Create i e2) \<notin> set pre" using P delete_prefix_options f1
    by (metis assms(2) assms(3) fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
        old.prod.inject operation.distinct(3) prefix_msg_in_history)
  moreover have "\<forall> mo. Deliver (i, Expunge e2 mo i) \<notin> set pre" using P delete_prefix_options f1
    by (metis Pair_inject assms(2) assms(3) fst_conv msg_id_unique network.delivery_has_a_cause 
        network_axioms operation.distinct(15) prefix_msg_in_history)
  moreover have "\<forall> mo. Deliver (i, Store e2 mo i) \<notin> set pre" using P delete_prefix_options f1
    by (metis Pair_inject assms(2) assms(3) fst_conv msg_id_unique network.delivery_has_a_cause 
        network_axioms operation.simps(23) prefix_msg_in_history)
  moreover hence "Deliver (i, Append i e2) \<in> set pre" 
    using P delete_prefix_options calculation(3) f2 assms(1) calculation(2) by blast     
  moreover have "Deliver (i, Append i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis using assms delete_prefix_options 
    by (metis f1 msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.inject(3) prod.sel(1))
qed

lemma (in imap) append_expunge_ids_imply_messages_same:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where "pre@[Broadcast (r, Expunge e2 mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  moreover hence "Deliver (mo, Append mo e2) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (mo, Store e2 mo2 mo) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1)
    by (meson imap.Broadcast_Deliver_prefix_closed imap_axioms)      
  hence "Deliver (i, Append i e2) \<in> set pre" using assms ids_are_unique
    by (metis (no_types, lifting) calculation delivery_has_a_cause fst_conv hb_broadcast_exists1 
        msg_id_unique network.hb_deliver network.prefix_msg_in_history network_axioms 
        node_histories.events_in_local_order node_histories_axioms operation.distinct(17) 
        prod.inject)     
  moreover have "Deliver (i, Append i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
    by (metis (no_types, lifting) fst_conv network.delivery_has_a_cause network.msg_id_unique 
        network_axioms operation.inject(3) prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed

lemma (in imap) append_store_ids_imply_messages_same:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Store e2 mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  moreover hence A: "Deliver (mo, Append mo e2) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (mo, Store e2 mo2 mo) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1)
    by (meson imap.Broadcast_Deliver_prefix_closed imap_axioms)
  have f1: "Deliver (i, Append i e1) \<in> set (history j)"
        using assms(2) assms(3) prefix_msg_in_history by blast
  hence "Deliver (i, Append i e2) \<in> set pre" using assms ids_are_unique P A
    by (metis Pair_inject assms(1) calculation delivery_has_a_cause fst_conv msg_id_unique 
        operation.simps(23) prefix_elem_to_carriers prefix_of_appendD)
  then show ?thesis using f1
    by (metis calculation delivery_has_a_cause fst_conv msg_id_unique 
        node_histories.prefix_of_appendD node_histories_axioms operation.inject(3) 
        prefix_elem_to_carriers prod.inject)
qed

lemma (in imap) expunge_store_ids_imply_messages_same:
  assumes "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e2 i r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Expunge e2 i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast 
  hence pprefix: "pre prefix of k"
      using P by blast
  have A: "Deliver (i, Append i e2) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (i, Store e2 mo2 i) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) P by blast      
  have "Deliver (i, Store e2 mo i) \<in> set pre" using assms ids_are_unique A P
  proof -
    obtain op1 :: "'a \<times> ('a, 'b) operation \<Rightarrow> nat" where
      f1: "Broadcast (i, Store e1 mo i) \<in> set (history (op1 (i, Store e1 mo i)))"
      by (meson assms(1) assms(2) delivery_has_a_cause prefix_msg_in_history)
    then show ?thesis 
      using f1 A pprefix delivery_has_a_cause network.msg_id_unique network_axioms 
        node_histories.prefix_to_carriers node_histories_axioms 
      by fastforce
  qed
  moreover have "Deliver (i, Store e1 mo i) \<in> set (history j)"
    using assms(1) assms(2) prefix_msg_in_history by auto
  ultimately show ?thesis using assms P
    by (metis delivery_has_a_cause fst_conv msg_id_unique operation.inject(5) 
        prefix_elem_to_carriers prefix_of_appendD prod.inject) 
qed

lemma (in imap) store_store_ids_imply_messages_same:
  assumes "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e2 i r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Store e2 i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  moreover hence A: "Deliver (i, Append i e2) \<in> set pre \<or>
    (\<exists> mo2 . Deliver (i, Store e2 mo2 i) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1) by blast
  have "\<forall>e. e \<notin> set pre \<or> e \<in> set (history k)"
    using calculation prefix_elem_to_carriers by auto
  hence "Deliver (i, Store e2 mo i) \<in> set pre" 
    by (metis A assms(1) assms(2) delivery_has_a_cause fst_conv msg_id_unique 
        operation.distinct(17) operation.inject(5) prefix_msg_in_history prod.inject)
  moreover have "Deliver (i, Store e1 mo i) \<in> set (history j)"
    using assms(1) assms(2) prefix_msg_in_history by auto
  ultimately show ?thesis using assms
    by (metis Pair_inject delivery_has_a_cause msg_id_unique operation.simps(5) 
        prefix_elem_to_carriers prefix_of_appendD prod.sel(1))
qed 

end
