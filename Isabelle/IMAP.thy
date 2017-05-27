theory IMAP
imports ORSet

begin



-- "#############################"
-- "### Definitions & Helpers ###"
-- "#############################"


-- "Type definition: 'a is the set of all folder names, 'b is the set of all message names"
type_synonym ('a, 'b) imap = "'a orset \<times> ('a \<rightharpoonup> 'b set)"

abbreviation folderset ::
  "('a, 'b) imap \<Rightarrow> 'a orset"
where
  "folderset I \<equiv> fst I"

abbreviation filesystem ::
  "('a, 'b) imap \<Rightarrow> ('a \<rightharpoonup> 'b set)"
where
  "filesystem I \<equiv> snd I"


definition validState ::
  "('a, 'b) imap \<Rightarrow> bool"
where
  "validState I = ((\<forall> (a, _) \<in> folderset I . (filesystem I) a \<noteq> None)
  \<and> (\<forall> f . (filesystem I) f \<noteq> None \<longrightarrow> (\<exists> (a, _) \<in> folderset I . a = f)))"

definition Msg ::
  "'b \<Rightarrow> 'b \<Rightarrow> 'b set \<Rightarrow> 'b set"
where
  "Msg msgold msgnew S = (S - {msgold}) \<union> {msgnew}"

definition msgLookup ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "msgLookup f msg I = (
  case (filesystem I)(f) of
      None \<Rightarrow> False |
      Some msgset \<Rightarrow> msg \<in> msgset
  )"

-- "#######################"
-- "### IMAP Operations ###"
-- "#######################"

definition create_pre ::
  "'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "create_pre f n I = (add_pre n (folderset I) \<and> \<not> lookup f (folderset I))"

definition create ::
  "'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "create f n I = (add f n (folderset I), (filesystem I)(f := Some {}))"

definition delete_pre ::
  "'a \<Rightarrow> 'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "delete_pre f R I = remove_pre f R (folderset I)"

definition delete ::
  "'a \<Rightarrow> 'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "delete f R I = (remove R (folderset I), (filesystem I)(f := None))"

definition append_pre ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "append_pre f m I = (\<exists> (a, _) \<in> folderset I . a = f \<and> \<not> msgLookup f m I)"

definition append ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "append f m I =
  (folderset I,
  (case (filesystem I)(f) of
      None \<Rightarrow> filesystem I |
      Some msgset \<Rightarrow> (filesystem I)(f := Some (msgset \<union> {m}))
  ))"


definition store_pre ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "store_pre f msgold msgnew I = ((\<exists> (a, _) \<in> folderset I . a = f) \<and> msgLookup f msgold I \<and> \<not>(msgLookup f msgnew I))"

definition store ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "store f msgold msgnew I =
  (folderset I,
  (case (filesystem I)(f) of
      None \<Rightarrow> filesystem I |
      Some msgset \<Rightarrow> (filesystem I)(f := Some (Msg msgold msgnew msgset))
  ))"

definition EXPUNGE_atSource ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "EXPUNGE_atSource f m I = ((\<exists> (a, _) \<in> folderset I . a = f) \<and> msgLookup f m I)"

definition EXPUNGE_downstream ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "EXPUNGE_downstream f m I =
  (folderset I,
  (case (filesystem I)(f) of
      None \<Rightarrow> filesystem I |
      Some msgset \<Rightarrow> (filesystem I)(f := Some (msgset - {m}))
  ))"



-- "########################"
-- "### Auxiliary Lemmas ###"
-- "########################"


lemma append_not_none:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  m1 :: "'b"
assumes
  O1pre: " append_pre f1 m1 I" and
  validS: "validState I"
shows "filesystem (append f1 m1 I) f1 \<noteq> None"
proof -
  have "filesystem I f1 \<noteq> None"
  using O1pre validS
  unfolding validState_def append_pre_def
  by auto

  thus ?thesis
  using validS O1pre
  unfolding append_def validState_def append_pre_def
  by auto
qed

lemma append_folderset:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a" and
  m :: "'b"
shows "folderset (append f m I) = folderset I"
proof -
  show ?thesis
  unfolding append_def
  by auto
qed

lemma append_filesystem:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  m1 :: "'b"
assumes
  O1pre: " append_pre f1 m1 I" and
  validS: "validState I"
shows "\<forall> f . f \<noteq> f1 \<longrightarrow> filesystem (append f1 m1 I) f = filesystem I f"
proof -
  show ?thesis
  by (simp add: append_def option.case_eq_if)
qed


lemma store_folderset:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a"
shows "folderset (store f msgold msgnew I) = folderset I"
proof -
  show ?thesis
  unfolding store_def
  by auto
qed


lemma store_filesystem:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a"
shows "\<forall> f. f \<noteq> f1 \<longrightarrow> filesystem (store f1 msgold msgnew I) f = filesystem I f"
proof -
  show ?thesis
  unfolding store_def
  by (simp add: option.case_eq_if)
qed


lemma store_not_none:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  msgold :: "'b" and
  msgnew :: "'b"
assumes
  pre: "store_pre f1 msgold msgnew I"
shows "filesystem (store f1 msgold msgnew I) f1 \<noteq> None"
proof -
  show ?thesis
  using pre unfolding store_def store_pre_def msgLookup_def
  by (metis fun_upd_same option.case_eq_if option.simps(3) snd_conv)
qed



-- "#########################################"
-- "### Closure Proofs of IMAP Operations ###"
-- "#########################################"


lemma create_valid:
fixes
  I :: "('a, 'b) imap" and
  e :: "'a" and
  n :: nat
assumes
  validS: "validState I"
shows "validState (create e n I)"
proof -
  show ?thesis
  using validS
  unfolding create_def add_def validState_def create_pre_def
  apply simp
  by (simp add: split_def)
qed


lemma delete_valid:
fixes
  I :: "('a, 'b) imap" and
  R :: "'a orset" and
  e1 :: "'a"
assumes
  O1pre: "delete_pre e1 R I" and
  validS: "validState I"
shows "validState (delete e1 R I)"
proof -
  have A1: "\<forall> (a, b) \<in> folderset I. a \<noteq> e1 \<longrightarrow> (a, b) \<in> folderset (delete e1 R I)"
  using O1pre
  unfolding delete_def remove_def delete_pre_def remove_pre_def
  by auto

  have "\<forall> (a, _) \<in> folderset (delete e1 R I). a \<noteq> e1"
  using O1pre
  unfolding delete_def remove_def delete_pre_def remove_pre_def
  by auto

  hence "(\<forall> (a, _) \<in> folderset (delete e1 R I) . (filesystem (delete e1 R I)) a \<noteq> None)" using validS
  unfolding validState_def delete_def remove_def delete_pre_def remove_pre_def
  by fastforce

  thus ?thesis
  using validS A1
  unfolding validState_def delete_pre_def delete_def remove_def remove_pre_def
  apply simp
  by blast
qed


lemma append_valid:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  m1 :: "'b"
assumes
  O1pre: " append_pre f1 m1 I" and
  validS: "validState I"
shows "validState (append f1 m1 I)"
proof -
  have "folderset (append f1 m1 I) = folderset I"
  unfolding append_def
  by auto

  hence "(\<forall>f. filesystem (append f1 m1 I) f \<noteq> None \<longrightarrow> (\<exists> (a, _) \<in>folderset (append f1 m1 I). a = f))"
  using O1pre
  by (metis (no_types, lifting) append_pre_def append_filesystem case_prod_beta' validS validState_def)

  thus ?thesis
  using O1pre validS
  unfolding validState_def append_def
  apply simp
  by (smt case_prodE fun_upd_apply old.prod.case option.case_eq_if)
qed


lemma store_valid:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a" and
  msgold :: "'b" and
  msgnew :: "'b"
assumes
  O1pre : "store_pre f msgold msgnew I" and
  validS: "validState I"
shows "validState (store f msgold msgnew I)"
proof -
  show ?thesis
  using O1pre validS
  unfolding store_def store_pre_def msgLookup_def Msg_def
  by (simp add: case_prod_beta' fun_upd_same option.case_eq_if validState_def)
qed


lemma expunge_valid:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a" and
  m :: "'b"
assumes
  O1pre: "EXPUNGE_atSource f m I" and
  validS: "validState I"
shows "validState (EXPUNGE_downstream f m I)"
proof -
  show ?thesis
  using O1pre validS
  unfolding EXPUNGE_atSource_def EXPUNGE_downstream_def msgLookup_def validState_def
  by (simp add: case_prod_beta' option.case_eq_if)
qed

-- "###############################################"
-- "### Commutativity Proofs of IMAP Operations ###"
-- "###############################################"

-- "        CREATE DELETE APPEND STORE EXPUNGE"
-- "                                          "
-- " CREATE    1      2     3      4      5   "
-- "                                          "
-- " DELETE    2      6     7      8      9   "
-- "                                          "
-- " APPEND    3      7    10     11     12   "
-- "                                          "
-- "  STORE    4      8    11     13     14   "
-- "                                          "
-- "EXPUNGE    5      9    12     14     15   "



-- "Case 1"
lemma comm_create_create:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  n1 :: nat and
  n2 :: nat
assumes
  O1pre: "create_pre f1 n1 I " and
  O2pre: "create_pre f2 n2 I" 
shows "create f1 n1 (create f2 n2 I) = create f2 n2 (create f1 n1 I)"
proof -
  show ?thesis 
    using orset_comm[of "Add f1 n1" "folderset I" "Add f2 n2"] O1pre O2pre
    unfolding create_pre_def create_def 
    by auto
qed

-- "Case 2"
lemma comm_create_delete:
fixes
  I :: "('a, 'b) imap" and
  R :: "'a orset" and
  f1 :: "'a" and
  f2 :: "'a" and
  n :: nat
assumes
  O1pre: "delete_pre f1 R I " and
  O2pre: "create_pre f2 n I" 
shows "delete f1 R (create f2 n I) = create f2 n (delete f1 R I)"
proof -
  have A1: "folderset (delete f1 R (create f2 n I)) = folderset (create f2 n (delete f1 R I))"
    using O1pre O2pre orset_comm[of "Remove f1 R" "folderset I" "Add f2 n"]
    by (simp add: delete_pre_def create_pre_def delete_def create_def)
  have "filesystem (delete f1 R (create f2 n I)) = filesystem (create f2 n (delete f1 R I))"
    using O1pre O2pre
    unfolding delete_def create_def delete_pre_def remove_pre_def create_pre_def     
    by fastforce
  thus ?thesis using A1 by (simp add: delete_def)
qed

-- "Case 6"
lemma comm_delete_delete:
fixes
  I :: "('a, 'b) imap" and
  R1 :: "'a orset" and
  R2 :: "'a orset" and
  f1 :: "'a" and
  f2 :: "'a"
assumes
  O1pre: "delete_pre f1 R1 I" and
  O2pre: "delete_pre f2 R2 I"
shows "delete f2 R2 (delete f1 R1 I) = delete f1 R1 (delete f2 R2 I)"
proof -
  have A1: "folderset(delete f2 R2 (delete f1 R1 I)) = folderset(delete f1 R1 (delete f2 R2 I))"
    using O1pre O2pre orset_comm[of "Remove f1 R1" "folderset I" "Remove f2 R2"]
    by (simp add: delete_pre_def delete_def)
  have "filesystem(delete f2 R2 (delete f1 R1 I)) = filesystem(delete f1 R1 (delete f2 R2 I))"
    using O1pre O2pre
    by (metis (mono_tags, lifting) delete_def fun_upd_twist snd_conv)    
  thus ?thesis using A1 by (simp add: delete_def)
qed
  
-- "Case 3"
-- "TODO: remove smt"
lemma comm_create_append:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  n :: nat and
  f2 :: "'a" and
  m :: "'b"
assumes
  O1pre: "append_pre f1 m I" and
  O2pre: "create_pre f2 n I"
shows "append f1 m (create f2 n I) = create f2 n (append f1 m I)"
proof -
  have "filesystem(append f1 m (create f2 n I)) = filesystem(create f2 n (append f1 m I))"
    using O1pre O2pre
    unfolding append_pre_def append_def create_pre_def create_def lookup_def apply simp
    by (smt case_prodE eq_snd_iff fun_upd_twist option.case_eq_if)
  thus ?thesis by (simp add: append_def create_def)
qed
  
-- "Case 7"
lemma comm_delete_append:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m :: "'b" and
  R :: "'a orset"
assumes
  O1pre: "append_pre f1 m I" and
  O2pre: "delete_pre f2 R I"
shows "append f1 m (delete f2 R I) = delete f2 R (append f1 m I)"
proof -
  have A1: "folderset(append f1 m (delete f2 R I)) = folderset(delete f2 R (append f1 m I))"
    by (simp add: append_folderset delete_def)
  have "filesystem(append f1 m (delete f2 R I)) = filesystem(delete f2 R (append f1 m I))"
    using O1pre O2pre
    unfolding append_pre_def append_def delete_pre_def delete_def
    by (simp add: fun_upd_twist option.case_eq_if)
  thus ?thesis using A1 prod_eqI  by blast
qed
  
-- "Case 10"
-- "TODO: remove smt"
lemma comm_append_append:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m1 :: "'b" and
  m2 :: "'b"
assumes
  O1pre: "append_pre f1 m1 I" and
  O2pre: "append_pre f2 m2 I"
shows "append f1 m1 (append f2 m2 I) = append f2 m2 (append f1 m1 I)"
proof -
  have A1: "folderset(append f1 m1 (append f2 m2 I)) = folderset(append f2 m2 (append f1 m1 I))"
    by (simp add: append_def)
  have "filesystem(append f1 m1 (append f2 m2 I)) = filesystem(append f2 m2 (append f1 m1 I))"
    using O1pre O2pre
    unfolding append_def append_pre_def msgLookup_def
    by (smt Un_insert_right fun_upd_twist fun_upd_upd insert_commute map_upd_Some_unfold option.case_eq_if option.collapse option.simps(3) snd_conv sup_bot.right_neutral)
  thus ?thesis using A1 by (simp add: prod_eq_iff)
qed
  
-- "Case 4"
lemma comm_create_store:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  mo :: "'b" and
  mn :: "'b" and
  n :: nat
assumes
  O1pre: "store_pre f1 mo mn I" and
  O2pre: "create_pre f2 n I"
shows "store f1 mo mn (create f2 n I) = create f2 n (store f1 mo mn I)"
proof -
  have A1: "folderset (store f1 mo mn (create f2 n I)) = folderset (create f2 n (store f1 mo mn I))"
    by (simp add: create_def store_folderset)
  have "filesystem (store f1 mo mn (create f2 n I)) = filesystem (create f2 n (store f1 mo mn I))"
    using O1pre O2pre
    unfolding store_def create_def create_pre_def store_pre_def lookup_def 
    by (smt case_prodE fun_upd_other fun_upd_twist option.case_eq_if snd_conv)
  thus ?thesis by (simp add: A1 prod.expand)
qed
  
-- "Case 8"
lemma comm_delete_store:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  mo :: "'b" and
  mn :: "'b" and
  R :: "'a orset"
assumes
  O1pre: "store_pre f1 mo mn I" and
  O2pre: "delete_pre f2 R I"
shows "store f1 mo mn (delete f2 R I) = delete f2 R (store f1 mo mn I)"
proof -
  have A1: "folderset (store f1 mo mn (delete f2 R I)) = folderset(delete f2 R (store f1 mo mn I))"
    by (simp add: delete_def store_folderset)
  have "filesystem (store f1 mo mn (delete f2 R I)) = filesystem(delete f2 R (store f1 mo mn I))"
    using O1pre O2pre
    unfolding store_def delete_def delete_pre_def store_pre_def
    by (simp add: fun_upd_twist option.case_eq_if)
  thus ?thesis by (simp add: A1 prod.expand)
qed
  
-- "Case 11"
lemma comm_append_store:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  mo :: "'b" and
  mn :: "'b" and
  m :: "'b"
assumes
  O1pre: " store_pre f1 mo mn I" and
  O2pre: " append_pre f2 m I"
shows "store f1 mo mn (append f2 m I) = append f2 m (store f1 mo mn I)"
proof -
  have A1: "folderset (store f1 mo mn (append f2 m I)) = folderset (append f2 m (store f1 mo mn I))"
    by (simp add: append_def store_folderset)
  have "filesystem (store f1 mo mn (append f2 m I)) = filesystem(append f2 m (store f1 mo mn I))"
    using O1pre O2pre unfolding store_def append_def append_pre_def store_pre_def Msg_def msgLookup_def
    apply (simp add: case_prod_beta') 
    by (smt Diff_empty Diff_insert0 Un_Diff Un_insert_left Un_insert_right fun_upd_twist fun_upd_upd insert_Diff insert_Diff1 map_upd_Some_unfold option.case_eq_if option.collapse option.simps(3) singletonI snd_conv)
  thus ?thesis using A1 by (simp add: prod.expand)
qed

-- "Case 13"
lemma comm_store_store:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  mo1 :: "'b" and
  mo2 :: "'b" and
  mn1 :: "'b" and
  mn2 :: "'b"
assumes
  O1pre: " store_pre f1 mo1 mn1 I" and
  O2pre: " store_pre f2 mo2 mn2 I"
shows "store f1 mo1 mn1 (store f2 mo2 mn2 I) = store f2 mo2 mn2 (store f1 mo1 mn1 I)"
proof -
  have A1: "folderset (store f1 mo1 mn1 (store f2 mo2 mn2 I)) = folderset(store f2 mo2 mn2 (store f1 mo1 mn1 I))"
    by (simp add: store_folderset)

  have A2: "\<forall> f . f1 \<noteq> f2 \<longrightarrow> filesystem (store f1 mo1 mn1 (store f2 mo2 mn2 I)) f = filesystem(store f2 mo2 mn2 (store f1 mo1 mn1 I)) f"
    by (smt store_def fun_upd_twist option.case_eq_if snd_conv store_filesystem)

  have "f1 = f2 \<longrightarrow> filesystem (store f1 mo1 mn1 (store f2 mo2 mn2 I)) f1 = filesystem(store f2 mo2 mn2 (store f1 mo1 mn1 I)) f1"
  proof auto
    assume Ass: "f1 = f2"

    hence "filesystem (store f1 mo1 mn1 (store f2 mo2 mn2 I)) f1 \<noteq> None"
      by (smt O2pre store_def fun_upd_eqD fun_upd_triv option.case_eq_if option.simps(3) snd_conv store_not_none)

    hence "\<exists> y . filesystem (store f1 mo1 mn1 (store f2 mo2 mn2 I)) f1 = Some y"
      by simp

    then obtain y
    where Ass4: "filesystem (store f1 mo1 mn1 (store f2 mo2 mn2 I)) f1 = Some y"
      by blast

    have "\<exists> S . filesystem (I) f1 = Some S"
      by (metis O2pre store_pre_def \<open>f1 = f2\<close> case_optionE msgLookup_def)

    then obtain S
    where Ass2: "(filesystem I) f1 = Some S"
      by blast

    have "\<exists> x . filesystem (store f2 mo2 mn2 I) f1 = Some x"
      using Ass
      by (metis O2pre option.collapse store_not_none)
    then obtain x where Ass3: "filesystem (store f2 mo2 mn2 I) f1 = Some x"
      by blast
    have "x = (S - {mo2}) \<union> {mn2}"
      using Ass Ass2 Ass3
      unfolding store_def Msg_def
      by simp
    hence Ass6: "y = (S - {mo1,mo2}) \<union> {mn1,mn2}"
      using Ass Ass2 Ass3 Ass4 O1pre O2pre
      unfolding store_def Msg_def store_pre_def
      by auto
    have "\<exists> w . filesystem (store f1 mo1 mn1 I) f1 = Some w"
      using Ass
      by (metis O1pre option.collapse store_not_none)
    then obtain w where Ass8: "filesystem (store f1 mo1 mn1 I) f1 = Some w"
      by blast
    hence Ass9: "w = (S - {mo1}) \<union> {mn1}"
      using Ass Ass2
      unfolding store_def Msg_def
      by simp
    have "filesystem(store f2 mo2 mn2 (store f1 mo1 mn1 I)) f1 \<noteq> None"
      using O1pre Ass Ass2
      unfolding store_def
      by auto
    hence "\<exists> z . filesystem(store f2 mo2 mn2 (store f1 mo1 mn1 I)) f1 = Some z"
      by simp
    then obtain z where Ass7: "filesystem(store f2 mo2 mn2 (store f1 mo1 mn1 I)) f1 = Some z"
      by blast
    hence "z = (S - {mo1,mo2}) \<union> {mn1,mn2}"
      using Ass Ass2 Ass9 Ass8 O1pre O2pre
      unfolding store_def Msg_def store_pre_def
      by auto
    thus "filesystem (store f2 mo1 mn1 (store f2 mo2 mn2 I)) f2 = filesystem (store f2 mo2 mn2 (store f2 mo1 mn1 I)) f2"
      using Ass7 Ass4 Ass6 Ass
      by auto
  qed

  thus ?thesis
  using A1 A2
  by (smt O1pre O2pre store_def fun_upd_same fun_upd_twist fun_upd_upd option.case_eq_if prod_eqI snd_conv store_not_none)
qed
-- "###############################################"
-- "### Framework ###"
-- "###############################################"  

datatype ('a, 'b) ops = Create 'a nat | Delete 'a "'a orset" | Append 'a 'b | Store 'a 'b 'b

fun imap_downstream :: "('a, 'b) ops \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a,'b) imap" where
  "imap_downstream (Create f n) imap = create f n imap"
| "imap_downstream (Delete f R) imap = delete f R imap"
| "imap_downstream (Append f m) imap = append f m imap"
| "imap_downstream (Store f mo mn) imap = store f mo mn imap"
  
  
fun imap_atSource :: "('a, 'b) ops \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool" where
  "imap_atSource (Create f n) imap = create_pre f n imap"
| "imap_atSource (Delete f R) imap = delete_pre f R imap"
| "imap_atSource (Append f m) imap = append_pre f m imap"
| "imap_atSource (Store f mo mn) imap = store_pre f mo mn imap"
  
theorem imap_comm :
fixes
  I :: "('a, 'b) imap" and
  O1 :: "('a, 'b) ops" and
  O2 :: "('a, 'b) ops"
assumes
  O1pre: "imap_atSource O1 I" and
  O2pre: "imap_atSource O2 I"
shows "imap_downstream O2 (imap_downstream O1 I) = imap_downstream O1 (imap_downstream O2 I)"    
proof (cases O1)
  case (Create f1 n1)
  assume C1: "O1 = Create f1 n1"
  then show ?thesis 
    proof (cases O2)
      case (Create f2 n2)
      then show ?thesis using C1 comm_create_create O1pre O2pre by simp
    next
      case (Delete f2 R)
      then show ?thesis using C1 comm_create_delete O1pre O2pre by simp
    next
      case (Append f2 m)
      then show ?thesis using C1 comm_create_append O1pre O2pre by simp
    next
      case (Store f2 mo mn)
      then show ?thesis using C1 comm_create_store O1pre O2pre by simp
    qed
next
  case (Delete f1 R1)
  assume C2: "O1 = Delete f1 R1"
  then show ?thesis
    proof (cases O2)
      case (Create f2 n)
      then show ?thesis using C2 comm_create_delete[of f1 R1 I f2 n] O1pre O2pre by simp
    next
      case (Delete f2 R2)
      then show ?thesis using C2 comm_delete_delete O1pre O2pre by simp
    next
      case (Append f2 m)
      then show ?thesis using C2 comm_delete_append O1pre O2pre by simp
    next
      case (Store f2 mo mn)
      then show ?thesis using C2 comm_delete_store O1pre O2pre by simp
    qed
next
  case (Append f1 m1)
  assume C3: "O1 = Append f1 m1"
  then show ?thesis
    proof (cases O2)
      case (Create f2 n)
      then show ?thesis using C3 comm_create_append[of f1 m1 I f2 n] O1pre O2pre by simp
    next
      case (Delete f2 R)
      then show ?thesis using C3 comm_delete_append[of f1 m1 I f2 R] O1pre O2pre by simp
    next
      case (Append f2 m2)
      then show ?thesis using C3 comm_append_append O1pre O2pre by simp
    next
      case (Store f2 mo mn)
      then show ?thesis using C3 comm_append_store O1pre O2pre by simp
    qed
next
  case (Store f1 mo1 mn1)
  assume C4: "O1 = Store f1 mo1 mn1"
  then show ?thesis
    proof (cases O2)
      case (Create f2 n)
      then show ?thesis using C4 comm_create_store[of f1 mo1 mn1 I f2 n] O1pre O2pre by simp
    next
      case (Delete f2 R)
      then show ?thesis using C4 comm_delete_store[of f1 mo1 mn1 I f2 R] O1pre O2pre by simp
    next
      case (Append f2 m2)
      then show ?thesis using C4 comm_append_store[of f1 mo1 mn1 I f2 m2] O1pre O2pre by simp
    next
      case (Store f2 mo mn)
      then show ?thesis using C4 comm_store_store O1pre O2pre by simp
    qed
qed
  
-- "###############################################"
-- "### TODO ###"
-- "###############################################"

-- "Case 5"
lemma commCREATE_EXPUNGE:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m :: "'b" and
  n :: nat
assumes
  O1pre: " EXPUNGE_atSource f1 m I" and
  O2pre: " create_pre f2 n I"
shows "EXPUNGE_downstream f1 m (create f2 n I) = create f2 n (EXPUNGE_downstream f1 m I)"
proof -
  have A1: "folderset (EXPUNGE_downstream f1 m (create f2 n I)) = folderset (create f2 n (EXPUNGE_downstream f1 m I))"
  unfolding create_def EXPUNGE_downstream_def
  by simp

  have "filesystem (EXPUNGE_downstream f1 m (create f2 n I)) = filesystem (create f2 n (EXPUNGE_downstream f1 m I))"
  using O1pre O2pre
  unfolding EXPUNGE_atSource_def EXPUNGE_downstream_def create_pre_def create_def
  by (simp add: fun_upd_twist option.case_eq_if)

  thus ?thesis
  using A1 prod_eqI
  by blast
qed
  
-- "Case 9"
lemma commDELETE_EXPUNGE:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m :: "'b" and
  R :: "'a orset"
assumes
  O1pre: " EXPUNGE_atSource f1 m I" and
  O2pre: " delete_pre f2 R I"
shows "EXPUNGE_downstream f1 m (delete f2 R I) = delete f2 R (EXPUNGE_downstream f1 m I)"
proof -
  have A1: "folderset(EXPUNGE_downstream f1 m (delete f2 R I)) = folderset (delete f2 R (EXPUNGE_downstream f1 m I))"
  unfolding delete_def EXPUNGE_downstream_def
  by simp

  have "filesystem(EXPUNGE_downstream f1 m (delete f2 R I)) = filesystem (delete f2 R (EXPUNGE_downstream f1 m I))"
  using O1pre O2pre
  unfolding EXPUNGE_atSource_def EXPUNGE_downstream_def delete_pre_def delete_def msgLookup_def
  by (simp add: fun_upd_twist option.case_eq_if)

  thus ?thesis
  using A1 prod_eqI
  by blast
qed

-- "Case 12"
lemma commAPPEND_EXPUNGE:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m1 :: "'b" and
  m2 :: "'b"
assumes
  O1pre: "EXPUNGE_atSource f1 m1 I" and
  O2pre: "append_pre f2 m2 I"
shows "EXPUNGE_downstream f1 m1 (append f2 m2 I) = append f2 m2 (EXPUNGE_downstream f1 m1 I)"
proof -
  have A1: "folderset (EXPUNGE_downstream f1 m1 (append f2 m2 I)) = folderset (append f2 m2 (EXPUNGE_downstream f1 m1 I))"
  unfolding EXPUNGE_downstream_def append_def
  by simp

  have "filesystem (EXPUNGE_downstream f1 m1 (append f2 m2 I)) = filesystem (append f2 m2 (EXPUNGE_downstream f1 m1 I))"
  using O1pre O2pre
  unfolding EXPUNGE_downstream_def EXPUNGE_atSource_def append_def append_pre_def
  by (smt Diff_empty Diff_insert0 Un_Diff case_prod_beta' fun_upd_apply fun_upd_twist fun_upd_upd insert_Diff insert_Diff1 map_upd_eqD1 mk_disjoint_insert msgLookup_def option.case_eq_if option.collapse option.simps(3) singletonI snd_conv)

  thus ?thesis
  using A1 prod_eqI
  by blast
qed

-- "Case 14"
lemma commSTORE_EXPUNGE:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m :: "'b" and
  mo :: "'b" and
  mn :: "'b"
assumes
  O1pre: "EXPUNGE_atSource f1 m1 I" and
  O2pre: "store_pre f2 mo mn I"
shows "EXPUNGE_downstream f1 m1 (store f2 mo mn I) = store f2 mo mn (EXPUNGE_downstream f1 m1 I)"
proof -
  have A1: "folderset (EXPUNGE_downstream f1 m1 (store f2 mo mn I)) = folderset (store f2 mo mn (EXPUNGE_downstream f1 m1 I))"
  unfolding EXPUNGE_downstream_def store_def
  by simp

  have A2: "\<forall> f . f1 \<noteq> f2 \<longrightarrow> filesystem (EXPUNGE_downstream f1 m1 (store f2 mo mn I)) f = filesystem (store f2 mo mn (EXPUNGE_downstream f1 m1 I)) f"
  using O1pre O2pre
  unfolding EXPUNGE_downstream_def EXPUNGE_atSource_def store_def store_pre_def
  by (smt fun_upd_other fun_upd_twist option.case_eq_if snd_conv)

  have A3: "\<forall> f . (f1 = f2 \<and> f \<noteq> f1) \<longrightarrow> filesystem (EXPUNGE_downstream f1 m1 (store f2 mo mn I)) f = filesystem (store f2 mo mn (EXPUNGE_downstream f1 m1 I)) f"
  using O1pre O2pre
  unfolding EXPUNGE_downstream_def EXPUNGE_atSource_def store_def store_pre_def
  by (smt fun_upd_other fun_upd_twist option.case_eq_if snd_conv)

  have "f1 = f2 \<longrightarrow> filesystem (EXPUNGE_downstream f1 m1 (store f2 mo mn I)) f1 = filesystem (store f2 mo mn (EXPUNGE_downstream f1 m1 I)) f1"
  using O1pre O2pre
  unfolding EXPUNGE_downstream_def EXPUNGE_atSource_def store_def store_pre_def msgLookup_def Msg_def
  by (smt Diff_empty Diff_insert Diff_insert0 Un_Diff empty_iff fun_upd_same insertE insert_commute map_upd_eqD1 option.case_eq_if option.collapse option.simps(3) snd_conv)

  hence "filesystem (EXPUNGE_downstream f1 m1 (store f2 mo mn I)) = filesystem (store f2 mo mn (EXPUNGE_downstream f1 m1 I))"
  using O1pre O2pre A2 A3
  unfolding EXPUNGE_downstream_def EXPUNGE_atSource_def store_def store_pre_def
  by fastforce

  thus ?thesis
  using A1 prod_eqI
  by blast
qed


-- "Case 15"
lemma commEXPUNGE_EXPUNGE:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m1 :: "'b" and
  m2 :: "'b"
assumes
  O1pre: " EXPUNGE_atSource f1 m1 I" and
  O2pre: " EXPUNGE_atSource f2 m2 I"
shows "EXPUNGE_downstream f1 m1 (EXPUNGE_downstream f2 m2 I) = EXPUNGE_downstream f2 m2 (EXPUNGE_downstream f1 m1 I)"
proof -
  have A1: "folderset (EXPUNGE_downstream f1 m1 (EXPUNGE_downstream f2 m2 I)) = folderset (EXPUNGE_downstream f2 m2 (EXPUNGE_downstream f1 m1 I))"
  unfolding EXPUNGE_downstream_def EXPUNGE_atSource_def
  by simp

  have "filesystem (EXPUNGE_downstream f1 m1 (EXPUNGE_downstream f2 m2 I)) = filesystem (EXPUNGE_downstream f2 m2 (EXPUNGE_downstream f1 m1 I))"
  using O1pre O2pre
  unfolding EXPUNGE_downstream_def EXPUNGE_atSource_def msgLookup_def
  by (smt Diff_insert fun_upd_twist fun_upd_upd insert_commute map_upd_Some_unfold option.case_eq_if option.collapse option.simps(3) snd_conv)

  thus ?thesis
  using A1
  by (simp add: prod_eqI)
qed



end
