section {* IMAP Proof *}

theory IMAP_proof
imports IMAP_def ORSet_proof
begin

text {* 
  We begin by showing auxiliary lemmas that simplify further proofs. The lemma 
  @{term append_not_none} shows that an append operation on a valid imap state never leads to an 
  undefined filesystem state.
*}
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

text {* 
  The lemma @{term append_folderset} shows the folderset is not modified by an append operation.
*}
lemma append_folderset:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a" and
  m :: "'b"
shows "folderset (append f m I) = folderset I"
proof -
  show ?thesis unfolding append_def by auto
qed

text {* 
  The lemma @{term append_filesytem} shows that an append operation only modifies the filesystem 
  entry for the selected folder.
*}
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
  show ?thesis by (simp add: append_def option.case_eq_if)
qed

text {* 
  The lemma @{term store_folderset} shows that a store operation does not modify the folderset.
*}
lemma store_folderset:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a"
shows "folderset (store f msgold msgnew I) = folderset I"
proof -
  show ?thesis by (simp add: store_def)
qed

text {* 
  Similar to the lemma @{term  append_filesystem}, the lemma @{term store_folderset} shows that 
  a store operation only modifies the filesystem state for the selected folder.
*}
lemma store_filesystem:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a"
shows "\<forall> f. f \<noteq> f1 \<longrightarrow> filesystem (store f1 msgold msgnew I) f = filesystem I f"
proof -
  show ?thesis by (simp add: store_def option.case_eq_if)
qed

text {* 
  The lemma @{term store_not_none} shows that a store operation never results in an undefined 
  filesystem state.
*}
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

subsection {* State Validity *}
	
text {* 
  With the following lemmas we show, that each operation on the imap datatype that is executed on
  a valid state also results in a valid state. We show this property for all defined operations.
*}
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

  hence "(\<forall> (a, _) \<in> folderset (delete e1 R I) . (filesystem (delete e1 R I)) a \<noteq> None)" 
    using validS
    unfolding validState_def delete_def remove_def delete_pre_def remove_pre_def
    by fastforce

  thus ?thesis
    using validS A1
    unfolding validState_def delete_pre_def delete_def remove_def remove_pre_def
    by (simp, blast)
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
    by (simp add: option.case_eq_if, auto)
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
    unfolding store_def store_pre_def msgLookup_def msgReplace_def
    by (simp add: case_prod_beta' fun_upd_same option.case_eq_if validState_def)
qed

lemma expunge_valid:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a" and
  m :: "'b"
assumes
  O1pre: "expunge_pre f m I" and
  validS: "validState I"
shows "validState (expunge f m I)"
proof -
  show ?thesis
    using O1pre validS
    unfolding expunge_pre_def expunge_def msgLookup_def validState_def
    by (simp add: case_prod_beta' option.case_eq_if)
qed

subsection {*Operation Commutativity *}

text {* 
  With the following lemmas we show, that each combination of operations is commutative. From the 
  5 imap operations we derive 15 cases and show each case individually. Note that every lemma only
  uses the atSource precondition of the corresponding operation and that no further assumptions are
  made.
*}
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
    unfolding append_pre_def append_def create_pre_def create_def lookup_def 
    by (simp add: option.case_eq_if, auto)
  thus ?thesis by (simp add: append_def create_def)
qed

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
    by (simp add: option.case_eq_if, auto)
  thus ?thesis by (simp add: A1 prod.expand)
qed

lemma comm_create_expunge:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m :: "'b" and
  n :: nat
assumes
  O1pre: "expunge_pre f1 m I" and
  O2pre: "create_pre f2 n I"
shows "expunge f1 m (create f2 n I) = create f2 n (expunge f1 m I)"
proof -
  have A1: "folderset (expunge f1 m (create f2 n I)) = folderset (create f2 n (expunge f1 m I))"
    by (simp add: create_def expunge_def)
  have "filesystem (expunge f1 m (create f2 n I)) = filesystem (create f2 n (expunge f1 m I))"
    using O1pre O2pre
    unfolding expunge_pre_def expunge_def create_pre_def create_def
    by (simp add: fun_upd_twist option.case_eq_if)
  thus ?thesis using A1 prod_eqI by blast
qed

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

lemma comm_delete_expunge:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m :: "'b" and
  R :: "'a orset"
assumes
  O1pre: " expunge_pre f1 m I" and
  O2pre: " delete_pre f2 R I"
shows "expunge f1 m (delete f2 R I) = delete f2 R (expunge f1 m I)"
proof -
  have A1: "folderset(expunge f1 m (delete f2 R I)) = folderset (delete f2 R (expunge f1 m I))"
    by (simp add: delete_def expunge_def)
  have "filesystem(expunge f1 m (delete f2 R I)) = filesystem (delete f2 R (expunge f1 m I))"
    using O1pre O2pre
    unfolding expunge_pre_def expunge_def delete_pre_def delete_def msgLookup_def
    by (simp add: fun_upd_twist option.case_eq_if)
  thus ?thesis
    using A1 prod_eqI
    by blast
qed

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
    by (simp add: option.case_eq_if, auto)
  thus ?thesis using A1 by (simp add: prod_eq_iff)
qed

lemma comm_append_store:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  mo :: "'b" and
  mn :: "'b" and
  m :: "'b"
assumes
  O1pre: "store_pre f1 mo mn I" and
  O2pre: "append_pre f2 m I"
shows "store f1 mo mn (append f2 m I) = append f2 m (store f1 mo mn I)"
proof -
  have A1: "folderset (store f1 mo mn (append f2 m I)) = folderset (append f2 m (store f1 mo mn I))"
    by (simp add: append_def store_folderset)
  have "filesystem (store f1 mo mn (append f2 m I)) = filesystem(append f2 m (store f1 mo mn I))"
    using O1pre O2pre unfolding store_def append_def append_pre_def store_pre_def msgReplace_def
    by (simp add: option.case_eq_if, auto)
  thus ?thesis using A1 by (simp add: prod.expand)
qed

lemma comm_append_expunge:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m1 :: "'b" and
  m2 :: "'b"
assumes
  O1pre: "expunge_pre f1 m1 I" and
  O2pre: "append_pre f2 m2 I"
shows "expunge f1 m1 (append f2 m2 I) = append f2 m2 (expunge f1 m1 I)"
proof -
  have A1: "folderset (expunge f1 m1 (append f2 m2 I)) = folderset (append f2 m2 (expunge f1 m1 I))"
    unfolding expunge_def append_def
    by simp
  have "filesystem (expunge f1 m1 (append f2 m2 I)) = filesystem (append f2 m2 (expunge f1 m1 I))"
    using O1pre O2pre
    unfolding expunge_def expunge_pre_def append_def append_pre_def
    by (simp add: option.case_eq_if, auto)
  thus ?thesis using A1 prod_eqI by blast
qed

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
    by (simp add: option.case_eq_if store_def, auto)
  have "f1 = f2 \<longrightarrow> filesystem (store f1 mo1 mn1 (store f2 mo2 mn2 I)) f1 = filesystem(store f2 mo2 mn2 (store f1 mo1 mn1 I)) f1"
  proof auto
    assume Ass: "f1 = f2"
    hence "filesystem (store f1 mo1 mn1 (store f2 mo2 mn2 I)) f1 \<noteq> None"
      using O2pre store_not_none[of f2 mo2 mn2 I]
      by (simp add: option.case_eq_if store_def)
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
      unfolding store_def msgReplace_def
      by simp
    hence Ass6: "y = (S - {mo1,mo2}) \<union> {mn1,mn2}"
      using Ass Ass2 Ass3 Ass4 O1pre O2pre
      unfolding store_def msgReplace_def store_pre_def
      by auto
    have "\<exists> w . filesystem (store f1 mo1 mn1 I) f1 = Some w"
      using Ass
      by (metis O1pre option.collapse store_not_none)
    then obtain w where Ass8: "filesystem (store f1 mo1 mn1 I) f1 = Some w"
      by blast
    hence Ass9: "w = (S - {mo1}) \<union> {mn1}"
      using Ass Ass2
      unfolding store_def msgReplace_def
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
      unfolding store_def msgReplace_def store_pre_def
      by auto
    thus "filesystem (store f2 mo1 mn1 (store f2 mo2 mn2 I)) f2 = filesystem (store f2 mo2 mn2 (store f2 mo1 mn1 I)) f2"
      using Ass7 Ass4 Ass6 Ass
      by auto
  qed
  thus ?thesis
    using A1 A2 O1pre O2pre
    by (simp add: store_def option.case_eq_if, auto)
qed

lemma comm_store_expunge:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m :: "'b" and
  mo :: "'b" and
  mn :: "'b"
assumes
  O1pre: "expunge_pre f1 m1 I" and
  O2pre: "store_pre f2 mo mn I"
shows "expunge f1 m1 (store f2 mo mn I) = store f2 mo mn (expunge f1 m1 I)"
proof -
  have A1: "folderset (expunge f1 m1 (store f2 mo mn I)) = folderset (store f2 mo mn (expunge f1 m1 I))"
    by (simp add: expunge_def store_def)
  have A2: "\<forall> f . f1 \<noteq> f2 \<longrightarrow> filesystem (expunge f1 m1 (store f2 mo mn I)) f = filesystem (store f2 mo mn (expunge f1 m1 I)) f"
    using O1pre O2pre
    unfolding expunge_def expunge_pre_def store_def store_pre_def
    by (simp add: option.case_eq_if, auto)
  have A3: "\<forall> f . (f1 = f2 \<and> f \<noteq> f1) \<longrightarrow> filesystem (expunge f1 m1 (store f2 mo mn I)) f = filesystem (store f2 mo mn (expunge f1 m1 I)) f"
    using O1pre O2pre
    unfolding expunge_def expunge_pre_def store_def store_pre_def
    by (simp add: option.case_eq_if)
  have "f1 = f2 \<longrightarrow> filesystem (expunge f1 m1 (store f2 mo mn I)) f1 = filesystem (store f2 mo mn (expunge f1 m1 I)) f1"
    using O1pre O2pre
    unfolding expunge_def expunge_pre_def store_def store_pre_def msgLookup_def msgReplace_def
    by (simp add: option.case_eq_if, auto)
  hence "filesystem (expunge f1 m1 (store f2 mo mn I)) = filesystem (store f2 mo mn (expunge f1 m1 I))"
    using O1pre O2pre A2 A3
    unfolding expunge_def expunge_pre_def store_def store_pre_def
    by fastforce
  thus ?thesis using A1 prod_eqI by blast
qed

lemma comm_expunge_expunge:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m1 :: "'b" and
  m2 :: "'b"
assumes
  O1pre: " expunge_pre f1 m1 I" and
  O2pre: " expunge_pre f2 m2 I"
shows "expunge f1 m1 (expunge f2 m2 I) = expunge f2 m2 (expunge f1 m1 I)"
proof -
  have A1: "folderset (expunge f1 m1 (expunge f2 m2 I)) = folderset (expunge f2 m2 (expunge f1 m1 I))"
    unfolding expunge_def expunge_pre_def
    by simp
  have "filesystem (expunge f1 m1 (expunge f2 m2 I)) = filesystem (expunge f2 m2 (expunge f1 m1 I))"
    using O1pre O2pre
    unfolding expunge_def expunge_pre_def msgLookup_def
    by (simp add: option.case_eq_if, auto)
  thus ?thesis using A1 by (simp add: prod_eqI)
qed

subsection {* Theorem *}

text {* 
  We propose the final theorem, showing that all combinations of operations on the imap datatype
  are commutative. For each operation we assume, that the atSource precondition holds for the 
  current state @{term I}. We show each case individually using the previously defined 
  commutativity lemmas.
*}
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
    next
      case (Expunge f2 m)
      then show ?thesis using C1 comm_create_expunge O1pre O2pre by simp
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
    next
      case (Expunge f2 m)
      then show ?thesis using C2 comm_delete_expunge O1pre O2pre by simp
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
    next
      case (Expunge f2 m)
      then show ?thesis using C3 comm_append_expunge O1pre O2pre by simp
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
    next
      case (Expunge f2 m)
      then show ?thesis using C4 comm_store_expunge O1pre O2pre by simp
    qed
next
  case (Expunge f1 m1)
  assume C5: "O1 = Expunge f1 m1"
  then show ?thesis
    proof (cases O2)
      case (Create f2 n)
      then show ?thesis using C5 comm_create_expunge[of f1 m1 I f2 n] O1pre O2pre by simp
    next
      case (Delete f2 R)
      then show ?thesis using C5 comm_delete_expunge[of f1 m1 I f2 R] O1pre O2pre by simp
    next
      case (Append f2 m2)
      then show ?thesis using C5 comm_append_expunge[of f1 m1 I f2 m2] O1pre O2pre by simp
    next
      case (Store f2 mo mn)
      then show ?thesis using C5 comm_store_expunge[of f1 m1 I f2 mo mn] O1pre O2pre by simp
    next
      case (Expunge f2 m)
      then show ?thesis using C5 comm_expunge_expunge O1pre O2pre by simp
    qed
qed

end
