theory IMAP
imports ORSet
	
begin
	
-- "Type defeinition: 'a is the set of all foldernames, 'b is the set of all messagenames"
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
	"('a,'b) imap \<Rightarrow> bool"
	where
	"validState I = ((\<forall> (a,_) \<in> folderset I . (filesystem I) a \<noteq> None)
	\<and> (\<forall> f . (filesystem I) f \<noteq> None \<longrightarrow> (\<exists> (a,_) \<in> folderset I . a = f)))"
	
definition replaceMsg ::
	"'b \<Rightarrow> 'b \<Rightarrow> 'b set \<Rightarrow> 'b set"
where
	"replaceMsg msgold msgnew S = (S - {msgold}) \<union> {msgnew}"

definition msgLookup ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "msgLookup f msg I = (case (filesystem I)(f) of 
			None \<Rightarrow> False | 
			Some msgset \<Rightarrow> msg \<in> msgset)"

-- "######### BEGIN OPERATIONS ##########"

definition CREATE_atSource ::
	"'a \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
	"CREATE_atSource f I = (\<nexists> n . (f,n) \<in> folderset I)"
  
definition CREATE_downstream ::
	"'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
	"CREATE_downstream f n I = (add f n (folderset I), (filesystem I)(f := Some {}))"

definition DELETE_atSource ::
	"'a \<Rightarrow> ('a, 'b) imap \<Rightarrow> 'a orset"
	where
	"DELETE_atSource e I = remove_atSource e (folderset I)"

-- "unused"
definition DELETE_atSource_pre ::
	"'a \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
	where
	"DELETE_atSource_pre e I = (\<exists> (a,_) \<in> folderset I . a = e)"

definition DELETE_downstream ::
	"'a \<Rightarrow> 'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
	where
	"DELETE_downstream e R I = (remove_downstream R (folderset I), (filesystem I)(e := None))"	
	
definition APPEND_atSource ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "APPEND_atSource f m I = (\<exists> (a,_) \<in> folderset I . a = f)"

definition APPEND_downstream ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "APPEND_downstream f m I = 
	(folderset I, 
		(case (filesystem I)(f) of 
			None \<Rightarrow> filesystem I | 
			Some msgset \<Rightarrow> (filesystem I)(f := Some (msgset \<union> {m})))
	)"
	
definition STORE_atSource ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "STORE_atSource f msgold msgnew I = ((\<exists> (a,_) \<in> folderset I . a = f) \<and> msgLookup f msgold I \<and> \<not>(msgLookup f msgnew I))"
	
definition STORE_downstream ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "STORE_downstream f msgold msgnew I = 
	(folderset I, 
		(case (filesystem I)(f) of 
			None \<Rightarrow> filesystem I | 
			Some msgset \<Rightarrow> (filesystem I)(f := Some (replaceMsg msgold msgnew msgset)))
	)"
	
-- "########## END OPERATIONS ##########"

-- "####### BEGIN HELPING LEMMAS #######"

lemma append_not_none:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  m1 :: "'b"
assumes
	O1pre: " APPEND_atSource f1 m1 I" and
	validS: "validState I"
shows "filesystem (APPEND_downstream f1 m1 I) f1 \<noteq> None"
proof -
	have "filesystem I f1 \<noteq> None" using O1pre validS unfolding validState_def APPEND_atSource_def by auto

	thus ?thesis using validS O1pre unfolding APPEND_downstream_def validState_def APPEND_atSource_def by auto
qed
  
lemma append_folderset:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a" and
  m :: "'b"
shows "folderset (APPEND_downstream f m I) = folderset I"
proof -
	show ?thesis unfolding APPEND_downstream_def by auto
qed
	
lemma append_filesystem:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  m1 :: "'b"
assumes
	O1pre: " APPEND_atSource f1 m1 I" and
	validS: "validState I"
shows "\<forall> f . f \<noteq> f1 \<longrightarrow> filesystem (APPEND_downstream f1 m1 I) f = filesystem I f"
proof (simp add: APPEND_downstream_def option.case_eq_if)
qed

lemma store_folderset:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a"
shows "folderset (STORE_downstream f msgold msgnew I) = folderset I"
proof -
	show ?thesis unfolding STORE_downstream_def by auto
qed

lemma store_filesystem:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a"
shows "\<forall> f. f \<noteq> f1 \<longrightarrow> filesystem (STORE_downstream f1 msgold msgnew I) f = filesystem I f"
proof -
	show ?thesis unfolding STORE_downstream_def by (simp add: option.case_eq_if)
qed
  
lemma store_not_none:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  msgold :: "'b" and
  msgnew :: "'b"
assumes
  pre: "STORE_atSource f1 msgold msgnew I"
shows "filesystem (STORE_downstream f1 msgold msgnew I) f1 \<noteq> None"
proof -
	show ?thesis using pre unfolding STORE_downstream_def STORE_atSource_def msgLookup_def
	  by (metis fun_upd_same option.case_eq_if option.simps(3) snd_conv)
qed


-- "######## END HELPING LEMMAS ########"

-- "###### BEGIN VALIDITY LEMMAS #######"

lemma append_valid:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  m1 :: "'b"
assumes
	O1pre: " APPEND_atSource f1 m1 I" and
	validS: "validState I"
shows "validState (APPEND_downstream f1 m1 I)"
proof -
	have "folderset (APPEND_downstream f1 m1 I) = folderset I" unfolding APPEND_downstream_def by auto
	hence "(\<forall>f. filesystem (APPEND_downstream f1 m1 I) f \<noteq> None \<longrightarrow> (\<exists>(a,_)\<in>folderset (APPEND_downstream f1 m1 I). a = f))"
		by (metis APPEND_atSource_def O1pre validS validState_def append_filesystem)			
	thus ?thesis using O1pre validS unfolding validState_def APPEND_downstream_def apply simp
		by (smt case_prodE fun_upd_apply old.prod.case option.case_eq_if)
qed
	
lemma delete_valid:
fixes
  I :: "('a, 'b) imap" and
  R :: "'a orset" and
  e1 :: "'a"
assumes
	O1pre: "R = DELETE_atSource e1 I" and
	validS: "validState I"
shows "validState (DELETE_downstream e1 R I)"
proof -
  have A1: "\<forall> (a,b) \<in> folderset I. a \<noteq> e1 \<longrightarrow> (a,b) \<in> folderset (DELETE_downstream e1 R I)"	
  	using O1pre unfolding DELETE_downstream_def remove_downstream_def DELETE_atSource_def remove_atSource_def by auto
  have "\<forall> (a,_) \<in> folderset (DELETE_downstream e1 R I). a \<noteq> e1" using O1pre 
  	unfolding DELETE_downstream_def remove_downstream_def DELETE_atSource_def remove_atSource_def by auto
  hence "(\<forall> (a,_) \<in> folderset (DELETE_downstream e1 R I) . (filesystem (DELETE_downstream e1 R I)) a \<noteq> None)" using validS
  	unfolding validState_def  DELETE_downstream_def remove_downstream_def DELETE_atSource_def remove_atSource_def by fastforce
	thus ?thesis using validS A1 unfolding validState_def DELETE_atSource_def DELETE_downstream_def remove_atSource_def 
		remove_downstream_def apply simp by blast
qed
  
lemma create_valid:
fixes
  I :: "('a, 'b) imap" and
  e :: "'a" and
  n :: nat
assumes
	validS: "validState I"
shows "validState (CREATE_downstream e n I)"
proof -
  show ?thesis using validS unfolding CREATE_downstream_def add_def validState_def CREATE_atSource_def apply simp 
    by (simp add: split_def)
qed
  
lemma store_valid:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a" and
  msgold :: "'b" and
  msgnew :: "'b"
assumes
	validS: "validState I"
shows "validState (STORE_downstream f msgold msgnew I)"
proof -
  show ?thesis sorry
qed

-- "####### END VALIDITY LEMMAS ########"  

-- "####### BEGIN COMMUTATIVITY ########"  

lemma commCREATE:
fixes
  I :: "('a,'b) imap" and
  e1 :: "'a" and
  e2 :: "'a" and
  n1 :: nat and
  n2 :: nat
assumes
	n1neqn2: "n1 \<noteq> n2"
shows 
	"CREATE_downstream e1 n1 (CREATE_downstream e2 n2 I) = CREATE_downstream e2 n2 (CREATE_downstream e1 n1 I)"
proof -
	show ?thesis unfolding CREATE_downstream_def using commAdd n1neqn2 by fastforce
qed
	
lemma commDELETE:
fixes
  I :: "('a, 'b) imap" and
  R1 :: "'a orset" and
  R2 :: "'a orset" and
  e1 :: "'a" and
  e2 :: "'a"
assumes 
  O1R1: " R1 = DELETE_atSource e1 I" and
  O2R2: " R2 = DELETE_atSource e2 I"
shows "DELETE_downstream e2 R2 (DELETE_downstream e1 R1 I) = DELETE_downstream e1 R1 (DELETE_downstream e2 R2 I)"
proof -
	show ?thesis using O1R1 O2R2 commRemove unfolding DELETE_downstream_def DELETE_atSource_def remove_atSource_def apply simp
	proof -
		assume a1: "R1 = {(a, b). (a, b) \<in> folderset I \<and> a = e1}"
		assume a2: "R2 = {(a, b). (a, b) \<in> folderset I \<and> a = e2}"
		have f3: "\<forall>P a Pa Pb aa. (P \<noteq> remove_atSource (a::'a) Pa \<or> Pb \<noteq> remove_atSource aa Pa) \<or> remove_downstream Pb (remove_downstream P Pa) = remove_downstream P (remove_downstream Pb Pa)"
			by (meson commRemove)
		have f4: "{(a, n). (a, n) \<in> folderset I \<and> a = e1} = remove_atSource e1 (folderset I)"
			using a1 by (simp add: DELETE_atSource_def O1R1)
		have "{(a, n). (a, n) \<in> folderset I \<and> a = e2} = remove_atSource e2 (folderset I)"
			using a2 by (simp add: DELETE_atSource_def O2R2)
		then show "remove_downstream {(a, n). (a, n) \<in> folderset I \<and> a = e2} (remove_downstream {(a, n). (a, n) \<in> folderset I \<and> a = e1} (folderset I)) = remove_downstream {(a, n). (a, n) \<in> folderset I \<and> a = e1} (remove_downstream {(a, n). (a, n) \<in> folderset I \<and> a = e2} (folderset I)) \<and> (filesystem I)(e1 := None, e2 := None) = (filesystem I) (e2 := None, e1 := None)"
			using f4 f3 by auto
	qed
qed
  
lemma commAPPEND:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  m1 :: "'b" and
  m2 :: "'b"
assumes 
  O1pre: " APPEND_atSource f1 m1 I" and
  O2pre: " APPEND_atSource f2 m2 I" and
	freshm: "m1 \<noteq> m2" and
	validS: "validState I"
shows "APPEND_downstream f1 m1 (APPEND_downstream f2 m2 I) = APPEND_downstream f2 m2 (APPEND_downstream f1 m1 I)"
proof -
	have A1: "folderset(APPEND_downstream f1 m1 (APPEND_downstream f2 m2 I)) = folderset(APPEND_downstream f2 m2 (APPEND_downstream f1 m1 I))"
		by (simp add: APPEND_downstream_def)
		
	have "filesystem(APPEND_downstream f1 m1 (APPEND_downstream f2 m2 I)) = filesystem(APPEND_downstream f2 m2 (APPEND_downstream f1 m1 I))"
		using O1pre O2pre freshm validS unfolding APPEND_downstream_def APPEND_atSource_def validState_def apply (simp add: append_valid)
		by (smt Un_insert_left Un_insert_right case_prodE fun_upd_twist fun_upd_upd map_upd_Some_unfold option.case(2) prod.sel(2) prod.simps(2)) 
	thus ?thesis using A1	by (simp add: prod_eq_iff)
qed
  
lemma commSTORE:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  mo1 :: "'b" and
  mo2 :: "'b" and
  mn1 :: "'b" and
  mn2 :: "'b"
assumes 
  O1pre: " STORE_atSource f1 mo1 mn1 I" and
  O2pre: " STORE_atSource f2 mo2 mn2 I" 
shows "STORE_downstream f1 mo1 mn1 (STORE_downstream f2 mo2 mn2 I) = STORE_downstream f2 mo2 mn2 (STORE_downstream f1 mo1 mn1 I)"
proof -
  have A1: "folderset (STORE_downstream f1 mo1 mn1 (STORE_downstream f2 mo2 mn2 I)) = folderset(STORE_downstream f2 mo2 mn2 (STORE_downstream f1 mo1 mn1 I))"
    by (simp add: store_folderset)
  
  have  A5: "\<forall> f . f1 \<noteq> f2 \<longrightarrow> filesystem (STORE_downstream f1 mo1 mn1 (STORE_downstream f2 mo2 mn2 I)) f = filesystem(STORE_downstream f2 mo2 mn2 (STORE_downstream f1 mo1 mn1 I)) f"
    by (smt STORE_downstream_def fun_upd_twist option.case_eq_if snd_conv store_filesystem)
    
  have  "f1 = f2 \<longrightarrow> filesystem (STORE_downstream f1 mo1 mn1 (STORE_downstream f2 mo2 mn2 I)) f1 = filesystem(STORE_downstream f2 mo2 mn2 (STORE_downstream f1 mo1 mn1 I)) f1"
  proof auto
    assume Ass: "f1 = f2"
    hence  "filesystem (STORE_downstream f1 mo1 mn1 (STORE_downstream f2 mo2 mn2 I)) f1 \<noteq> None"
      by (smt O2pre STORE_downstream_def fun_upd_eqD fun_upd_triv option.case_eq_if option.simps(3) snd_conv store_not_none)
  
    hence "\<exists> y . filesystem (STORE_downstream f1 mo1 mn1 (STORE_downstream f2 mo2 mn2 I)) f1 = Some y"
      by simp
    
    then obtain y where Ass4: "filesystem (STORE_downstream f1 mo1 mn1 (STORE_downstream f2 mo2 mn2 I)) f1 = Some y" by blast
    
    have "\<exists> S . filesystem (I) f1 = Some S" by (metis O2pre STORE_atSource_def \<open>f1 = f2\<close> case_optionE msgLookup_def)
    then obtain S where Ass2: "(filesystem I) f1 = Some S" by blast
        
    have "\<exists> x . filesystem (STORE_downstream f2 mo2 mn2 I) f1 = Some x" using Ass by (metis O2pre option.collapse store_not_none) 
    then obtain x where Ass3: "filesystem (STORE_downstream f2 mo2 mn2 I) f1 = Some x" by blast
        
    have "x = (S - {mo2}) \<union> {mn2}" using Ass Ass2 Ass3 unfolding STORE_downstream_def replaceMsg_def  by simp    
        
    hence Ass6: "y = (S - {mo1,mo2}) \<union> {mn1,mn2}" using Ass Ass2 Ass3 Ass4 O1pre O2pre unfolding STORE_downstream_def replaceMsg_def STORE_atSource_def
      by auto
        
    have "\<exists> w . filesystem (STORE_downstream f1 mo1 mn1 I) f1 = Some w" using Ass by (metis O1pre option.collapse store_not_none)
    then obtain w where Ass8: "filesystem (STORE_downstream f1 mo1 mn1 I) f1 = Some w" by blast
        
    hence Ass9: "w = (S - {mo1}) \<union> {mn1}" using Ass Ass2 unfolding STORE_downstream_def replaceMsg_def by simp
        
    have "filesystem(STORE_downstream f2 mo2 mn2 (STORE_downstream f1 mo1 mn1 I)) f1 \<noteq> None" using O1pre 
        unfolding STORE_downstream_def using Ass Ass2 by auto
      
    hence "\<exists> z . filesystem(STORE_downstream f2 mo2 mn2 (STORE_downstream f1 mo1 mn1 I)) f1 = Some z"
      by simp
      
    then obtain z where Ass7: "filesystem(STORE_downstream f2 mo2 mn2 (STORE_downstream f1 mo1 mn1 I)) f1 = Some z" by blast
        
    hence "z = (S - {mo1,mo2}) \<union> {mn1,mn2}" using Ass Ass2 Ass9 Ass8 O1pre O2pre unfolding STORE_downstream_def replaceMsg_def STORE_atSource_def by auto
    
    thus "filesystem (STORE_downstream f2 mo1 mn1 (STORE_downstream f2 mo2 mn2 I)) f2 =
    filesystem (STORE_downstream f2 mo2 mn2 (STORE_downstream f2 mo1 mn1 I)) f2" using Ass7 Ass4 Ass6 Ass by auto
  qed
  thus ?thesis using A1 A5
    by (smt O1pre O2pre STORE_downstream_def fun_upd_same fun_upd_twist fun_upd_upd option.case_eq_if prod_eqI snd_conv store_not_none)
qed
  
lemma commCREATE_STORE:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  mo :: "'b" and
  mn :: "'b" and
  n :: nat
assumes 
  O1pre: " STORE_atSource f1 mo mn I" and
  O2pre: " CREATE_atSource f2 I"
shows "STORE_downstream f1 mo mn (CREATE_downstream f2 n I) = CREATE_downstream f2 n (STORE_downstream f1 mo mn I)"
proof - 
  have A1: "folderset (STORE_downstream f1 mo mn (CREATE_downstream f2 n I)) = folderset (CREATE_downstream f2 n (STORE_downstream f1 mo mn I))"
    by (simp add: CREATE_downstream_def store_folderset)
  have "filesystem (STORE_downstream f1 mo mn (CREATE_downstream f2 n I)) = filesystem (CREATE_downstream f2 n (STORE_downstream f1 mo mn I))"
    using O1pre O2pre unfolding STORE_downstream_def CREATE_downstream_def CREATE_atSource_def STORE_atSource_def
    by (smt case_prodE fun_upd_other fun_upd_twist option.case_eq_if snd_conv)
  thus ?thesis using A1 by (simp add: prod.expand)
qed
  
lemma commDELETE_STORE:
fixes
  I :: "('a, 'b) imap" and
  f1 :: "'a" and
  f2 :: "'a" and
  mo :: "'b" and
  mn :: "'b" and
  R :: "'a orset"
assumes 
  O1pre: " STORE_atSource f1 mo mn I" and
  O2pre: " R = DELETE_atSource f2 I"
shows "STORE_downstream f1 mo mn (DELETE_downstream f2 R I) = DELETE_downstream f2 R (STORE_downstream f1 mo mn I)"
proof - 
  have A1: "folderset (STORE_downstream f1 mo mn (DELETE_downstream f2 R I)) = folderset(DELETE_downstream f2 R (STORE_downstream f1 mo mn I))"
    by (simp add: DELETE_downstream_def store_folderset)
  have "filesystem (STORE_downstream f1 mo mn (DELETE_downstream f2 R I)) = filesystem(DELETE_downstream f2 R (STORE_downstream f1 mo mn I))"
    using O1pre O2pre unfolding STORE_downstream_def DELETE_downstream_def DELETE_atSource_def STORE_atSource_def
    by (simp add: fun_upd_twist option.case_eq_if)
  thus ?thesis using A1 by (simp add: prod.expand)
qed
      
lemma commCREATE_DELETE:
fixes
  I :: "('a, 'b) imap" and
  R1 :: "'a orset" and
  e1 :: "'a" and
  e2 :: "'a" and
  n :: nat
assumes 
  O1R1: " R1 = DELETE_atSource e1 I" and
	freshn: "fresh n (folderset I)" and
	O2pre: "CREATE_atSource e2 I" and
	lookupe1: "lookup e1 (folderset I)"
shows "DELETE_downstream e1 R1 (CREATE_downstream e2 n I) = CREATE_downstream e2 n (DELETE_downstream e1 R1 I)"
proof -
	have fset: "folderset (DELETE_downstream e1 R1 (CREATE_downstream e2 n I)) = folderset (CREATE_downstream e2 n (DELETE_downstream e1 R1 I))"
		using O1R1 freshn unfolding DELETE_downstream_def CREATE_downstream_def fresh_def commAddRemove 
		  DELETE_atSource_def remove_atSource_def remove_downstream_def add_def by auto		  
	have "filesystem (DELETE_downstream e1 R1 (CREATE_downstream e2 n I)) = filesystem (CREATE_downstream e2 n (DELETE_downstream e1 R1 I))" 
	  using O1R1 O2pre lookupe1 unfolding DELETE_downstream_def CREATE_downstream_def DELETE_atSource_def remove_atSource_def CREATE_atSource_def validState_def
		lookup_def by fastforce
	thus ?thesis using fset unfolding DELETE_downstream_def by auto
qed
  
lemma commCREATE_APPEND:
fixes
  I :: "('a, 'b) imap" and
  e :: "'a" and
  n :: nat and
  f :: "'a" and
  m :: "'b"
assumes 
  O1pre: " APPEND_atSource f m I" and
  O2pre: " CREATE_atSource e I"
shows "APPEND_downstream f m (CREATE_downstream e n I) = CREATE_downstream e n (APPEND_downstream f m I)"
proof -
  have "filesystem(APPEND_downstream f m (CREATE_downstream e n I)) = filesystem(CREATE_downstream e n (APPEND_downstream f m I))"
    using O1pre O2pre
    unfolding APPEND_atSource_def APPEND_downstream_def CREATE_atSource_def CREATE_downstream_def
    by (smt case_prodE fun_upd_apply fun_upd_twist option.case_eq_if prod.sel(2))
	thus ?thesis using append_folderset[of f m I] unfolding APPEND_downstream_def CREATE_downstream_def by auto
qed
  
lemma commDELETE_APPEND:
fixes
  I :: "('a, 'b) imap" and
  f :: "'a" and
  e :: "'a" and
  m :: "'b" and
  R :: "'a orset"
assumes 
  O1pre: " APPEND_atSource f m I" and
  O2pre: " R = DELETE_atSource e I" and
	validS: "validState I"
shows "APPEND_downstream f m (DELETE_downstream e R I) = DELETE_downstream e R (APPEND_downstream f m I)"
proof -
  have A1: "folderset(APPEND_downstream f m (DELETE_downstream e R I)) = folderset(DELETE_downstream e R (APPEND_downstream f m I))"
    unfolding DELETE_downstream_def by (simp add: append_folderset)
  have "filesystem(APPEND_downstream f m (DELETE_downstream e R I)) = filesystem(DELETE_downstream e R (APPEND_downstream f m I))"
    using O1pre O2pre unfolding APPEND_atSource_def APPEND_downstream_def DELETE_atSource_def DELETE_downstream_def 
    by (simp add: fun_upd_twist option.case_eq_if)
	thus ?thesis using A1 prod_eqI by blast
qed
  
-- "######## END COMMUTATIVITY #########"  
  
end
	