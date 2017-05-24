theory IMAP
imports ORSet
	
begin
	
(* 'a is the set of all foldernames, 'b is the set of all messagenames  *)
type_synonym ('a, 'b) imap = "'a orset \<times> ('a \<rightharpoonup> 'b set)"
	
abbreviation folderset ::
  "('a, 'b) imap \<Rightarrow> 'a orset" 
where
  "folderset I \<equiv> fst I"
  
abbreviation filesystem ::
  "('a, 'b) imap \<Rightarrow> ('a \<rightharpoonup> 'b set)"
where
  "filesystem I \<equiv> snd I"
  
(*State Invariants*)
definition validState ::
	"('a,'b) imap \<Rightarrow> bool"
	where
	"validState I = ((\<forall> (a,_) \<in> folderset I . (filesystem I) a \<noteq> None)
	\<and> (\<forall> f . (filesystem I) f \<noteq> None \<longrightarrow> (\<exists> (a,_) \<in> folderset I . a = f)))"
  
definition CREATE_atSource ::
	"'a \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
	"CREATE_atSource f I = (\<nexists> n . (f,n) \<in> folderset I)"
  
definition CREATE_downstream ::
	"'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
	"CREATE_downstream f n I = (add f n (folderset I), (filesystem I)(f := Some {}))"
	
(*computes the R set for a mailbox*)
definition DELETE_atSource ::
	"'a \<Rightarrow> ('a, 'b) imap \<Rightarrow> 'a orset"
	where
	"DELETE_atSource e I = remove_atSource e (folderset I)"
	
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

(*rewrite filesystem with option type?*)
  
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
	validS: "validState I" and
	Delpre: "DELETE_atSource_pre e1 I"
shows "validState (DELETE_downstream e1 R I)"
proof -
	have "filesystem (DELETE_downstream e1 R I) e1 = None " unfolding DELETE_downstream_def by simp
	have "\<forall> f. f \<noteq> e1 \<longrightarrow> (filesystem I) f = (filesystem (DELETE_downstream e1 R I)) f" unfolding DELETE_downstream_def by auto
  have A1: "\<forall> (a,b) \<in> folderset I. a \<noteq> e1 \<longrightarrow> (a,b) \<in> folderset (DELETE_downstream e1 R I)"	
  	using O1pre unfolding DELETE_downstream_def remove_downstream_def DELETE_atSource_def remove_atSource_def by auto
  have "\<forall> (a,_) \<in> folderset (DELETE_downstream e1 R I). a \<noteq> e1" using O1pre 
  	unfolding DELETE_downstream_def remove_downstream_def DELETE_atSource_def remove_atSource_def by auto
  hence "(\<forall> (a,_) \<in> folderset (DELETE_downstream e1 R I) . (filesystem (DELETE_downstream e1 R I)) a \<noteq> None)" using A1 O1pre validS
  	unfolding validState_def  DELETE_downstream_def remove_downstream_def DELETE_atSource_def remove_atSource_def by fastforce
  
	thus ?thesis using O1pre validS Delpre A1 unfolding validState_def DELETE_atSource_def DELETE_downstream_def remove_atSource_def 
		remove_downstream_def apply simp by blast
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
	
end
	