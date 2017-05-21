theory IMAP
imports ORSet
	
begin
	
(* 'a is the set of all foldernames, 'b is the set of all messagenames  *)
type_synonym ('a, 'b) imap = "'a orset \<times> ('a \<times> ('b \<times> 'b) orset) set"
	
abbreviation folderset :: 
  "('a, 'b) imap \<Rightarrow> 'a orset" 
where
  "folderset I \<equiv> fst I"
  
abbreviation filesystem :: 
  "('a, 'b) imap \<Rightarrow> ('a \<times> ('b \<times> 'b) orset) set" 
where
  "filesystem I \<equiv> snd I"
  
definition CREATE ::
	"'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
	"CREATE f n I = (add f n (folderset I), filesystem I \<union> {(f,{})})"
	
definition CREATE2 ::
	"'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
	"CREATE2 f n I = (add f n (folderset I), filesystem I)"
	
(*computes the R set for a mailbox*)
definition DELETE_atSource ::
	"'a \<Rightarrow> ('a, 'b) imap \<Rightarrow> 'a orset"
	where
	"DELETE_atSource e I = remove_atSource e (folderset I)"

definition DELETE_downstream ::
	"'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
	where
	"DELETE_downstream R I = (remove_downstream R (folderset I), filesystem I - {(a,b). (a,b) \<in> filesystem I \<and> (\<exists> e . (a,e) \<in> R)})"
	
definition DELETE_downstream2 ::
	"'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
	where
	"DELETE_downstream2 R I = (remove_downstream R (folderset I), filesystem I)"

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
	"CREATE e1 n1 (CREATE e2 n2 I) = CREATE e2 n2 (CREATE e1 n1 I)"
proof -
	show ?thesis unfolding CREATE_def using commAdd n1neqn2 by fastforce
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
shows "DELETE_downstream R2 (DELETE_downstream R1 I) = DELETE_downstream R1 (DELETE_downstream R2 I)"
proof -
	show ?thesis using O1R1 O2R2 commRemove unfolding DELETE_downstream_def DELETE_atSource_def remove_atSource_def by simp
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
	freshn: "fresh n (folderset I)"
shows "DELETE_downstream R1 (CREATE e2 n I) = CREATE e2 n (DELETE_downstream R1 I)"
proof -
	have "folderset (DELETE_downstream R1 (CREATE e2 n I)) = folderset (CREATE e2 n (DELETE_downstream R1 I))"
		using O1R1 freshn unfolding DELETE_downstream_def CREATE_def fresh_def commAddRemove DELETE_atSource_def remove_atSource_def remove_downstream_def add_def insert_Diff_if by auto
			
		show ?thesis sorry			
qed
	
end
	