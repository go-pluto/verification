theory ORSet
imports Main
    
begin

type_synonym 'a payload = "('a * nat) set"
	
definition abstractState ::
  "'a payload \<Rightarrow> 'a set"
where
  "abstractState S = {e . (\<exists> n . (e,n) \<in> S)}"
  
definition fresh ::
  "nat \<Rightarrow> 'a payload \<Rightarrow> bool"
where
  "fresh n S = (\<nexists> e . (e,n) \<in> S)"
  
definition lookup ::
  "'a \<Rightarrow> 'a payload \<Rightarrow> bool"
where
  "lookup e S = (\<exists> n. (e,n) \<in> S)" 

definition add ::
  "'element \<Rightarrow> nat \<Rightarrow> 'element payload \<Rightarrow> 'element payload"
where
  "add e alpha S = S \<union> {(e, alpha)}"
  
definition remove_atSource ::
	"'element \<Rightarrow> 'element payload \<Rightarrow> 'element payload"
where
	"remove_atSource e S = {(e,n).(\<exists> u.(e,u) \<in> S \<and> n = u)}"
  
definition remove_downstream ::
  "'element payload \<Rightarrow> 'element payload \<Rightarrow> 'element payload"
where
  "remove_downstream R S = S - R"  

lemma commAdd:
  shows "\<forall> S . n1 \<noteq> n2 \<longrightarrow> add e1 n1 (add e2 n2 S) = add e2 n2 (add e1 n1 S)"
proof clarify
  fix S
  assume "n1 \<noteq> n2"
  then show "add e1 n1 (add e2 n2 S) = add e2 n2 (add e1 n1 S)"
    by (simp add: Un_commute add_def)
qed
	
lemma commRemove:
fixes
  S :: "'a payload" and
  R1 :: "'a payload" and
  R2 :: "'a payload" and
  e1 :: "'a" and
  e2 :: "'a"
assumes 
  O1R1: " R1 = remove_atSource e1 S" and
  O2R2: " R2 = remove_atSource e2 S" and
  ValO1: "lookup e1 S" and
  ValO2: "lookup e2 S"
shows "remove_downstream R2 (remove_downstream R1 S) = remove_downstream R1 (remove_downstream R2 S)"
proof -
	show ?thesis using O1R1 O2R2 unfolding remove_atSource_def by auto
qed

lemma commAddRemove:
fixes
  S :: "'a payload" and
  R :: "'a payload" and
  e1 :: "'a" and
  e2 :: "'a" and
  n :: nat
assumes
	OR: " R = remove_atSource e1 S" and
	ValO1: "lookup e1 S" and
	freshn: "fresh n S"
shows "abstractState (remove_downstream R (add e2 n S)) = abstractState (add e2 n (remove_downstream R S))"
proof -
  show ?thesis using OR ValO1 freshn unfolding abstractState_def remove_downstream_def remove_atSource_def add_def fresh_def by auto
qed

end
 