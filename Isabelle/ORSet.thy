theory ORSet
imports Main

begin



-- "############################"
-- "##### CRDT Definitions #####"
-- "############################"


type_synonym 'a orset = "('a \<times> nat) set"

definition abstractState ::
  "'a orset \<Rightarrow> 'a set"
where
  "abstractState S = {e . (\<exists> n . (e, n) \<in> S)}"

definition lookup ::
  "'a \<Rightarrow> 'a orset \<Rightarrow> bool"
where
  "lookup e S = (\<exists> n. (e, n) \<in> S)"

definition add_pre ::
  "nat \<Rightarrow> 'element orset \<Rightarrow> bool"
where
  "add_pre n S = (\<nexists> e . (e, n) \<in> S)"
  
definition add ::
  "'element \<Rightarrow> nat \<Rightarrow> 'element orset \<Rightarrow> 'element orset"
where
  "add e n S = S \<union> {(e, n)}"

definition remove_pre ::
  "'element \<Rightarrow> 'element orset \<Rightarrow> 'element orset \<Rightarrow> bool"
where
  "remove_pre e R S = (lookup e S \<and> (R = {(a, b) \<in> S. a = e}))"

definition remove ::
  "'element orset \<Rightarrow> 'element orset \<Rightarrow> 'element orset"
where
  "remove R S = S - R"
  
-- "#################"
-- "### Framework ###"
-- "#################"  

datatype 'a ops = Add 'a nat | Remove 'a "'a orset"
  
fun orset_downstream :: "'a ops \<Rightarrow> 'a orset \<Rightarrow> 'a orset" where
  "orset_downstream (Add e n) pl = add e n pl"
| "orset_downstream (Remove e R) pl = remove R pl"
  
fun orset_atSource :: "'a ops \<Rightarrow> 'a orset \<Rightarrow> bool" where
  "orset_atSource (Add e n) pl = add_pre n pl"
| "orset_atSource (Remove e R) pl = remove_pre e R pl"

theorem orset_comm :
fixes
  S :: "'a orset" and
  O1 :: "'a ops" and
  O2 :: "'a ops"
assumes
  O1pre: "orset_atSource O1 S" and
  O2pre: "orset_atSource O2 S"
shows "orset_downstream O2 (orset_downstream O1 S) = orset_downstream O1 (orset_downstream O2 S)"    
proof (cases O1)  
  case (Add e1 n1)
  assume C1: "O1 = Add e1 n1"
  then show ?thesis 
    proof (cases O2)
      case (Add e2 n2)
      then show ?thesis
      using C1 O1pre O2pre
      by (simp add: Un_commute add_def)
    next
      case (Remove e2 R)
      then show ?thesis
      using C1 O1pre O2pre
      apply (simp add: add_pre_def add_def remove_pre_def remove_def) 
      by auto
    qed
next
  case (Remove e1 R1)
  assume C2: "O1 = Remove e1 R1"
  then show ?thesis 
    proof (cases O2)
      case (Add e2 n)
      then show ?thesis using C2 O1pre O2pre
      apply (simp add: add_pre_def add_def remove_pre_def remove_def)
      by auto        
    next
      case (Remove e2 R)
      then show ?thesis using C2 O1pre O2pre
      apply (simp add: remove_def remove_pre_def) 
      by auto
    qed
qed

end
