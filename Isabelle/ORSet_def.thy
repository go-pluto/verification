theory ORSet_def
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

end
