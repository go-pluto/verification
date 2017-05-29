section {* OR-Set Definitions *}

text {*
  In this section, we define the the op-based OR-Set type and operations on this type.
*}
theory ORSet_def
imports Main
begin
	
text {*
  We start by defining the payload. The payload is a set of value/tag pairs. In this implementation, 
  the unique tag is a number.
*}
type_synonym 'a orset = "('a \<times> nat) set"
	
subsection {* Query Operations *}

text {*
  The @{term lookup} query scans for existing pairs for the element @{term e} in the OR-Set.
*}
definition lookup ::
  "'a \<Rightarrow> 'a orset \<Rightarrow> bool"
where
  "lookup e S = (\<exists> n. (e, n) \<in> S)"
  
subsection {* Update Operations *}

text {*
  The @{term add} precondition requires the freshness of the tag with respect to the current state
  of the OR-Set.
*}
definition add_pre ::
  "nat \<Rightarrow> 'element orset \<Rightarrow> bool"
where
  "add_pre n S = (\<nexists> e . (e, n) \<in> S)"

text {*
  The @{term add} operation inserts the pair of the element @{term e} and the tag @{term n} to the OR-Set @{term S}.
*}
definition add ::
  "'element \<Rightarrow> nat \<Rightarrow> 'element orset \<Rightarrow> 'element orset"
where
  "add e n S = S \<union> {(e, n)}"

text {*
  The @{term remove} precondition checks whether the value @{term e} is currently an element of the
  OR-Set. Moreover, the remove-set @{term R} is computed.
*}
definition remove_pre ::
  "'element \<Rightarrow> 'element orset \<Rightarrow> 'element orset \<Rightarrow> bool"
where
  "remove_pre e R S = (lookup e S \<and> (R = {(a, b) \<in> S. a = e}))"

text {*
  The @{term remove} operation deletes the remove-set @{term R} from the OR-Set @{term S}.
*}
definition remove ::
  "'element orset \<Rightarrow> 'element orset \<Rightarrow> 'element orset"
where
  "remove R S = S - R"
  
subsection {* Datatype Definitions *}
	
text {*
  Next, we define the OR-Set datatype by defining the update operations @{term Add} and 
  @{term Remove} and assign the corresponding downstream operations and atSource preconditions.
*}

datatype 'a ops = Add 'a nat | Remove 'a "'a orset"
  
fun orset_downstream :: "'a ops \<Rightarrow> 'a orset \<Rightarrow> 'a orset" where
  "orset_downstream (Add e n) pl = add e n pl"
| "orset_downstream (Remove e R) pl = remove R pl"
  
fun orset_atSource :: "'a ops \<Rightarrow> 'a orset \<Rightarrow> bool" where
  "orset_atSource (Add e n) pl = add_pre n pl"
| "orset_atSource (Remove e R) pl = remove_pre e R pl"

end
