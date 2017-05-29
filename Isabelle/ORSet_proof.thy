section {* ORSet Proofs *}

theory ORSet_proof
imports ORSet_def
begin

text {* We show, that all operations on the OR-Set datatype are commutative.*}
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
      by (simp add: add_pre_def add_def remove_pre_def remove_def, auto)
  qed
next
  case (Remove e1 R1)
  assume C2: "O1 = Remove e1 R1"
  then show ?thesis 
  proof (cases O2)
    case (Add e2 n) 
    then show ?thesis using C2 O1pre O2pre
      by (simp add: add_pre_def add_def remove_pre_def remove_def, auto)      
  next
    case (Remove e2 R)
    then show ?thesis using C2 O1pre O2pre
      by (simp add: remove_def remove_pre_def, auto)
  qed
qed

end
