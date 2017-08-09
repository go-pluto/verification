theory
  "IMAP-def"
imports
  "../CRDT/Network"
begin

datatype ('id, 'a) operation = 
	Add "'id" "'a" | 
	Rem "'id set" "'a" | 
	Append "'id" "'a" | 
	Expunge "'a" "'id" "'id" | 
	Store "'a" "'id" "'id"

type_synonym ('id, 'a) state = "'a \<Rightarrow> ('id set \<times> 'id set)"

definition op_elem :: "('id, 'a) operation \<Rightarrow> 'a" where
  "op_elem oper \<equiv> case oper of 
		Add i e \<Rightarrow> e | 
		Rem is e \<Rightarrow> e | 
		Append i e \<Rightarrow> e | 
		Expunge e mo i \<Rightarrow> e | 
		Store e mo i \<Rightarrow> e"

definition interpret_op :: "('id, 'a) operation \<Rightarrow> ('id, 'a) state \<rightharpoonup> ('id, 'a) state" ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_op oper state \<equiv>
     let metadata = fst (state (op_elem oper));
				 files = snd (state (op_elem oper));
         after  = case oper of 
				   Add i e \<Rightarrow> (metadata \<union> {i}, files) |
					 Rem is e \<Rightarrow> (metadata - is, files - is) |
					 Append i e \<Rightarrow> (metadata, files \<union> {i}) |
				   Expunge e mo i \<Rightarrow> (metadata \<union> {i}, files - {mo}) |
					 Store e mo i \<Rightarrow> (metadata, insert i (files - {mo}))
     in  Some (state ((op_elem oper) := after))"
  
definition valid_behaviours :: "('id, 'a) state \<Rightarrow> 'id \<times> ('id, 'a) operation \<Rightarrow> bool" where
  "valid_behaviours state msg \<equiv>
     case msg of
       (i, Add j  e) \<Rightarrow> i = j |
       (i, Rem is e) \<Rightarrow> is = fst (state e) \<union> snd (state e) |
			 (i, Append j e) \<Rightarrow> i = j |
			 (i, Expunge e mo j) \<Rightarrow> i = j \<and> mo \<in> snd (state e) |
		   (i, Store e mo j) \<Rightarrow> i = j \<and> mo \<in> snd (state e)"

locale imap = network_with_constrained_ops _ interpret_op "\<lambda>x. ({},{})" valid_behaviours
	
end