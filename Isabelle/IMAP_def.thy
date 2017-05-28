theory IMAP_def
imports ORSet_def
begin

-- "#############################"
-- "### Definitions & Helpers ###"
-- "#############################"


-- "Type definition: 'a is the set of all folder names, 'b is the set of all message names"
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
  "('a, 'b) imap \<Rightarrow> bool"
where
  "validState I = ((\<forall> (a, _) \<in> folderset I . (filesystem I) a \<noteq> None)
  \<and> (\<forall> f . (filesystem I) f \<noteq> None \<longrightarrow> (\<exists> (a, _) \<in> folderset I . a = f)))"

definition msgReplace ::
  "'b \<Rightarrow> 'b \<Rightarrow> 'b set \<Rightarrow> 'b set"
where
  "msgReplace msgold msgnew S = (S - {msgold}) \<union> {msgnew}"

definition msgLookup ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "msgLookup f msg I = (
  case (filesystem I)(f) of
      None \<Rightarrow> False |
      Some msgset \<Rightarrow> msg \<in> msgset
  )"

-- "#######################"
-- "### IMAP Operations ###"
-- "#######################"

definition create_pre ::
  "'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "create_pre f n I = (add_pre n (folderset I) \<and> \<not> lookup f (folderset I))"

definition create ::
  "'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "create f n I = (add f n (folderset I), (filesystem I)(f := Some {}))"

definition delete_pre ::
  "'a \<Rightarrow> 'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "delete_pre f R I = remove_pre f R (folderset I)"

definition delete ::
  "'a \<Rightarrow> 'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "delete f R I = (remove R (folderset I), (filesystem I)(f := None))"

definition append_pre ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "append_pre f m I = (\<exists> (a, _) \<in> folderset I . a = f \<and> \<not> msgLookup f m I)"

definition append ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "append f m I =
  (folderset I,
  (case (filesystem I)(f) of
      None \<Rightarrow> filesystem I |
      Some msgset \<Rightarrow> (filesystem I)(f := Some (msgset \<union> {m}))
  ))"

definition store_pre ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "store_pre f msgold msgnew I = ((\<exists> (a, _) \<in> folderset I . a = f) \<and> msgLookup f msgold I \<and> \<not>(msgLookup f msgnew I))"

definition store ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "store f msgold msgnew I =
  (folderset I,
  (case (filesystem I)(f) of
      None \<Rightarrow> filesystem I |
      Some msgset \<Rightarrow> (filesystem I)(f := Some (msgReplace msgold msgnew msgset))
  ))"

definition expunge_pre ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "expunge_pre f m I = ((\<exists> (a, _) \<in> folderset I . a = f) \<and> msgLookup f m I)"

definition expunge ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "expunge f m I =
  (folderset I,
  (case (filesystem I)(f) of
      None \<Rightarrow> filesystem I |
      Some msgset \<Rightarrow> (filesystem I)(f := Some (msgset - {m}))
  ))"

datatype ('a, 'b) ops = 
  Create 'a nat | 
  Delete 'a "'a orset" | 
  Append 'a 'b | 
  Store 'a 'b 'b |
  Expunge 'a 'b

fun imap_downstream :: "('a, 'b) ops \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a,'b) imap" where
  "imap_downstream (Create f n) imap = create f n imap"
| "imap_downstream (Delete f R) imap = delete f R imap"
| "imap_downstream (Append f m) imap = append f m imap"
| "imap_downstream (Store f mo mn) imap = store f mo mn imap"
| "imap_downstream (Expunge f m) imap = expunge f m imap"  
  
fun imap_atSource :: "('a, 'b) ops \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool" where
  "imap_atSource (Create f n) imap = create_pre f n imap"
| "imap_atSource (Delete f R) imap = delete_pre f R imap"
| "imap_atSource (Append f m) imap = append_pre f m imap"
| "imap_atSource (Store f mo mn) imap = store_pre f mo mn imap"
| "imap_atSource (Expunge f m) imap = expunge_pre f m imap"

end