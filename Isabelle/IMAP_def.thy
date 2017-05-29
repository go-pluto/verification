section {* IMAP Definitions *}

theory IMAP_def
imports ORSet_def
begin
	
text {* 
  Based on the previously defined OR-Set we define the @{term imap} datatype by combining an 
  OR-Set with a partial function. The OR-Set represents the set of folders inside a mailbox. The
  partial function can be interpreted as a filesystem, where we have for each mailbox a folder, 
  which contains a set of message files. Hence, the abbreviations @{term folderset} and 
  @{term filesystem}.
*}
type_synonym ('a, 'b) imap = "'a orset \<times> ('a \<rightharpoonup> 'b set)"

abbreviation folderset ::
  "('a, 'b) imap \<Rightarrow> 'a orset"
where
  "folderset I \<equiv> fst I"

abbreviation filesystem ::
  "('a, 'b) imap \<Rightarrow> ('a \<rightharpoonup> 'b set)"
where
  "filesystem I \<equiv> snd I"
  
subsection {* Auxiliary Definitions  *}

text {* 
  We define an imap instance to be valid, if each folder in the folderset is present in the 
  filesystem and each folder in the filesystem has a corresponding folder in the folderset.
*}
definition validState ::
  "('a, 'b) imap \<Rightarrow> bool"
where
  "validState I = 
		((\<forall> (a, _) \<in> folderset I . (filesystem I) a \<noteq> None) \<and>
    (\<forall> f . (filesystem I) f \<noteq> None \<longrightarrow> (\<exists> (a, _) \<in> folderset I . a = f)))"

text {* 
  We define a lookup function that returns true if a message @{term msg} is present in the folder 
  @{term f} in the imap instance @{term I}.
*}	
definition msgLookup ::
  "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "msgLookup f msg I = (
  case (filesystem I)(f) of
      None \<Rightarrow> False |
      Some msgset \<Rightarrow> msg \<in> msgset
  )"

text {* 
  The operation @{term msgReplace} removes the message @{term msgold} from the set of messages 
  @{term S} and inserts the new message @{term msgnew}.
*}	
definition msgReplace ::
  "'b \<Rightarrow> 'b \<Rightarrow> 'b set \<Rightarrow> 'b set"
where
  "msgReplace msgold msgnew S = (S - {msgold}) \<union> {msgnew}"

subsection {* Update Operations *}

text {* 
  Next, we define the update operations on the imap type and the corresponding preconditions. The
  operation @{term create} adds a folder to the folderset and creates an entry in the filesystem.
  The corresponding precondition checks whether the tag @{term n} is fresh with respect to the 
  current state of the folderset. Moreover the folder must not be already present in the folderset.
*}	
definition create_pre ::
  "'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "create_pre f n I = (add_pre n (folderset I) \<and> \<not> lookup f (folderset I))"

definition create ::
  "'a \<Rightarrow> nat \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "create f n I = (add f n (folderset I), (filesystem I)(f := Some {}))"

text {* 
  The @{term delete} operation removes a folder from the folderset and deletes the corresponding 
  entry in the filesystem. The precondition is satisfied if the folder @{term f} is present in the
  current state of the imap instance @{term I}. Moreover, the remove-set @{term R} must be computed
  accordingly.
*}
definition delete_pre ::
  "'a \<Rightarrow> 'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "delete_pre f R I = remove_pre f R (folderset I)"

definition delete ::
  "'a \<Rightarrow> 'a orset \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "delete f R I = (remove R (folderset I), (filesystem I)(f := None))"

text {* 
  The append operation adds the message @{term m} to the folder @{term f} in @{term I}. As
  precondition, we define that the folder must exist in the folderset and that the message is not
  already present in the folder. In the IMAP specification (RFC 3501), the APPEND command can be
  executed when the user is in the SELECTED state, i.e. a certain folder has been focused. We 
  modeled this focus by the parameter @{term f}, which represents the selected folder.
*}
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

text {* 
  The STORE command in IMAP aims to change the flags for a set of message. For the sake of 
  simplicity, we have modeled the @{term store} operation to work only on one message. According to 
  maildir, the file format for a mailbox, flags of a message are stored in the filename of the 
  message. Hence, in our model, the @{term store} operation replaces the entry in the filesystem 
  with a new entry. These entrys can be interpreted as filenames for a message file. As 
  precondition, we have defined that the folder @{term f} must exist in @{term I} and that the 
  messages @{term msgold} and @{term msgnew} can be removed and inserted accordingly. Note that, as 
  described above, we have modeled the folder focus by IMAP SELECT with the parameter @{term f}.
*}
definition store_pre ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> bool"
where
  "store_pre f msgold msgnew I = 
		((\<exists> (a, _) \<in> folderset I . a = f) \<and>
		msgLookup f msgold I \<and> \<not>(msgLookup f msgnew I))"

definition store ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) imap \<Rightarrow> ('a, 'b) imap"
where
  "store f msgold msgnew I =
  (folderset I,
  (case (filesystem I)(f) of
    None \<Rightarrow> filesystem I |
    Some msgset \<Rightarrow> (filesystem I)(f := Some (msgReplace msgold msgnew msgset))
  ))"

text {* 
  The EXPUNGE command in IMAP removes all messages with a deleted flag in a selected folder. 
  Since, in the current model and according to maildir, the flags are part of the message filename, 
  we model the @{term expunge} operation as an operation that removes a message from the filesystem. 
  For the sake of simplicity, we define the operation to work only on one message at a time. As 
  precondition we have defined that the folder @{term f} must exist in @{term I} and that the 
  message is present in the filesytem.
*}
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

subsection {* IMAP Datatype *}

text {*
  Next, we define the IMAP datatype by defining the update operations @{term Create}, 
  @{term Delete}, @{term Append}, @{term Store}, and @{term Expunge}. Moreover we assign the 
  corresponding downstream operations and atSource preconditions.
*}
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
