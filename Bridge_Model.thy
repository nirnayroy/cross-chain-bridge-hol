theory Bridge_Model
  imports Core
begin

text \<open>The benchmark uses a closed alphabet of protocol observations. A location
  describes the history of one symbolic transfer. Delay and arrival are separate
  from source finality. Authentication is a stipulated gate, and asset identity
  is fixed. Recipient and amount observations are either consistent or inconsistent.\<close>

datatype location = Idle | Submitted | Final | Queued | Delayed | Arrived | Paid
  | ReturnPending | Returned | PendingNotice | EarlyArrival | Disconnected
  | SecondCredit | CreditWithoutFinality | BothOutcomes | CreditWithoutApproval | ChangedFields
  | PublishedSnapshot

datatype operation = Submit | Seal | Send | Delay | Deliver | Credit | StartReturn
  | FinishReturn | EmitNotice | DeliverNotice | Audit | Publish

record rule =
  origin :: location
  operation :: operation
  destination :: location
  guards :: "nat list"
  field_links :: "(nat \<times> nat) list"

abbreviation "entry s op t \<equiv>
  \<lparr>origin = s, operation = op, destination = t, guards = [], field_links = []\<rparr>"

abbreviation "credit_entry s t checks links \<equiv>
  \<lparr>origin = s, operation = Credit, destination = t, guards = checks, field_links = links\<rparr>"

abbreviation "usual_checks \<equiv> ([0,1,2] :: nat list)"
abbreviation "usual_links \<equiv> ([(0,2),(1,3)] :: (nat \<times> nat) list)"

definition standard_rules :: "rule list" where
  "standard_rules =
     [entry Idle Submit Submitted, entry Submitted Seal Final,
      entry Final Send Queued, entry Queued Delay Delayed,
      entry Queued Deliver Arrived, entry Delayed Deliver Arrived,
      credit_entry Arrived Paid usual_checks usual_links,
      entry Final StartReturn ReturnPending, entry ReturnPending FinishReturn Returned,
      entry Submitted EmitNotice PendingNotice, entry PendingNotice DeliverNotice EarlyArrival]"

definition family_rules :: "nat \<Rightarrow> rule list" where
  "family_rules family =
     (if family = 10 then [entry Idle Submit Submitted, entry Submitted Seal Final,
                            entry Final Publish PublishedSnapshot,
                            credit_entry PublishedSnapshot Paid usual_checks usual_links]
      else standard_rules @
        (if family \<le> 1 then [entry Disconnected Audit SecondCredit] else []) @
        (if family = 1 then [credit_entry Paid SecondCredit [1,2] usual_links]
         else if family = 3 then [credit_entry EarlyArrival CreditWithoutFinality [0,2] usual_links]
         else if family = 5 then [entry Paid FinishReturn BothOutcomes]
         else if family = 7 then [credit_entry Arrived CreditWithoutApproval [0,1] usual_links]
         else if family = 9 then [credit_entry Arrived ChangedFields usual_checks []]
         else []))"

definition family_bad :: "nat \<Rightarrow> location" where
  "family_bad family =
     (if family < 10 then [SecondCredit,CreditWithoutFinality,BothOutcomes,CreditWithoutApproval,ChangedFields] ! (family div 2)
      else SecondCredit)"

fun slot :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "slot x [] = 0"
| "slot x (y # ys) = (if x = y then 0 else Suc (slot x ys))"

definition locations :: "location list" where
  "locations = [Idle, Submitted, Final, Queued, Delayed, Arrived, Paid,
     ReturnPending, Returned, PendingNotice, EarlyArrival, Disconnected, SecondCredit,
     CreditWithoutFinality, BothOutcomes, CreditWithoutApproval, ChangedFields, PublishedSnapshot]"

abbreviation "location_id s \<equiv> slot s locations"

fun operation_id :: "operation \<Rightarrow> nat" where
  "operation_id Submit = 0" | "operation_id Seal = 1" | "operation_id Send = 2"
| "operation_id Delay = 3" | "operation_id Deliver = 4" | "operation_id Credit = 5"
| "operation_id StartReturn = 6" | "operation_id FinishReturn = 7"
| "operation_id EmitNotice = 8" | "operation_id DeliverNotice = 9"
| "operation_id Audit = 10" | "operation_id Publish = 11"

definition event_id :: "operation \<Rightarrow> nat \<Rightarrow> nat" where
  "event_id op transfer = 1 + 2 * operation_id op + transfer"

definition local_vertices :: "nat \<Rightarrow> nat list" where
  "local_vertices family =
     remdups (location_id Idle # location_id (family_bad family) #
       concat (map (\<lambda>r. [location_id (origin r), location_id (destination r)]) (family_rules family)))"

definition encode_state :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "encode_state left right clock = 2 * (left + length locations * right) + clock"

definition state_columns :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "state_columns transfer_count s =
     (let low = (s div 2) mod length locations; high = (s div 2) div length locations
      in (if transfer_count = 1 then [low] else [low,high]) @ [s mod 2])"

definition other_vertices :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "other_vertices family transfer_count = (if transfer_count = 1 then [0] else local_vertices family)"

definition universe :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "universe family transfer_count = concat (map (\<lambda>left. concat (map (\<lambda>right.
     map (encode_state left right) [0,1]) (other_vertices family transfer_count))) (local_vertices family))"

abbreviation "initial_states \<equiv> ([0] :: nat list)"

definition lift_rule :: "nat \<Rightarrow> nat \<Rightarrow> rule \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "lift_rule family transfer_count r =
     (let s = location_id (origin r); t = location_id (destination r); op = operation r
      in concat (map (\<lambda>right. map (\<lambda>clock.
           (encode_state s right clock,event_id op 0,encode_state t right clock)) [0,1])
           (other_vertices family transfer_count)) @
         (if transfer_count = 1 then [] else concat (map (\<lambda>left. map (\<lambda>clock.
           (encode_state left s clock,event_id op 1,encode_state left t clock)) [0,1])
           (local_vertices family))))"

definition labelled_edges :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "labelled_edges family transfer_count =
     concat (map (lift_rule family transfer_count) (family_rules family)) @
     map (\<lambda>s. (s,0,if s mod 2 = 0 then Suc s else s - 1)) (universe family transfer_count)"

definition bad_states :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "bad_states family transfer_count =
     filter (\<lambda>s. location_id (family_bad family) \<in> set (take transfer_count (state_columns transfer_count s)))
       (universe family transfer_count)"

definition predicate_columns :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "predicate_columns family transfer_count =
     concat (map (\<lambda>i. map (\<lambda>v. filter (\<lambda>s. state_columns transfer_count s ! i = v) (universe family transfer_count))
          (local_vertices family)) [0..<transfer_count])"

definition dependencies :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat list \<times> nat list) list" where
  "dependencies family transfer_count = (0,[],[transfer_count]) # remdups (concat (map (\<lambda>i.
     map (\<lambda>r. (event_id (operation r) i,[i],[i])) (family_rules family)) [0..<transfer_count]))"

definition ordinary_edges :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "ordinary_edges family transfer_count = map (\<lambda>(s,e,t). (s,t)) (labelled_edges family transfer_count)"

end
