theory Core
  imports Main "HOL-Library.Code_Target_Nat"
begin

(* A datatype defines the possible shapes of a value. The vertical bar separates
   constructors. Certified carries a list of allowed state IDs, Violation
   carries a path, and Alert carries rule IDs. The other constructors carry no
   data. *)
datatype verdict = Certified "nat list" | Violation "nat list" | Alert "nat list"
  | NoFinding | Inconclusive | Unsupported

(* A record groups named fields. The field names also act as functions, so work
   result reads the work field of result. *)
record observation =
  outcome :: verdict
  work :: nat
  refinements :: nat

(* Build an observation with a verdict and work count. The expression after where
   is a defining equation. Function application uses spaces, so measured
   result steps passes two arguments. *)
definition measured :: "verdict \<Rightarrow> nat \<Rightarrow> observation" where
  "measured result steps = \<lparr>outcome = result, work = steps, refinements = 0\<rparr>"

(* An inductive definition gives the rules that generate a relation. Fix init and
   edges with for. The start rule makes each initial state reachable. The
   advance rule extends reachability by one edge. The double arrow reads as
   “implies” between premises and conclusion. *)
inductive reachable :: "nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" for init edges where
  start: "s \<in> set init \<Longrightarrow> reachable init edges s"
| advance: "reachable init edges s \<Longrightarrow> (s,t) \<in> set edges \<Longrightarrow> reachable init edges t"

(* Test three obligations. Every initial state belongs to the proposed
   certificate, every edge leaving a certificate state stays inside it, and no
   certificate state is bad. list_all checks every list entry, set converts a
   list into a set, and the lambda over (s,t) unpacks each edge. *)
definition check_invariant :: "nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "check_invariant init edges bad certificate =
     (list_all (\<lambda>s. s \<in> set certificate) init \<and>
      list_all (\<lambda>(s,t). s \<in> set certificate \<longrightarrow> t \<in> set certificate) edges \<and>
      list_all (\<lambda>s. s \<notin> set bad) certificate)"

(* A lemma states a claim. assumes names its premises and shows states its
   conclusion. The proof inducts over how reachability was derived. The start
   case uses initial inclusion, and the advance case uses closure under one
   edge. *)
lemma check_invariant_sound:
  assumes "check_invariant init edges bad certificate" and "reachable init edges s"
  shows "s \<notin> set bad"
proof -
  from assms(2) have "s \<in> set certificate"
  proof (induction rule: reachable.induct)
    case (start s)
    with assms(1) show ?case by (auto simp: check_invariant_def list_all_iff)
  next
    case (advance s t)
    with assms(1) show ?case by (auto simp: check_invariant_def list_all_iff)
  qed
  with assms(1) show ?thesis by (auto simp: check_invariant_def list_all_iff)
qed

(* fun defines a function by equations. An empty suffix [] checks whether the
   current state is bad. The pattern t # ts splits a nonempty suffix into its
   head t and tail ts. Check the next edge and recurse on the shorter tail. *)
fun trace_from :: "(nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "trace_from edges bad s [] = (s \<in> set bad)"
| "trace_from edges bad s (t # ts) = ((s,t) \<in> set edges \<and> trace_from edges bad t ts)"

(* Reject an empty path. For a nonempty path, check that its first state is
   initial and hand the rest to trace_from. *)
fun check_trace :: "nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "check_trace init edges bad [] = False"
| "check_trace init edges bad (s # ss) = (s \<in> set init \<and> trace_from edges bad s ss)"

(* Induct on the remaining path. arbitrary: s keeps the starting state general so
   the induction hypothesis can be applied with the next state t. The base
   case already ends at the current state. *)
lemma trace_from_sound:
  assumes "trace_from edges bad s ss" and "reachable init edges s"
  shows "reachable init edges (last (s # ss)) \<and> last (s # ss) \<in> set bad"
  using assms
proof (induction ss arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  then have tail: "trace_from edges bad t ts" and step_reachable: "reachable init edges t"
    by (auto intro: reachable.advance)
  from Cons.IH[OF tail step_reachable] show ?case by simp
qed

(* cases path splits the proof into Nil and Cons, the empty and nonempty list
   cases. In the Cons case, combine the initial state's reachability with the
   previous lemma. *)
lemma check_trace_sound:
  assumes "check_trace init edges bad path"
  shows "path \<noteq> [] \<and> reachable init edges (last path) \<and> last path \<in> set bad"
proof (cases path)
  case Nil
  with assms show ?thesis by simp
next
  case (Cons s ss)
  with assms have tail: "trace_from edges bad s ss" and first: "s \<in> set init" by simp_all
  from trace_from_sound[OF tail reachable.start[OF first]] Cons show ?thesis by simp
qed

(* A case expression inspects the result constructor and binds its data. Forward
   accepted evidence unchanged. An invalid certificate or trace gets an
   Inconclusive outcome through a record update. The wildcard _ covers
   statuses that carry no definitive claim. *)
definition validate :: "nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> observation \<Rightarrow> observation" where
  "validate init edges bad result =
     (case outcome result of
       Certified certificate \<Rightarrow> if check_invariant init edges bad certificate then result
                         else result\<lparr>outcome := Inconclusive\<rparr>
     | Violation path \<Rightarrow> if check_trace init edges bad path then result
                           else result\<lparr>outcome := Inconclusive\<rparr>
     | _ \<Rightarrow> result)"

(* Connect an externally visible Certified result to the invariant check. The
   proof splits the verdict and the if conditions in validate. *)
lemma validated_certificate:
  assumes "outcome (validate init edges bad result) = Certified certificate"
  shows "check_invariant init edges bad certificate"
  using assms by (cases "outcome result") (auto simp: validate_def split: if_splits)

(* Connect an externally visible Violation result to the trace check by the same
   case split. *)
lemma validated_violation:
  assumes "outcome (validate init edges bad result) = Violation path"
  shows "check_trace init edges bad path"
  using assms by (cases "outcome result") (auto simp: validate_def split: if_splits)

(* This regression example starts in state 0, which has an edge to bad state 1. A
   certificate containing only state 0 fails the closure check. simp rewrites
   the concrete equation. *)
lemma invalid_certificate: "\<not> check_invariant [0] [(0,1)] [1] [0]"
  by (simp add: check_invariant_def)

(* The list [0,2] skips the intermediate state 1. The checker must reject it even
   though 2 is reachable by a different path. *)
lemma infeasible_trace: "\<not> check_trace [0] [(0,1),(1,2)] [2] [0,2]"
  by simp

text \<open>Each frontier contains reversed paths of the same length. The first
  path retained for a new endpoint is therefore already a shortest path.\<close>

(* Visit candidate pairs (endpoint, reversed path) in order. Retain the first
   path to each new endpoint and add it to seen immediately. Reverse the
   accumulator at the end to restore candidate order. *)
fun extend_frontier :: "(nat \<times> nat list) list \<Rightarrow> nat list \<Rightarrow> nat list list
    \<Rightarrow> nat list \<times> nat list list" where
  "extend_frontier [] seen next = (seen, rev next)"
| "extend_frontier ((t,path) # rest) seen next =
     (if t \<in> set seen then extend_frontier rest seen next
      else extend_frontier rest (t # seen) ((t # path) # next))"

(* Test the current frontier for a bad endpoint before examining the depth
   budget. An empty frontier means exploration reached a fixed point.
   Otherwise spend one unit of fuel, collect successors, and recur with the
   next breadth-first layer. The work counter counts expanded states. *)
fun search_layers :: "nat \<Rightarrow> bool \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list
    \<Rightarrow> nat list \<Rightarrow> nat list list \<Rightarrow> nat \<Rightarrow> observation" where
  "search_layers fuel certify edges bad seen frontier steps =
     (case List.find (\<lambda>p. hd p \<in> set bad) frontier of
       Some p \<Rightarrow> measured (Violation (rev p)) steps
     | None \<Rightarrow> if frontier = [] then measured (if certify then Certified seen else NoFinding) steps
       else case fuel of 0 \<Rightarrow> measured (if certify then Inconclusive else NoFinding) steps
       | Suc remaining \<Rightarrow>
         (let successors = concat (map (\<lambda>p. map (\<lambda>(s,t). (t,p)) (filter (\<lambda>e. fst e = hd p) edges)) frontier);
              (seen',next) = extend_frontier successors seen []
          in search_layers remaining certify edges bad seen' next (steps + length frontier)))"

(* abbreviation gives a shorter expression that Isabelle expands automatically.
   Start with each initial state as a one-element path and with work equal to
   zero. *)
abbreviation "start_search fuel certify init edges bad \<equiv>
  search_layers fuel certify edges bad init (map (\<lambda>s. [s]) init) 0"

end
