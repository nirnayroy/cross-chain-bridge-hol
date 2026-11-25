theory Core
  imports Main "HOL-Library.Code_Target_Nat"
begin

datatype verdict = Certified "nat list" | Violation "nat list" | Alert "nat list"
  | NoFinding | Inconclusive | Unsupported

record observation =
  outcome :: verdict
  work :: nat
  refinements :: nat

definition measured :: "verdict \<Rightarrow> nat \<Rightarrow> observation" where
  "measured result steps = \<lparr>outcome = result, work = steps, refinements = 0\<rparr>"

inductive reachable :: "nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" for init edges where
  start: "s \<in> set init \<Longrightarrow> reachable init edges s"
| advance: "reachable init edges s \<Longrightarrow> (s,t) \<in> set edges \<Longrightarrow> reachable init edges t"

definition check_invariant :: "nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "check_invariant init edges bad certificate =
     (list_all (\<lambda>s. s \<in> set certificate) init \<and>
      list_all (\<lambda>(s,t). s \<in> set certificate \<longrightarrow> t \<in> set certificate) edges \<and>
      list_all (\<lambda>s. s \<notin> set bad) certificate)"

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

fun trace_from :: "(nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "trace_from edges bad s [] = (s \<in> set bad)"
| "trace_from edges bad s (t # ts) = ((s,t) \<in> set edges \<and> trace_from edges bad t ts)"

fun check_trace :: "nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "check_trace init edges bad [] = False"
| "check_trace init edges bad (s # ss) = (s \<in> set init \<and> trace_from edges bad s ss)"

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

definition validate :: "nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> observation \<Rightarrow> observation" where
  "validate init edges bad result =
     (case outcome result of
       Certified certificate \<Rightarrow> if check_invariant init edges bad certificate then result
                         else result\<lparr>outcome := Inconclusive\<rparr>
     | Violation path \<Rightarrow> if check_trace init edges bad path then result
                           else result\<lparr>outcome := Inconclusive\<rparr>
     | _ \<Rightarrow> result)"

lemma validated_certificate:
  assumes "outcome (validate init edges bad result) = Certified certificate"
  shows "check_invariant init edges bad certificate"
  using assms by (cases "outcome result") (auto simp: validate_def split: if_splits)

lemma validated_violation:
  assumes "outcome (validate init edges bad result) = Violation path"
  shows "check_trace init edges bad path"
  using assms by (cases "outcome result") (auto simp: validate_def split: if_splits)

lemma invalid_certificate: "\<not> check_invariant [0] [(0,1)] [1] [0]"
  by (simp add: check_invariant_def)

lemma infeasible_trace: "\<not> check_trace [0] [(0,1),(1,2)] [2] [0,2]"
  by simp

text \<open>Each frontier contains reversed paths of the same length. The first
  path retained for a new endpoint is therefore already a shortest path.\<close>

fun extend_frontier :: "(nat \<times> nat list) list \<Rightarrow> nat list \<Rightarrow> nat list list
    \<Rightarrow> nat list \<times> nat list list" where
  "extend_frontier [] seen next = (seen, rev next)"
| "extend_frontier ((t,path) # rest) seen next =
     (if t \<in> set seen then extend_frontier rest seen next
      else extend_frontier rest (t # seen) ((t # path) # next))"

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

abbreviation "start_search fuel certify init edges bad \<equiv>
  search_layers fuel certify edges bad init (map (\<lambda>s. [s]) init) 0"

end
