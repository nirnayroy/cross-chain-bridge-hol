theory PDR
  imports Core
begin

text \<open>Each frame from level one represents the safety property strengthened by
  a conjunction of blocking clauses. A cube is the finite set of states excluded
  by a clause. The initial frame is represented by the initial states directly.\<close>

(* The following aliases give meaningful names to existing types. Each cube lists
   the states a blocking clause excludes. A frame holds several such clauses,
   an edge holds two state IDs, and an obligation holds a frame level and a
   path suffix. *)
type_synonym pdr_cube = "nat list"
type_synonym pdr_frame = "pdr_cube list"
type_synonym pdr_edges = "(nat \<times> nat) list"
type_synonym pdr_obligation = "nat \<times> nat list"

(* Increment the work counter with Suc, which means one plus a natural number.
   The record update keeps the other fields. *)
definition pdr_tick :: "observation \<Rightarrow> observation" where
  "pdr_tick result = result\<lparr>work := Suc (work result)\<rparr>"

(* A state satisfies a frame if it is outside the bad set and outside every
   blocked cube. *)
definition pdr_in_frame :: "nat list \<Rightarrow> pdr_frame \<Rightarrow> nat \<Rightarrow> bool" where
  "pdr_in_frame bad frame state =
    (\<not> List.member bad state \<and> list_all (\<lambda>cube. \<not> List.member cube state) frame)"

(* Level zero denotes the initial states. Successor levels index the frame list,
   whose first entry represents level one. *)
fun pdr_in_level :: "nat list \<Rightarrow> nat list \<Rightarrow> pdr_frame list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "pdr_in_level initial bad frames 0 state = List.member initial state"
| "pdr_in_level initial bad frames (Suc level) state = pdr_in_frame bad (frames ! level) state"

(* Add a clause unless the same cube is already in the frame. *)
definition pdr_add_clause :: "pdr_cube \<Rightarrow> pdr_frame \<Rightarrow> pdr_frame" where
  "pdr_add_clause cube frame = (if List.member frame cube then frame else cube # frame)"

(* Strengthen every stored frame through the selected level. Stop when the level
   is zero or there are no frames left. *)
fun pdr_add_through :: "nat \<Rightarrow> pdr_cube \<Rightarrow> pdr_frame list \<Rightarrow> pdr_frame list" where
  "pdr_add_through level cube [] = []"
| "pdr_add_through level cube (frame # frames) =
     (if level = 0 then frame # frames
      else pdr_add_clause cube frame # pdr_add_through (level - 1) cube frames)"

text \<open>Relax the equality cube by dropping low-order bits of the finite state
  encoding. A relaxed cube can be blocked only when it excludes initial states
  and its complement is inductive relative to the previous frame.\<close>

(* Check that the cube excludes all initial states and that no edge enters it
   from outside it in the previous frame. This checks relative inductiveness
   of the cube's complement. *)
definition pdr_can_block :: "nat list \<Rightarrow> pdr_edges \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> pdr_cube \<Rightarrow> bool" where
  "pdr_can_block initial edges previous cube =
    (list_all (\<lambda>s. \<not> List.member cube s) initial \<and>
     list_all (\<lambda>(s, t). \<not> List.member cube t \<or> List.member cube s \<or> \<not> previous s) edges)"

(* Try cubes that group state IDs by increasingly wide numeric intervals. foldl
   carries the best valid cube forward from the singleton candidate. *)
definition pdr_generalize :: "nat list \<Rightarrow> nat list \<Rightarrow> pdr_edges \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> pdr_cube" where
  "pdr_generalize universe initial edges previous state =
    foldl (\<lambda>blocked width.
      let candidate = filter (\<lambda>s. s div width = state div width) universe
      in if pdr_can_block initial edges previous candidate then candidate else blocked)
      [state] [2, 4, 8, 16, 32]"

(* Compute the successors of the current frame. Any blocked cube that excludes
   all those successors can be carried into the next frame. *)
fun pdr_push :: "nat list \<Rightarrow> pdr_edges \<Rightarrow> pdr_frame \<Rightarrow> pdr_frame list \<Rightarrow> pdr_frame list" where
  "pdr_push bad edges current [] = [current]"
| "pdr_push bad edges current (next # rest) =
     (let successors = map snd (filter (\<lambda>edge. pdr_in_frame bad current (fst edge)) edges);
          pushable = filter (\<lambda>cube. list_all (\<lambda>s. \<not> List.member successors s) cube) current;
          strengthened = fold pdr_add_clause pushable next
      in current # pdr_push bad edges strengthened rest)"

(* Compare membership in successive frames for every state in the finite
   universe. Return Some invariant on equality, or None when no pair matches. *)
fun pdr_fixed_frame :: "nat list \<Rightarrow> nat list \<Rightarrow> pdr_frame \<Rightarrow> pdr_frame list \<Rightarrow> nat list option" where
  "pdr_fixed_frame universe bad current [] = None"
| "pdr_fixed_frame universe bad current (next # rest) =
     (if list_all (\<lambda>s. pdr_in_frame bad current s = pdr_in_frame bad next s) universe
      then Some (filter (pdr_in_frame bad current) universe)
      else pdr_fixed_frame universe bad next rest)"

text \<open>An obligation stores its level and its suffix to a bad state. Predecessor
  obligations run first. Successful blocking strengthens the earlier frames and
  lets the search retry the parent obligation. Fuel counts search iterations.\<close>

(* Spend one step on the worklist. With no pending obligations, either schedule a
   predecessor of a bad state or propagate clauses and look for convergence.
   With an obligation, check initial membership, skip an already excluded
   state, chase a predecessor, or learn a blocking clause. *)
fun pdr_search :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> pdr_edges \<Rightarrow> nat list \<Rightarrow>
    pdr_frame list \<Rightarrow> pdr_obligation list \<Rightarrow> observation" where
  "pdr_search 0 universe initial edges bad frames pending = measured Inconclusive 0"
| "pdr_search (Suc fuel) universe initial edges bad frames pending = pdr_tick
     (case pending of
        [] \<Rightarrow>
          (case List.find (\<lambda>(s, t). pdr_in_frame bad (last frames) s \<and> List.member bad t) edges of
             Some (s, t) \<Rightarrow> pdr_search fuel universe initial edges bad frames [(length frames, [s, t])]
           | None \<Rightarrow>
               (let pushed = pdr_push bad edges (hd frames) (tl frames @ [[]]) in
                case pdr_fixed_frame universe bad (hd pushed) (tl pushed) of
                   Some invariant \<Rightarrow> measured (Certified invariant) 0
                 | None \<Rightarrow> pdr_search fuel universe initial edges bad pushed []))
      | (_, []) # rest \<Rightarrow> pdr_search fuel universe initial edges bad frames rest
      | (level, s # suffix) # rest \<Rightarrow>
          (if List.member initial s then measured (Violation (s # suffix)) 0
           else if level = 0 \<or> \<not> pdr_in_level initial bad frames level s
             then pdr_search fuel universe initial edges bad frames rest
           else let previous = pdr_in_level initial bad frames (level - 1) in
             case List.find (\<lambda>(source, target). target = s \<and> previous source) edges of
                Some (source, _) \<Rightarrow> pdr_search fuel universe initial edges bad frames
                  ((level - 1, source # s # suffix) # pending)
              | None \<Rightarrow>
                  (let cube = pdr_generalize universe initial edges previous s;
                       strengthened = pdr_add_through level cube frames
                   in pdr_search fuel universe initial edges bad strengthened rest)))"

(* Handle zero fuel and bad initial states first. Otherwise start with one
   property frame and an empty obligation list. *)
definition run_pdr :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> pdr_edges \<Rightarrow> nat list \<Rightarrow> observation" where
  "run_pdr fuel universe initial edges bad =
    (if fuel = 0 then measured Inconclusive 0
     else case List.find (List.member bad) initial of
        Some state \<Rightarrow> measured (Violation [state]) 1
      | None \<Rightarrow> pdr_search fuel universe initial edges bad [[]] [])"

subsection \<open>Predicate abstraction and refinement\<close>

(* Encode the truth values of the current predicates as a binary number. States
   with the same signature are in the same abstract class. *)
definition pdr_signature :: "nat list list \<Rightarrow> nat \<Rightarrow> nat" where
  "pdr_signature predicates state =
     foldl (\<lambda>key predicate. 2 * key + (if List.member predicate state then 1 else 0)) 0 predicates"

(* A feasible result carries one concrete path. A spurious result carries the
   endpoint sets around the first failed join so refinement can distinguish
   them. *)
datatype pdr_feasibility = Feasible "nat list" | Spurious "nat list" "nat list"

(* Extend paths with concrete edges into the next abstract class. Keep one path
   per endpoint because future steps depend only on that endpoint. *)
definition pdr_extend_witnesses :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pdr_edges \<Rightarrow>
    (nat \<times> nat list) list \<Rightarrow> (nat \<times> nat list) list" where
  "pdr_extend_witnesses key target edges witnesses =
    foldl (\<lambda>next (s, t).
      if key t \<noteq> target \<or> map_of next t \<noteq> None then next
      else case map_of witnesses s of
         None \<Rightarrow> next
       | Some suffix \<Rightarrow> (t, t # suffix) # next) [] edges"

(* Walk along the abstract path one class at a time. If no concrete extension
   exists, report the reachable prefix endpoints and potential sources of the
   missing edge. *)
fun pdr_follow_classes :: "(nat \<Rightarrow> nat) \<Rightarrow> pdr_edges \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow>
    (nat \<times> nat list) list \<Rightarrow> pdr_feasibility" where
  "pdr_follow_classes key edges previous [] witnesses =
    (case witnesses of [] \<Rightarrow> Spurious [] [] | (_, suffix) # _ \<Rightarrow> Feasible (rev suffix))"
| "pdr_follow_classes key edges previous (target # todo) witnesses =
    (let next = pdr_extend_witnesses key target edges witnesses
     in if next = [] then Spurious (map fst witnesses)
          (remdups (map fst (filter (\<lambda>(s, t). key s = previous \<and> key t = target) edges)))
        else pdr_follow_classes key edges target todo next)"

(* Start only from concrete initial states in the first abstract class. Replay
   the remaining classes from these starting points. *)
fun pdr_concretize :: "(nat \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> pdr_edges \<Rightarrow> nat list \<Rightarrow> pdr_feasibility" where
  "pdr_concretize key initial edges [] = Spurious [] []"
| "pdr_concretize key initial edges (start # todo) =
    pdr_follow_classes key edges start todo (map (\<lambda>s. (s, [s])) (filter (\<lambda>s. key s = start) initial))"

(* Count how many pairs of opposing candidate states a predicate separates. A
   higher score means the predicate distinguishes more of the conflicting
   pairs. *)
definition pdr_separation_score :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "pdr_separation_score reached alternate predicate =
     (let left = length (filter (List.member predicate) reached);
          right = length (filter (List.member predicate) alternate)
      in left * (length alternate - right) + right * (length reached - left))"

(* Choose a supplied predicate with the highest positive score. When none helps,
   try a singleton as a finite fallback. *)
definition pdr_split_predicate :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list list \<Rightarrow> nat list option" where
  "pdr_split_predicate reached alternate available =
     (let (score, best) = foldl (\<lambda>(best_score, best) candidate.
             let score = pdr_separation_score reached alternate candidate
             in if score > best_score then (score, candidate) else (best_score, best)) (0, []) available
      in if score > 0 then Some best else
           map_option (\<lambda>s. [s]) (List.find (\<lambda>s. \<not> List.member alternate s) reached))"

text \<open>The initial partition tracks the property. May transitions between classes
  permit paths that cannot be joined in the concrete model. At the first
  infeasible join, prefer the supplied predicate that separates the most pairs
  of concrete prefix endpoints and incompatible abstract predecessors.
  Singleton predicates give a finite fallback when the supplied vocabulary
  cannot split that conflict.\<close>

(* Build the abstract graph by mapping concrete endpoints to classes, then run
   PDR on that graph. Lift a proposed invariant back to concrete states.
   Replay a violation, and if replay fails add a distinguishing predicate and
   repeat with the remaining fuel. *)
fun pdr_refine :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> pdr_edges \<Rightarrow> nat list \<Rightarrow>
    nat list list \<Rightarrow> nat list list \<Rightarrow> observation" where
  "pdr_refine 0 fuel universe initial edges bad predicates available = measured Inconclusive 0"
| "pdr_refine (Suc rounds) fuel universe initial edges bad predicates available =
    (if fuel = 0 then measured Inconclusive 0
     else
       let key = pdr_signature predicates;
           classes = remdups (map key universe);
           abstract_initial = remdups (map key initial);
           abstract_edges = remdups (map (\<lambda>(s, t). (key s, key t)) edges);
           abstract_bad = remdups (map key bad);
           result = pdr_tick (run_pdr (fuel - 1) classes abstract_initial abstract_edges abstract_bad)
       in case outcome result of
           Certified invariant \<Rightarrow> result\<lparr>outcome := Certified (filter (\<lambda>s. List.member invariant (key s)) universe)\<rparr>
         | Violation path \<Rightarrow>
            (case pdr_concretize key initial edges path of
                Feasible history \<Rightarrow> result\<lparr>outcome := Violation history\<rparr>
              | Spurious reached alternate \<Rightarrow>
                (case pdr_split_predicate reached alternate available of
                    None \<Rightarrow> result\<lparr>outcome := Inconclusive\<rparr>
                  | Some predicate \<Rightarrow>
                      (if work result \<ge> fuel then result\<lparr>outcome := Inconclusive\<rparr>
                       else let refined = pdr_refine rounds (fuel - work result) universe initial edges bad
                         (predicates @ [predicate]) (filter (\<lambda>p. p \<noteq> predicate) available)
                       in refined\<lparr>work := work result + work refined, refinements := Suc (refinements refined)\<rparr>)))
         | _ \<Rightarrow> result)"

(* Begin with a partition that distinguishes bad states from other states. Bound
   the number of refinement rounds and share the overall work budget between
   rounds. *)
definition run_cegar :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> pdr_edges \<Rightarrow> nat list \<Rightarrow> nat list list \<Rightarrow> observation" where
  "run_cegar fuel universe initial edges bad predicates =
     pdr_refine (Suc (length predicates + length universe)) fuel universe initial edges bad [bad] predicates"

(* Evaluate a short chain where the only violating path has three edges. *)
lemma pdr_finds_three_step_path:
  "outcome (run_pdr 100 [0, 1, 2, 3] [0] [(0, 1), (1, 2), (2, 3)] [3]) = Violation [0, 1, 2, 3]"
  by eval

(* Check that a reachable cycle can be certified when the bad state is only
   reached from a disconnected component. *)
lemma pdr_proves_safe_cycle:
  "outcome (run_pdr 100 [0, 1, 2, 3] [0] [(0, 1), (1, 0), (2, 3)] [3]) = Certified [0, 1]"
  by eval

(* Check that an abstract connection disappears after refinement and that the
   returned outcome is a certificate. *)
lemma pdr_cegar_refines_spurious_path:
  "let result = run_cegar 100 [0, 1, 2, 3] [0] [(0, 1), (1, 0), (2, 3)] [3] [[0, 1]]
   in outcome result = Certified [0, 1] \<and> refinements result = 1"
  by eval

(* Check that refinement still returns a concrete trace when a violation really
   is reachable. *)
lemma pdr_cegar_preserves_counterexample:
  "outcome (run_cegar 100 [0, 1, 2, 3] [0] [(0, 1), (1, 2), (2, 3)] [3] [[0, 1]]) =
    Violation [0, 1, 2, 3]"
  by eval

(* Exercise the singleton fallback when the supplied predicates cannot explain an
   infeasible prefix. *)
lemma pdr_cegar_uses_finite_fallback:
  "let result = run_cegar 100 [0, 1, 2, 3] [0] [(0, 1), (1, 0), (2, 3)] [3] []
   in outcome result = Certified [0, 1] \<and> refinements result = 2"
  by eval

(* Verify that insufficient work budget returns an inconclusive verdict. *)
lemma pdr_cegar_reports_exhausted_fuel:
  "let result = run_cegar 2 [0, 1, 2, 3] [0] [(0, 1), (1, 0), (2, 3)] [3] [[0, 1]]
   in outcome result = Inconclusive \<and> work result = 2 \<and> refinements result = 0"
  by eval

end
