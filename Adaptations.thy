theory Adaptations
  imports Core
begin

section \<open>Static checks on the symbolic operation graph\<close>

datatype axe_rule =
    RequiresGuard nat nat
  | RequiresFlow nat nat nat

text \<open>
  Each control-flow row records an operation, the protected resource it can
  reach, and the checks on that path. Data-flow edges are scoped to the
  operation so that dependencies on another route cannot satisfy its rule.
\<close>

definition adaptation_has :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "adaptation_has item items = list_ex ((=) item) items"

fun axe_flow_reachable ::
  "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "axe_flow_reachable 0 edges reached = reached"
| "axe_flow_reachable (Suc fuel) edges reached =
    (let more = map snd (filter (\<lambda>edge. adaptation_has (fst edge) reached) edges);
         enlarged = remdups (reached @ more)
     in if enlarged = reached then reached
        else axe_flow_reachable fuel edges enlarged)"

fun axe_rule_alerts ::
  "(nat \<times> nat \<times> nat list) list \<Rightarrow> (nat \<times> nat \<times> nat) list
    \<Rightarrow> axe_rule \<Rightarrow> nat list" where
  "axe_rule_alerts paths flow (RequiresGuard resource guard_id) =
    map fst (filter (\<lambda>(_, destination, checks).
      destination = resource \<and> \<not> adaptation_has guard_id checks) paths)"
| "axe_rule_alerts paths flow (RequiresFlow operation origin destination) =
    (let edges = map snd (filter (\<lambda>row. fst row = operation) flow);
         reached = axe_flow_reachable (length edges) edges [origin]
     in if adaptation_has destination reached then [] else [operation])"

definition smart_axe ::
  "(nat \<times> nat \<times> nat list) list \<Rightarrow> (nat \<times> nat \<times> nat) list
    \<Rightarrow> axe_rule list \<Rightarrow> observation" where
  "smart_axe paths flow rules =
    (let alerts = remdups (concat (map (axe_rule_alerts paths flow) rules))
     in measured (if rules = [] then Unsupported else
                    if alerts = [] then NoFinding else Alert alerts)
          (length paths + length flow))"

section \<open>Seeded sampling of model executions\<close>

definition bridge_random :: "nat \<Rightarrow> nat" where
  "bridge_random seed = (48271 * seed) mod 2147483647"

definition bridge_seed :: "nat \<Rightarrow> nat" where
  "bridge_seed seed = 1 + seed mod 2147483646"

definition bridge_successors ::
  "(nat \<times> nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "bridge_successors edges state =
    map snd (filter (\<lambda>edge. fst edge = state) edges)"

text \<open>
  A trial samples enabled labeled steps and correlates observations through the
  shared model state. Its oracle is the given finite set of failing observations.
  An exhausted trial or a dead end leaves no finding and permits a fresh trial.
\<close>

fun fuzz_trial ::
  "nat \<Rightarrow> (nat \<Rightarrow> (nat \<times> nat) list) \<Rightarrow> nat list
    \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat
    \<Rightarrow> (nat list option \<times> nat \<times> nat)" where
  "fuzz_trial 0 enabled bad seed state history steps =
    (if adaptation_has state bad then Some (rev (state # history)) else None, seed, steps)"
| "fuzz_trial (Suc depth) enabled bad seed state history steps =
    (if adaptation_has state bad then (Some (rev (state # history)), seed, steps)
     else
       (let choices = enabled state;
            next_seed = bridge_random seed
        in if choices = [] then (None, next_seed, steps)
           else fuzz_trial depth enabled bad next_seed
             (snd (choices ! (next_seed mod length choices))) (state # history) (Suc steps)))"

fun fuzz_trials ::
  "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> (nat \<times> nat) list)
    \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> observation" where
  "fuzz_trials 0 depth initial enabled bad seed steps = measured NoFinding steps"
| "fuzz_trials (Suc trials) depth initial enabled bad seed steps =
    (if initial = [] then measured NoFinding steps
     else
       (let start_seed = bridge_random seed;
            start = initial ! (start_seed mod length initial);
            (candidate, next_seed, total_steps) = fuzz_trial depth enabled bad start_seed start [] steps
        in case candidate of
             Some path \<Rightarrow> measured (Violation path) total_steps
           | None \<Rightarrow> fuzz_trials trials depth initial enabled bad next_seed total_steps))"

definition bridge_fuzz ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat \<times> nat) list
    \<Rightarrow> nat list \<Rightarrow> observation" where
  "bridge_fuzz seed trials depth initial edges bad =
    fuzz_trials trials depth initial (bridge_successors edges) bad (bridge_seed seed) 0"

section \<open>Goal-directed reduction and sketch feasibility\<close>

type_synonym location_dependencies = "(nat \<times> nat list \<times> nat list) list"
type_synonym abstract_location = "nat list"
type_synonym abstract_edge = "abstract_location \<times> nat \<times> abstract_location"
type_synonym sketch_node = "abstract_location \<times> (nat \<times> nat list) list"

text \<open>
  A dependency row gives the event and its read and write locations. A sketch
  records its current abstract location and all concrete paths that realize its
  prefix, keeping one reversed path per concrete state. The concrete frontier
  determines which suffixes are feasible, so identical frontiers can share work.
\<close>

fun scutum_location_closure ::
  "nat \<Rightarrow> location_dependencies \<Rightarrow> nat list \<Rightarrow> nat list" where
  "scutum_location_closure 0 dependencies retained = retained"
| "scutum_location_closure (Suc fuel) dependencies retained =
    (let reads = concat (map (fst \<circ> snd)
            (filter (\<lambda>(_, _, written). list_ex (\<lambda>i. adaptation_has i retained) written)
              dependencies));
         enlarged = sort (remdups (retained @ reads))
     in if enlarged = retained then retained
        else scutum_location_closure fuel dependencies enlarged)"

definition scutum_locations :: "location_dependencies \<Rightarrow> nat list \<Rightarrow> nat list" where
  "scutum_locations dependencies goals =
    scutum_location_closure (length (concat (map (fst \<circ> snd) dependencies)))
      dependencies (sort (remdups goals))"

fun scutum_backward ::
  "nat \<Rightarrow> abstract_edge list \<Rightarrow> abstract_location list \<Rightarrow> abstract_location list" where
  "scutum_backward 0 edges cone = cone"
| "scutum_backward (Suc fuel) edges cone =
    (let more = map fst (filter (\<lambda>(_, _, target). adaptation_has target cone) edges);
         enlarged = remdups (more @ cone)
     in if length enlarged = length cone then cone
        else scutum_backward fuel edges enlarged)"

definition scutum_frontier :: "sketch_node \<Rightarrow> nat list" where
  "scutum_frontier node = sort (map fst (snd node))"

fun unique_endpoint_paths ::
  "(nat \<times> nat list) list \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat list) list" where
  "unique_endpoint_paths [] seen = []"
| "unique_endpoint_paths ((state, path) # rest) seen =
    (if adaptation_has state seen then unique_endpoint_paths rest seen
     else (state, path) # unique_endpoint_paths rest (state # seen))"

definition scutum_step ::
  "(nat \<Rightarrow> (nat \<times> nat) list) \<Rightarrow> (nat \<Rightarrow> abstract_location)
    \<Rightarrow> (nat \<times> nat list) list \<Rightarrow> (nat \<times> abstract_location) \<Rightarrow> sketch_node" where
  "scutum_step enabled project paths choice =
    (let (event, destination) = choice;
         extensions = concat (map (\<lambda>(state, path).
           map (\<lambda>(_, target). (target, target # path))
             (filter (\<lambda>(action, target). action = event \<and> project target = destination)
               (enabled state))) paths)
     in (destination, unique_endpoint_paths extensions []))"

fun scutum_enqueue ::
  "sketch_node list \<Rightarrow> nat list list \<Rightarrow> (sketch_node list \<times> nat list list)" where
  "scutum_enqueue [] seen = ([], seen)"
| "scutum_enqueue (node # nodes) seen =
    (let key = scutum_frontier node
     in if key = [] \<or> adaptation_has key seen then scutum_enqueue nodes seen
        else (let (fresh, known) = scutum_enqueue nodes (key # seen)
              in (node # fresh, known)))"

fun scutum_search ::
  "nat \<Rightarrow> (nat \<Rightarrow> (nat \<times> nat) list) \<Rightarrow> (nat \<Rightarrow> abstract_location)
    \<Rightarrow> abstract_location list \<Rightarrow> abstract_edge list \<Rightarrow> nat list \<Rightarrow> nat list
    \<Rightarrow> sketch_node list \<Rightarrow> nat list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> observation" where
  "scutum_search fuel enabled project bad_locations abstract_edges bad outside pending seen steps blocks =
    (case pending of
       [] \<Rightarrow> \<lparr> outcome = Certified (remdups (outside @ concat seen)), work = steps, refinements = blocks \<rparr>
     | node # queue \<Rightarrow>
        (case fuel of
           0 \<Rightarrow> \<lparr> outcome = Inconclusive, work = steps, refinements = blocks \<rparr>
         | Suc remaining \<Rightarrow>
            (let (location, paths) = node;
                 witness = List.find (\<lambda>pair. adaptation_has (fst pair) bad) paths
             in case witness of
                 Some (_, path) \<Rightarrow> \<lparr> outcome = Violation (rev path), work = Suc steps, refinements = blocks \<rparr>
               | None \<Rightarrow>
                   (let choices = map snd (filter (\<lambda>edge. fst edge = location) abstract_edges);
                        candidates = map (scutum_step enabled project paths) choices;
                        infeasible = length (filter (\<lambda>p. snd p = []) candidates);
                        blocked_goal = (if adaptation_has location bad_locations then 1 else 0);
                        (fresh, known) = scutum_enqueue candidates seen
                    in scutum_search remaining enabled project bad_locations abstract_edges bad outside
                         (queue @ fresh) known (Suc steps) (blocks + infeasible + blocked_goal)))))"

text \<open>
  The backward cone excludes any abstract location that cannot reach a bad
  location in the projected graph. Exhausting the worklist yields a certificate
  containing concrete states outside that cone and the feasible states seen
  inside it. The shared checker decides whether that set is an inductive invariant.
\<close>

definition scutum ::
  "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> nat list
    \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> location_dependencies \<Rightarrow> nat list \<Rightarrow> observation" where
  "scutum budget universe initial edges bad state_fields dependencies goals =
    (if goals = [] then measured Unsupported 0
     else
       (let retained = scutum_locations dependencies goals;
            project = (\<lambda>state. map (\<lambda>i. (state_fields state) ! i) retained);
            abstract_edges = remdups (map (\<lambda>(source, event, target).
              (project source, event, project target)) edges);
            bad_locations = remdups (map project bad);
            cone = scutum_backward (length abstract_edges) abstract_edges bad_locations;
            outside = filter (\<lambda>state. \<not> adaptation_has (project state) cone) universe;
            kept_edges = filter (\<lambda>(source, _, target).
              adaptation_has source cone \<and> adaptation_has target cone) abstract_edges;
            starts = filter (\<lambda>loc. adaptation_has loc cone) (remdups (map project initial));
            nodes = map (\<lambda>loc. (loc, map (\<lambda>state. (state, [state]))
              (remdups (filter (\<lambda>state. project state = loc) initial)))) starts
        in scutum_search budget (bridge_successors edges) project bad_locations kept_edges bad outside
             nodes (map scutum_frontier nodes) 0 0))"

section \<open>Small regression cases\<close>

lemma smart_axe_follows_transitive_data_flow:
  "outcome (smart_axe [(1, 2, [3])] [(1, 4, 5), (1, 5, 6)]
      [RequiresGuard 2 3, RequiresFlow 1 4 6]) = NoFinding"
  by eval

lemma smart_axe_checks_dependencies_per_operation:
  "outcome (smart_axe [(1, 2, [])] [(2, 4, 6)] [RequiresFlow 1 4 6]) = Alert [1]"
  by eval

lemma fuzz_handles_initial_bad_and_empty_search:
  "outcome (bridge_fuzz 1 1 0 [0] [] [0]) = Violation [0] \<and>
   outcome (bridge_fuzz 1 0 0 [0] [] [0]) = NoFinding"
  by eval

lemma scutum_blocks_a_spurious_sketch:
  "let result = scutum 10 [0, 1, 2, 3] [0] [(0, 0, 1), (2, 1, 3)] [3]
        (\<lambda>state. [if state = 2 then 1 else state]) [] [0]
   in refinements result = 1 \<and>
       (case outcome result of Certified certificate \<Rightarrow> check_invariant [0] [(0, 1), (2, 3)] [3] certificate
        | _ \<Rightarrow> False)"
  by eval

end
