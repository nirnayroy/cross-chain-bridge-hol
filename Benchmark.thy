theory Benchmark
  imports Bridge_Model PDR Adaptations
begin

(* Pair each credit rule with its index in the full rule list. Extract guard and
   field-flow rows, then choose the static checks for the selected family. An
   empty check list records that the property is unsupported by this
   adaptation. *)
definition axe_benchmark :: "nat \<Rightarrow> observation" where
  "axe_benchmark family =
     (let rows = filter (\<lambda>pair. operation (snd pair) = Credit)
             (zip [0..<length (family_rules family)] (family_rules family));
          paths = map (\<lambda>(i,r). (i,0,guards r)) rows;
          flows = concat (map (\<lambda>(i,r). map (\<lambda>(s,t). (i,s,t)) (field_links r)) rows);
          checks = (if family = 10 \<or> family div 2 = 0 then [RequiresGuard 0 0]
                 else if family div 2 = 1 then [RequiresGuard 0 1]
                 else if family div 2 = 3 then [RequiresGuard 0 2]
                 else if family div 2 = 4 then
                   concat (map (\<lambda>(i,r). [RequiresFlow i 0 2, RequiresFlow i 1 3]) rows)
                 else [])
      in smart_axe paths flows checks)"

(* This is the shared entry point for the generated executable. Check the case
   and transfer count, construct the model, dispatch by method number, then
   validate the method's evidence against the same initial states, edges, and
   property. *)
definition run_job :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> observation" where
  "run_job family transfer_count method budget seed =
     (if family > 10 \<or> transfer_count = 0 \<or> transfer_count > 2 then measured Unsupported 0
      else let vertices = universe family transfer_count;
               labelled = labelled_edges family transfer_count;
               edges = map (\<lambda>(s,e,t). (s,t)) labelled;
               bad = bad_states family transfer_count;
               result = (if method = 0 then start_search budget True initial_states edges bad
                  else if method = 1 then run_cegar budget vertices initial_states edges bad (predicate_columns family transfer_count)
                  else if method = 2 then run_pdr budget vertices initial_states edges bad
                  else if method = 3 then axe_benchmark family
                  else if method = 4 then bridge_fuzz seed budget 16 initial_states labelled bad
                  else if method = 5 then scutum budget vertices initial_states labelled bad
                    (state_columns transfer_count) (dependencies family transfer_count) [0..<transfer_count]
                  else if method = 6 then start_search budget False initial_states edges bad
                  else measured Unsupported 0)
           in validate initial_states edges bad result)"

(* Encode each HOL verdict as a small integer understood by the Python runner. A
   wildcard payload means the number depends on the constructor alone. *)
fun status_number :: "verdict \<Rightarrow> nat" where
  "status_number (Certified _) = 0"
| "status_number (Violation _) = 1"
| "status_number (Alert _) = 2"
| "status_number NoFinding = 3"
| "status_number Inconclusive = 4"
| "status_number Unsupported = 5"

(* Extract the verdict field and translate it to the wire status number. *)
definition job_status :: "observation \<Rightarrow> nat" where
  "job_status job = status_number (outcome job)"

(* The path lists both endpoints. A list of length n therefore represents n minus
   one transitions. Only a violation has a witness depth. *)
definition job_depth :: "observation \<Rightarrow> nat" where
  "job_depth job = (case outcome job of Violation path \<Rightarrow> length path - 1 | _ \<Rightarrow> 0)"

(* Expose the method's work counter. Different algorithms count different units,
   which the report explains. *)
definition job_work :: "observation \<Rightarrow> nat" where
  "job_work job = work job"

(* Expose the refinement counter for algorithms that use it. *)
definition job_refinements :: "observation \<Rightarrow> nat" where
  "job_refinements job = refinements job"

(* Return the constructor payload as a list for JSON output. Its meaning depends
   on whether the result is a certificate, a trace, or a static alert. *)
definition job_evidence :: "observation \<Rightarrow> nat list" where
  "job_evidence job = (case outcome job of Certified certificate \<Rightarrow> certificate
    | Violation path \<Rightarrow> path | Alert operations \<Rightarrow> operations | _ \<Rightarrow> [])"

(* Run the same case at two depth bounds and check the expected statuses. by eval
   asks Isabelle to evaluate the concrete expressions. *)
lemma bounded_search_depth:
  "job_status (run_job 1 1 6 4 0) = 3 \<and>
   job_status (run_job 1 1 6 8 0) = 1 \<and>
   job_depth (run_job 1 1 6 8 0) = 6"
  by eval

(* Check that the safe model with a disconnected component requires at least one
   refinement before it is certified. *)
lemma benchmark_spurious_case:
  "let r = run_job 0 1 1 256 0 in job_status r = 0 \<and> job_refinements r > 0"
  by eval

(* Check the exhaustive oracle's verdict for the published-model fragment at both
   supported sizes. *)
lemma published_fragment_checked:
  "job_status (run_job 10 1 0 1000 0) = 0 \<and> job_status (run_job 10 2 0 1000 0) = 0"
  by eval

text \<open>A local final credit and a local final return are independently reachable
  in each synthetic control. The rule declarations are shared across those controls.\<close>

(* Replay known ordinary credit and return paths in every synthetic reference
   family. This checks that those operations can occur in the safe controls. *)
lemma reference_operations_reachable:
  "list_all (\<lambda>family. list_all (\<lambda>transfer_count.
     check_trace initial_states (ordinary_edges family transfer_count) [12] [0,2,4,6,10,12] \<and>
     check_trace initial_states (ordinary_edges family transfer_count) [16] [0,2,4,14,16]) [1,2]) [0,2,4,6,8]"
  by eval

(* Replay the credit path through the published snapshot at both model sizes. *)
lemma published_credit_reachable:
  "list_all (\<lambda>transfer_count. check_trace initial_states (ordinary_edges 10 transfer_count) [12] [0,2,4,34,12]) [1,2]"
  by eval

(* For each fixture, check that the state list has no duplicates, includes the
   initial state, and contains both endpoints of every edge. *)
lemma finite_graph_closed:
  "list_all (\<lambda>family. list_all (\<lambda>transfer_count.
     let states = universe family transfer_count in
       distinct states \<and> List.member states 0 \<and>
       list_all (\<lambda>(s,t). List.member states s \<and> List.member states t)
         (ordinary_edges family transfer_count)) [1,2]) [0..<11]"
  by eval

(* Generate Standard ML for these selected functions and their dependencies.
   module_name is the SML module name used by the driver. file_prefix
   identifies the generated file in the Isabelle session export. *)
export_code run_job job_status job_depth job_work job_refinements job_evidence nat_of_integer integer_of_nat
  in SML module_name Bridge_Run file_prefix Bridge_Run

end
