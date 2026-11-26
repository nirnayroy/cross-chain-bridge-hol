structure Benchmark_Driver =
struct
  (* fun defines an SML function. Accept only strings of digits and convert via
     IntInf, SML's arbitrary-precision integer type, to the natural type
     exported by Isabelle. *)
  fun natural source =
    if size source > 0 andalso List.all Char.isDigit (String.explode source)
    then Bridge_Run.nat_of_integer (valOf (IntInf.fromString source))
    else raise Fail "Each job argument must be a nonnegative integer"

  (* Convert a HOL natural back to decimal text so it can appear as a JSON
     number. *)
  fun natural_string value = IntInf.toString (Bridge_Run.integer_of_nat value)
  (* Pass an accessor as conversion. Apply it to a result, then render the
     returned number. *)
  fun number conversion result = natural_string (conversion result)

  (* Map the decimal conversion over the list of evidence IDs and join the
     entries into a JSON array. *)
  fun evidence result =
    String.concatWith "," (map natural_string (Bridge_Run.job_evidence result))

  (* This list pattern matches exactly five CLI strings. let introduces local
     values. Evaluate one HOL job, measure elapsed time, and print one JSON
     line. *)
  fun run [family, transfers, method, budget, seed] =
        let
          val timer = Timer.startRealTimer ()
          val result = Bridge_Run.run_job (natural family) (natural transfers)
            (natural method) (natural budget) (natural seed)
          val elapsed = Time.toMicroseconds (Timer.checkRealTimer timer)
        in
          print (String.concat ["{\"status\":", number Bridge_Run.job_status result,
            ",\"depth\":", number Bridge_Run.job_depth result,
            ",\"work\":", number Bridge_Run.job_work result,
            ",\"refinements\":", number Bridge_Run.job_refinements result,
            ",\"evidence\":[", evidence result, "]",
            ",\"compute_us\":", LargeInt.toString elapsed, "}\n"])
        end
    | run _ = raise Fail "Expected FAMILY TRANSFERS METHOD BUDGET SEED"

  (* The :: operator matches a list's head and tail. Here the pattern skips the
     script launcher flag and script path when present. *)
  fun arguments ("--script" :: _ :: parameters) = parameters
    | arguments parameters = parameters

  (* The unit value () indicates no input to main. handle catches exceptions,
     writes the diagnostic to stderr, and returns a failing process exit code. *)
  fun main () =
    let val parameters = arguments (CommandLine.arguments ())
    in run parameters; OS.Process.exit OS.Process.success end
    handle problem =>
      (TextIO.output (TextIO.stdErr, General.exnMessage problem ^ "\n");
       OS.Process.exit OS.Process.failure)
end
