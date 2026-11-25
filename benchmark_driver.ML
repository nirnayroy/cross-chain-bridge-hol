structure Benchmark_Driver =
struct
  fun natural source =
    if size source > 0 andalso List.all Char.isDigit (String.explode source)
    then Bridge_Run.nat_of_integer (valOf (IntInf.fromString source))
    else raise Fail "Each job argument must be a nonnegative integer"

  fun natural_string value = IntInf.toString (Bridge_Run.integer_of_nat value)
  fun number conversion result = natural_string (conversion result)

  fun evidence result =
    String.concatWith "," (map natural_string (Bridge_Run.job_evidence result))

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

  fun arguments ("--script" :: _ :: parameters) = parameters
    | arguments parameters = parameters

  fun main () =
    let val parameters = arguments (CommandLine.arguments ())
    in run parameters; OS.Process.exit OS.Process.success end
    handle problem =>
      (TextIO.output (TextIO.stdErr, General.exnMessage problem ^ "\n");
       OS.Process.exit OS.Process.failure)
end
