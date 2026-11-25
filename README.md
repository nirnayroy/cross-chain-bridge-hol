# Cross-chain bridge safety in Isabelle/HOL

This benchmark compares property-directed reachability with counterexample-guided abstraction refinement (PDR/CEGAR), concrete PDR, and model-level versions of SmartAxe, BridgeFuzz, and Scutum. Bounded breadth-first checking provides a depth-based baseline. The comparison measures what each method can establish on the same finite transition systems.

## VS Code Dev Container

Start Docker Desktop and install the **Dev Containers** extension in VS Code. On Apple Silicon, choose **Dev Containers: Clone Repository in Container Volume** from the Command Palette and paste the GitHub repository URL. If your local checkout is writable from Docker, you can open that folder and choose **Dev Containers: Reopen in Container**. [VS Code guide](https://code.visualstudio.com/docs/devcontainers/containers)

The configuration uses the official Isabelle2026 ARM image for Apple Silicon. On an x86-64 host, set `build.args.ISABELLE_IMAGE` in `.devcontainer/devcontainer.json` to `makarius/isabelle:Isabelle2026` before opening the container.

In the VS Code terminal, build the theories and run a quick check. Then run the full comparison when you're ready. The separate output directory keeps the published measurements available.

```sh
isabelle build -d . Bridge_Benchmark
python3 run_benchmark.py --oracle-only --case once-reference/1 --output /tmp/bridge-smoke
python3 run_benchmark.py --output results-local
```

If a local checkout is mounted read-only for the container user, use `--output /tmp/bridge-results` for the full run.

## Run the benchmark

From the directory containing this README, use Isabelle2026 and Python 3.9 or later on macOS or Linux. The runner builds the Isabelle session, extracts the generated Standard ML, and runs it with Isabelle's bundled Poly/ML. Set `--isabelle` to the path to `bin/isabelle` in your installation.

```sh
python3 run_benchmark.py --isabelle /path/to/Isabelle2026/bin/isabelle
```

You can also build the theories independently.

```sh
isabelle build -d . Bridge_Benchmark
```

The runner writes to `results/` by default. `--output` changes that directory. `--oracle-only` runs just the exhaustive labeling pass. `--help` lists the available options. [Comparison report](results/report.md) · [Raw results](results/runs.jsonl) · [Run metadata](results/metadata.json)

The reference run used the official Isabelle2026 ARM Linux image on Apple Silicon. To rerun with Docker, use the command below. The compiler and GMP package are used inside the disposable container to link the generated Standard ML engine.

```sh
mkdir -p results
docker run --rm --user root --entrypoint /bin/bash \
  --mount "type=bind,source=$PWD,target=/project,readonly" \
  --mount "type=bind,source=$PWD/results,target=/results" \
  makarius/isabelle:Isabelle2026_ARM -lc '
    apt-get update && apt-get install -y --no-install-recommends g++ libgmp-dev &&
    BRIDGE_ISABELLE_PROFILE=/tmp/bridge-isabelle-results \
      python3 /project/run_benchmark.py --isabelle /home/isabelle/Isabelle/bin/isabelle --output /results'
```

## Model and labels

`Bridge_Model.thy` defines a finite set of local protocol locations and guarded, labeled transitions. The locations record symbolic observations about submission, source finality, relayer delivery, and destination credit. An event changes one transfer ID at a time. Each instance starts with both modeled chains idle and all transfers absent. The graph permits independent interleaving across IDs, an optional delivery delay, early notices, and a separate scheduler bit. Authentication is a model condition. The asset is fixed and recipient and amount agreement are represented as Boolean observations. The scope is finite-prefix safety.

The manifest declares five pairs of synthetic cases. Each pair differs in one transition rule and has a designated property. The two sizes instantiate one or two independent transfer IDs. The reference and variation are experimental controls. Run the exhaustive reachability oracle to derive the label for every instance and check it against the manifest. It retains shortest paths by searching in breadth-first layers. The reference cases have checked paths to a credit and a return so their safety results don't rely on those operations being unreachable. The first pair also includes a disconnected component to exercise spurious counterexample refinement.

The published-model case is a finite interpretation of the lock, state update, and mint fragment of Marić, Scholz, and Subotić's fail-safe bridge. `Submitted` and `Final` represent a successful deposit and its finality. `PublishedSnapshot` represents the oracle update carrying the trusted source state. `Paid` represents a successful claim. In the model, claim is terminal per transfer and can happen once. The upstream theory also relies on a correct state-root update and proof verifier, represented here by the stipulated observation gate. The benchmark checks at-most-once credit in this fragment with its own reachability oracle. The full paper's payback theorem quantifies over future recovery operations and other users' interleavings. That is a separate property. [Paper](https://drops.dagstuhl.de/entities/document/10.4230/OASIcs.FMBC.2025.8) · [Pinned Isabelle formalization](https://github.com/filipmaric/bridge_formalization/tree/c099ef015d76a1749c4c1570083c6ce21bcc4500)

## Methods and evidence

- **PDR/CEGAR** applies frame-based predecessor blocking and clause propagation to a finite may abstraction. It checks proposed paths against the full graph and uses the first infeasible prefix to select a distinguishing predicate. Concrete PDR applies the same frame search directly to the full graph. Both use explicit finite state sets for relative inductiveness queries. [PDR](https://theory.stanford.edu/~arbrad/papers/IC3.pdf) · [CEGAR](https://doi.org/10.1184/R1/6604547)
- **SmartAxe** reads guard and field-dependency annotations on symbolic routes. Its expected guard associations are supplied as rules, and the data-flow check uses reachability within each route. An alert identifies a route that fails a rule. The refund and payout property requires history and has no rule in this adaptation. [SmartAxe](https://doi.org/10.1145/3643738)
- **BridgeFuzz** samples enabled labeled steps with a seeded generator. The model locations serve as correlated observations from the two chains and relayer. The comparison uses 30 seeds per instance and up to 64 samples of length 16 per seed. A successful sample gives a concrete trace in the model. [BridgeFuzz](https://doi.org/10.1145/3803525.3804980)
- **Scutum** starts with the locations the property reads and computes a backward dependency closure. It then searches the projected graph and checks the feasibility of candidate prefixes on the original graph. It skips blocked sketches and merges identical concrete frontiers. Exhaustion returns a proposed closure certificate. [Scutum](https://eprint.iacr.org/2024/1834)
- **Bounded checking** searches to depths 4, 8, and 16. Its verdict is either a checked violation or the absence of a finding within that bound. The exhaustive oracle uses a separate unbounded-in-depth run to saturation with a finite fuel cap large enough for this suite.

`Core.thy` proves that accepted invariants exclude every reachable bad state, and that accepted traces reach one. `Benchmark.thy` applies the same executable checker to definitive outputs from every method. A rejected certificate or trace yields `inconclusive`. Static alerts, bounded and sampled runs with no finding, and unsupported properties each have their own status. Evidence in the raw results uses symbolic state IDs for traces and invariants and zero-based rule indices for static alerts. A state ID encodes the two local location indices and scheduler bit using `encode_state` in `Bridge_Model.thy`.

These measurements apply to small closed protocol models. Each published method is adapted from the papers, and the metrics compare the implementations in this session. The model sizes measure the cost of interleaving independent transfers. They provide limited evidence about bridges with shared liquidity, consensus, or cryptographic state. [RAID taxonomy](https://doi.org/10.1145/3678890.3678894)
