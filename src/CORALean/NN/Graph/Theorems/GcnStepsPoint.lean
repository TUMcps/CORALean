module

public import CORALean.NN.Graph.Operations.EvalSteps
public import CORALean.NN.Graph.Operations.GcnSteps
public import CORALean.NN.Graph.Theorems.GcnSharedPoint
public import CORALean.NN.Graph.Theorems.GcnStepsP

@[expose] public section

/-!
# The chain, at one factor vector

Induction on the number of steps, `gcnShared_point` at each: the chain's point is `evalSteps` at the
graph's own point, so one factor vector drives every step and a recurring edge weighs the same at
each of them.

The casts are the only bookkeeping. `gcnSteps_p` says every set in the chain has `P`'s factors, so
all of them are the identity; only the proofs they carry differ, and `Fin.cast` ignores its proof,
so a `show` on the whole goal discharges the difference.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `P` – polynomial zonotope of the graph
* `L` – number of steps
* `W` – weights of the steps
* `H` – polynomial zonotope of the node features
* `a` – factor vector

## Hypotheses
* `hp` – both sets share their factors

## Conclusion
* the chain's point is the iteration at the graph's point
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The chain's point at `a` is `evalSteps` at `P`'s point there, started from
the feature set's own point. -/
theorem GNN.gcnSteps_point {N F : ℕ} (P : PolyZonotope (Mat ℝ N N)) (L : ℕ)
    (W : Fin L → Mat ℝ F F) (H : PolyZonotope (Mat ℝ N F)) (hp : P.p = H.p)
    (a : Fin P.p → ℝ) : -- --- CONCL ---
    (GNN.gcnSteps P L W H hp).point (fun k => a (Fin.cast (GNN.gcnSteps_p P L W H hp) k))
      = GNN.evalSteps (P.point a) L W
          (H.point fun k => a (Fin.cast hp.symm k)) := by -- --- PROOF ---
  induction L generalizing H hp with
  | zero => rfl
  | succ L ih =>
      -- the head of the chain is a `gcnShared`, whose point the step lemma names
      show (GNN.gcnSteps P L (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl).point
            (fun k => a (Fin.cast (GNN.gcnSteps_p P L (fun i => W i.succ)
              (GNN.gcnShared (W 0) P H hp) rfl) k))
          = GNN.evalSteps (P.point a) L (fun i => W i.succ)
            (P.point a * H.point (fun k => a (Fin.cast hp.symm k)) * W 0)
      rw [← GNN.gcnShared_point (W 0) P H hp a]
      exact ih (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
