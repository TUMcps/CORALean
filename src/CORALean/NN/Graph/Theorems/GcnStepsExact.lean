module

public import CORALean.NN.Graph.Operations.EvalSteps
public import CORALean.NN.Graph.Operations.GcnSteps
public import CORALean.NN.Graph.Theorems.GcnSharedExact
public import CORALean.NN.Graph.Theorems.GcnSharedPoint

@[expose] public section

/-!
# The chain is exactly what it computes

Induction on the number of steps, `gcnShared_exact` at the last one: the set the chain returns is
exactly the image of the admissible factor box under the iteration `evalSteps`, so `L` steps at one
uncertain graph cost nothing beyond the enclosure of the graph itself.

Stated at `L + 1` steps, because at `L = 0` the chain is `H` unchanged and the claim is false there
whenever `H` has an independent block. `H.q = 0` would repair it but rules out the feature sets the
layer is written for, while every set the chain produces has `q = 0`. That `bilin` drops `H`'s
independent block is also why the statement reads over `H.point`.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `P` – polynomial zonotope of the graph
* `L` – number of steps minus one
* `W` – weights of the steps
* `H` – polynomial zonotope of the node features

## Hypotheses
* `hp` – both sets share their factors

## Conclusion
* the chain is exactly the image of the admissible factor box under the iteration
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `L + 1` steps at one uncertain graph are exactly the values the iteration
takes over the admissible factor vectors. -/
theorem GNN.gcnSteps_exact {N F : ℕ} (P : PolyZonotope (Mat ℝ N N)) (L : ℕ)
    (W : Fin (L + 1) → Mat ℝ F F) (H : PolyZonotope (Mat ℝ N F)) (hp : P.p = H.p) : -- --- CONCL ---
    (fun a : Fin P.p → ℝ =>
        GNN.evalSteps (P.point a) (L + 1) W (H.point fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      = (GNN.gcnSteps P (L + 1) W H hp).construct := by -- --- PROOF ---
  induction L generalizing H hp with
  | zero =>
      -- a single step is `gcnShared`, and `evalSteps` at one step is its product
      exact GNN.gcnShared_exact (W 0) P H hp
  | succ L ih =>
      -- peel the first step off both sides: what is left is a chain one shorter
      refine Eq.trans ?_ (ih (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl)
      refine Set.image_congr' fun a => ?_
      show GNN.evalSteps (P.point a) (L + 1) (fun i => W i.succ)
            (P.point a * H.point (fun k => a (Fin.cast hp.symm k)) * W 0)
          = GNN.evalSteps (P.point a) (L + 1) (fun i => W i.succ)
            ((GNN.gcnShared (W 0) P H hp).point a)
      rw [GNN.gcnShared_point]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
