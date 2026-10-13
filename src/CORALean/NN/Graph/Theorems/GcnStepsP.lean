module

public import CORALean.NN.Graph.Operations.GcnSteps

@[expose] public section

/-!
# `gcnSteps` keeps the factor set throughout the chain

Every set in the chain carries `P`'s factors: the base case through the
sharing hypothesis, and every step through `gcnShared_p`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every set in the chain carries `P`'s factors: the base case through `hp`, and
every step through `gcnShared_p`. -/
theorem GNN.gcnSteps_p {N F : ℕ} (P : PolyZonotope (Mat ℝ N N)) (L : ℕ) :
    ∀ (W : Fin L → Mat ℝ F F) (H : PolyZonotope (Mat ℝ N F)) (hp : P.p = H.p),
      (GNN.gcnSteps P L W H hp).p = P.p := by
  induction L with
  | zero => exact fun _ _ hp => hp.symm
  | succ L ih => exact fun W H hp => ih (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
