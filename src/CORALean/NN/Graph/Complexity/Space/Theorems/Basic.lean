module

public import CORALean.NN.Graph.Operations.Gcn
public import CORALean.NN.Graph.Operations.GcnShared
public import CORALean.NN.Graph.Operations.GcnUncertain
public import CORALean.NN.Graph.Operations.MessagePassingEnclosure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.NN.Graph.Operations.SumPool

@[expose] public section

/-!
# `NN/Graph/Complexity/Space/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  `GNN.gcn_h`  ======================================== --
-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `gcn`'s result. -/
theorem GNN.gcn_h (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (pZ : PolyZonotope (Mat ℝ N F₁)) :
    (GNN.gcn P W pZ).h = pZ.h := rfl


-- =======================================  `GNN.gcn_q`  ======================================== --
-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `gcn`'s result. -/
theorem GNN.gcn_q (P : Mat ℝ N N) (W : Mat ℝ F₁ F₂) (pZ : PolyZonotope (Mat ℝ N F₁)) :
    (GNN.gcn P W pZ).q = pZ.q := rfl


-- ===================================  `GNN.gcnUncertain_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `h` count of `gcnUncertain`'s result. -/
theorem GNN.gcnUncertain_h (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : (GNN.gcnUncertain W P H).h = (P.h + 1) * (H.h + 1) := rfl


-- ===================================  `GNN.gcnUncertain_p`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `p` count of `gcnUncertain`'s result. -/
theorem GNN.gcnUncertain_p (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : (GNN.gcnUncertain W P H).p = P.p + H.p := rfl


-- ===================================  `GNN.gcnUncertain_q`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `q` count of `gcnUncertain`'s result. -/
theorem GNN.gcnUncertain_q (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : (GNN.gcnUncertain W P H).q = 0 := rfl

end

section

open Matrix

variable {N m : ℕ}


-- =============================  `GNN.messagePassingEnclosure_q`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---

/-- The `q` count of `messagePassingEnclosure`'s result. -/
theorem GNN.messagePassingEnclosure_q (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : (GNN.messagePassingEnclosure R A U).q = 0 := rfl

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
