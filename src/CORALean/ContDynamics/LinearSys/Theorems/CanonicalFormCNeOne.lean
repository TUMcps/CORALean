module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalForm
public import CORALean.ContDynamics.LinearSys.Theorems.IsCanonicalFormCanonical

@[expose] public section

/-!
# `canonicalForm` keeps `C`, which `isCanonicalForm` tests against the identity

CORA's `isCanonicalForm.m` [1] rejects `C ≠ eye(nrOfOutputs)`, yet its docstring says canonical
form is `y = Cx + v` and `canonicalForm` returns the original `C`. With a `1 × 1` output
matrix `C = 2` the system `canonicalForm` returns has `C ≠ I`, though it is in canonical
form for every other entry.

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [∀ n, Recentre (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The system `ẋ = 0`, `y = 2 x`, with no inputs, disturbances or noises. -/
theorem LinearSys.canonicalForm_C_ne_one (U : S 0) (uVec : Vec ℝ 0) (W : S 0) (V : S 0)
    (vVec : Vec ℝ 0) :
    let sys : LinearSys ℝ 1 := ⟨0, 1, 0, 0, 0, 0, 0, !![2], 0, 0, 0, 0⟩
    (sys.canonicalForm U uVec W V vVec).1.C ≠ (1 : Mat ℝ 1 1) ∧
      (sys.canonicalForm U uVec W V vVec).1.IsCanonicalForm := by -- --- PROOF ---
  intro sys
  refine ⟨fun h => ?_, LinearSys.isCanonicalForm_canonical sys U uVec W V vVec⟩
  -- the returned `C` is the given one, whose entry is `2`
  have h00 := congrFun (congrFun h (0 : Fin 1)) (0 : Fin 1)
  simp only [sys, LinearSys.canonicalForm, Matrix.one_apply_eq] at h00
  norm_num at h00

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
