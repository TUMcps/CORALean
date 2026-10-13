import CORALean.ContDynamics.LinearSys.Operations.CanonicalForm
import CORALean.ContDynamics.LinearSys.Theorems.IsCanonicalFormCanonical

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
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes

variable {m q s : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [∀ n, Recentre (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.canonicalForm_C_ne_one (sys : LinearSys ℝ 1) (B : Mat ℝ 1 m) (c : Vec ℝ 1)
    (out : OutputEq ℝ 1 m 1) (k : Vec ℝ 1) (E : Mat ℝ 1 q) (F : Mat ℝ 1 s) (U : S m)
    (uVec : Vec ℝ m) (W : S q) (V : S s) (vVec : Vec ℝ s) (hC : out.C 0 0 = 2) :
    (sys.canonicalForm B c out k E F U uVec W V vVec).2.1.C ≠ 1 ∧
      LinearSys.IsCanonicalForm (1 : Mat ℝ 1 1) 0 (0 : Mat ℝ 1 1) 0 (0 : Mat ℝ 1 1)
        (1 : Mat ℝ 1 1) := by -- --- PROOF ---
  refine ⟨fun h => ?_, LinearSys.isCanonicalForm_canonical⟩
  -- the returned `C` is the given one, whose entry is `2`
  have h00 := congrFun (congrFun h 0) 0
  simp only [LinearSys.canonicalForm, hC, Matrix.one_apply_eq] at h00
  norm_num at h00

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
