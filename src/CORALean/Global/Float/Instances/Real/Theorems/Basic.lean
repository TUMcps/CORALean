module

public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# `Global/Float/Instances/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ======================================  `toReal_real`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

/-- `toReal` at the ℝ model is the identity. True by `rfl`, but a statement written once over the
scalar and read at `𝕋 := ℝ` mentions it, and a proof rewriting there needs it by name. -/
@[simp] theorem toReal_real (a : ℝ) : SoundFloatArithmetic.toReal a = a := rfl

end CORALean.Float


-- =====================================  `toRealMat_real`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {m n : ℕ}

/-- `toRealMat` at the ℝ model is the identity, by `rfl`, as `toRealVec_real` is for a vector.
A layer written once over the scalar states its map with `toRealMat W`; at `𝕋 := ℝ` this is
what turns that back into `W`. -/
@[simp] theorem toRealMat_real (M : Mat ℝ m n) : toRealMat M = M := rfl

end CORALean.Float


-- =====================================  `toRealVec_real`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {n : ℕ}

/-- `toRealVec` at the ℝ model is the identity, by `rfl`: the entrywise reading `toReal_real` is.
Named because a generic statement at `𝕋 := ℝ` carries it and a rewrite has to remove it. -/
@[simp] theorem toRealVec_real (v : Vec ℝ n) : toRealVec v = v := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
