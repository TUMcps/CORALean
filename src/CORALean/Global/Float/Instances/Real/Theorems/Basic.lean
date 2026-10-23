module

public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# `Global/Float/Instances/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

variable {m n : ℕ}


-- ======================================  `addDown_real`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `addDown` at the ℝ model is `+`. -/
@[simp] theorem addDown_real (a b : ℝ) : FloatOps.addDown a b = a + b := rfl


-- =======================================  `addUp_real`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `addUp` at the ℝ model is `+`. -/
@[simp] theorem addUp_real (a b : ℝ) : FloatOps.addUp a b = a + b := rfl


-- ======================================  `maximum_real`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `maximum` at the ℝ model is `max`. -/
@[simp] theorem maximum_real (a b : ℝ) : FloatOps.maximum a b = max a b := rfl


-- ======================================  `minimum_real`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minimum` at the ℝ model is `min`. -/
@[simp] theorem minimum_real (a b : ℝ) : FloatOps.minimum a b = min a b := rfl


-- ========================================  `one_real`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `one` at the ℝ model is `1`. -/
@[simp] theorem one_real : (FloatOps.one : ℝ) = 1 := rfl


-- ======================================  `subDown_real`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `subDown` at the ℝ model is `-`. -/
@[simp] theorem subDown_real (a b : ℝ) : subDown a b = a - b := (sub_eq_add_neg a b).symm


-- =======================================  `subUp_real`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `subUp` at the ℝ model is `-`. -/
@[simp] theorem subUp_real (a b : ℝ) : subUp a b = a - b := (sub_eq_add_neg a b).symm


-- ======================================  `toReal_real`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toReal` at the ℝ model is the identity. True by `rfl`, but a statement written once over the
scalar and read at `𝕋 := ℝ` mentions it, and a proof rewriting there needs it by name. -/
@[simp] theorem toReal_real (a : ℝ) : SoundFloatArithmetic.toReal a = a := rfl


-- =====================================  `toRealMat_real`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toRealMat` at the ℝ model is the identity, by `rfl`, as `toRealVec_real` is for a vector.
A layer written once over the scalar states its map with `toRealMat W`; at `𝕋 := ℝ` this is
what turns that back into `W`. -/
@[simp] theorem toRealMat_real (M : Mat ℝ m n) : toRealMat M = M := rfl


-- =====================================  `toRealVec_real`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toRealVec` at the ℝ model is the identity, by `rfl`: the entrywise reading `toReal_real` is.
Named because a generic statement at `𝕋 := ℝ` carries it and a rewrite has to remove it. -/
@[simp] theorem toRealVec_real (v : Vec ℝ n) : toRealVec v = v := rfl


-- =======================================  `zero_real`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `zero` at the ℝ model is `0`. -/
@[simp] theorem zero_real : (FloatOps.zero : ℝ) = 0 := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
