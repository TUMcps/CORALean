module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The scalar a layer computes in

`Scalar 𝕋` is a type whose matrices and vectors denote real ones: ℝ itself, or a
machine scalar read entrywise. It is all the exact layer needs to know about the
arithmetic an implementation runs, which is what lets one guarantee cover both.

`toRealVec` is not `toRealMat` at a single column: a vector `Vec 𝕋 n` is a
function `Fin n → 𝕋`, not a `Matrix`, so reading it needs its own field.

`toReal` reads one entry, and the two entrywise laws say `toRealMat` and `toRealVec` are that
reading applied to every entry. So a matrix built by placing existing entries, `0` and `1`
(see `ExactScalar`) reads back as the real matrix of those entries, at any scalar, rounded or not.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

-- Import guards (CONTRIBUTING, "Import guards and layering"): what must stay out of the closure.

-- Measure theory, whose import closure is larger than this whole layer.
assert_not_exists MeasureTheory.Measure
-- Probability, which sits on top of measure theory.
assert_not_exists ProbabilityTheory.IndepFun
-- Determinants and the spectral theory built on them.
assert_not_exists Matrix.det
-- The analytic special functions; exact enclosures of them belong higher up.
assert_not_exists Real.exp
-- Calculus, which only the dynamics layers need.
assert_not_exists HasDerivAt
-- Inner-product geometry; the sup norm is what this layer uses.
assert_not_exists InnerProductSpace
-- The entrywise layer sits above this file.
assert_not_imported CORALean.Global.Entrywise
-- The abstract set class sits above this file.
assert_not_imported CORALean.ContSet.ContSet.ContSet

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

class Scalar (𝕋 : Type) where
  toRealMat {m n : ℕ} : Mat 𝕋 m n → Mat ℝ m n
  toRealVec {n : ℕ} : Vec 𝕋 n → Vec ℝ n
  toReal : 𝕋 → ℝ
  toRealMat_apply {m n : ℕ} (M : Mat 𝕋 m n) (i : Fin m) (j : Fin n) :
    toRealMat M i j = toReal (M i j)
  toRealVec_apply {n : ℕ} (v : Vec 𝕋 n) (i : Fin n) : toRealVec v i = toReal (v i)

/-- ℝ stores itself. -/
instance : Scalar ℝ where
  toRealMat M := M
  toRealVec v := v
  toReal := id
  toRealMat_apply _ _ _ := rfl
  toRealVec_apply _ _ := rfl

/-- True by `rfl`, but a proof about the real layer has to rewrite with it. -/
@[simp] theorem Scalar.toRealMat_real {m n : ℕ} (M : Mat ℝ m n) : toRealMat M = M := rfl

/-- True by `rfl`, but a proof about the real layer has to rewrite with it. -/
@[simp] theorem Scalar.toRealVec_real {n : ℕ} (v : Vec ℝ n) : toRealVec v = v := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
