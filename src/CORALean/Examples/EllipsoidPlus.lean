import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum
import CORALean.ContSet.Ellipsoid.Float.Instances
import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusScalingsAdmissible

/-!
# A precision parameter, named by the caller

`Ellipsoid.plus` carries a free parameter, so there is no `Plus` for instance search to find. What
there is instead is `plusInstance`, a `def` the caller applies to its own choice, and this file is
the evidence that that is enough: an algorithm written against `Plus` runs at an ellipsoid with no
line of it changed. `LinearSys.inputTaylorSum` is the algorithm because `Plus` and `Mtimes (Mat ℝ)`
are exactly what it asks for; the reachability loops still do not run at an ellipsoid, because
`Reduce`, `LinComb`, `OfInterval` and `Mtimes ℐ` are missing operations. Both layers take the same
parameter: the two scalings with the inequality they owe. No generic algorithm runs at the float
layer yet; there the instance is shown lawful and `⊞` reads at a float ellipsoid.

## Inputs
* `n` – dimension
* `s₁` – first scaling
* `s₂` – second scaling
* `sys` – linear system
* `r` – time step
* `U` – input ellipsoid

## Hypotheses
* `hne₁` – first scaling nonzero
* `hne₂` – second scaling nonzero
* `hs` – the scalings satisfy the plus inequality

## Output
* Taylor sums of the input ellipsoid by step count
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The input Taylor sum at an ellipsoid, the scalings fixed once for the whole
sum. `inputTaylorSum` is unchanged and unaware; the `letI` is the entire cost of
running it here. -/
noncomputable def ellipsoidInputTaylorSum {n : ℕ} {s₁ s₂ : ℝ} (hne₁ : s₁ ≠ 0)
    (hne₂ : s₂ ≠ 0) (hs : 1 / s₁ ^ 2 + 1 / s₂ ^ 2 ≤ 1)
    (sys : LinearSys ℝ n) (r : ℝ) (U : Ellipsoid n) : ℕ → Ellipsoid n :=
  letI := Ellipsoid.plusInstance hne₁ hne₂ hs
  sys.inputTaylorSum r U

/-- What the generic recursion unfolds to: the caller's scalings, in the
operation the representation actually implements. -/
example {n : ℕ} {s₁ s₂ : ℝ} (hne₁ : s₁ ≠ 0) (hne₂ : s₂ ≠ 0)
    (hs : 1 / s₁ ^ 2 + 1 / s₂ ^ 2 ≤ 1) (sys : LinearSys ℝ n) (r : ℝ)
    (U : Ellipsoid n) (i : ℕ) :
    ellipsoidInputTaylorSum hne₁ hne₂ hs sys r U (i + 1)
      = Ellipsoid.plus s₁ s₂ (ellipsoidInputTaylorSum hne₁ hne₂ hs sys r U i)
          (Mtimes.mtimes (sys.inputTerm r (i + 1)) U) :=
  rfl

/-- The instance is lawful, and its law is the operation's own theorem. -/
example {n : ℕ} {s₁ s₂ : ℝ} (hne₁ : s₁ ≠ 0) (hne₂ : s₂ ≠ 0)
    (hs : 1 / s₁ ^ 2 + 1 / s₂ ^ 2 ≤ 1) (E₁ E₂ : Ellipsoid n) :
    construct E₁ + construct E₂ ⊆ construct (Ellipsoid.plus s₁ s₂ E₁ E₂) := by
  letI := Ellipsoid.plusInstance hne₁ hne₂ hs
  exact Plus.plus_outer E₁ E₂

/-- A caller holding Kurzhanski and Varaiya's `l` is no worse off than before:
its two square roots discharge the three obligations. -/
example {n : ℕ} {l : ℝ} (hl : 0 < l) (E₁ E₂ : Ellipsoid n) :
    construct E₁ + construct E₂
      ⊆ construct (Ellipsoid.plus (Real.sqrt (1 + 1 / l)) (Real.sqrt (1 + l)) E₁ E₂) := by
  obtain ⟨hne₁, hne₂, hs⟩ := Ellipsoid.plus_scalings_admissible hl
  letI := Ellipsoid.plusInstance hne₁ hne₂ (le_of_eq hs)
  exact Plus.plus_outer E₁ E₂

end CORALean.Real

namespace CORALean.Float

open Pointwise ContSet SoundFloatArithmetic

/-- The same at the float layer, where the parameter is the two scalings and the
certificate they carry. Stated through `⊞`, so what is checked is that the
notation reads here at all. -/
example {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {s₁ s₂ : 𝕋}
    (hne₁ : toReal s₁ ≠ 0) (hne₂ : toReal s₂ ≠ 0)
    (hs : 1 / toReal s₁ ^ 2 + 1 / toReal s₂ ^ 2 ≤ 1) (E₁ E₂ : Ellipsoid 𝕋 n) :
    letI := Ellipsoid.plusInstance hne₁ hne₂ hs
    construct E₁ + construct E₂ ⊆ construct (E₁ ⊞ E₂) := by
  letI := Ellipsoid.plusInstance hne₁ hne₂ hs
  exact Plus.plus_outer E₁ E₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
