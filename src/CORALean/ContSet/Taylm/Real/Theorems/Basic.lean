module

public import CORALean.ContSet.Taylm.Real.Definitions.Scaled
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Trace
public import CORALean.ContSet.Taylm.Real.Theorems.SmulOuter
public import CORALean.ContSet.Taylm.Real.Theorems.SumOuter

@[expose] public section

/-!
# `ContSet/Taylm/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ===================================  `Taylm.const_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `Taylm.const` encloses the constant -/
theorem Taylm.const_outer (c : ℝ) (N : ℕ) : (Taylm.const n c N).Encloses fun _ => c := by
  intro t _
  simp [Taylm.const, Taylm.poly, Taylm.monomial_zero]

end CORALean.Real


-- ==================================  `Taylm.degree_single`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- A unit vector has degree one -/
theorem Taylm.degree_single (k : Fin n) : Taylm.degree (Pi.single k 1 : Fin n → ℕ) = 1 := by
  simp [Taylm.degree, Finset.sum_pi_single']

end CORALean.Real


-- ===================================  `Taylm.mtimes_outer`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- Row `i` encloses `Σⱼ M i j fⱼ`, the image of the enclosed functions under `M`. -/
theorem Taylm.mtimes_outer {k m : ℕ} (M : Mat ℝ k m) {T : Fin m → Taylm n}
    {f : Fin m → Vec ℝ n → ℝ} (h : ∀ j, (T j).Encloses (f j)) (i : Fin k) :
    (Taylm.mtimes M T i).Encloses fun t => ∑ j, M i j * f j t :=
  Taylm.sum_outer fun j => Taylm.smul_outer (M i j) (h j)

end CORALean.Real


-- ===================================  `Taylm.trace_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `Taylm.trace` encloses the trace -/
theorem Taylm.trace_outer {k : ℕ} {A : Fin k → Fin k → Taylm n}
    {f : Fin k → Fin k → Vec ℝ n → ℝ} (h : ∀ i j, (A i j).Encloses (f i j)) :
    (Taylm.trace A).Encloses fun t => ∑ i, f i i t :=
  Taylm.sum_outer fun i => h i i

end CORALean.Real


-- ===================================  `Taylm.uplus_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `Taylm.uplus` encloses the function -/
theorem Taylm.uplus_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.uplus.Encloses f := h

end CORALean.Real


-- ==================================  `Taylm.weight_append`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `weight` is a sum over the term list, so it adds over `++`, which is how `plus` joins two
models. -/
@[simp] theorem Taylm.weight_append (L₁ L₂ : List (ℝ × (Fin n → ℕ))) (h : ℝ) :
    Taylm.weight (L₁ ++ L₂) h = Taylm.weight L₁ h + Taylm.weight L₂ h := by
  simp [Taylm.weight]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
