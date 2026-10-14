module

public import CORALean.ContSet.Taylm.Real.Definitions.Scaled
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Trace
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.SmulOuter
public import CORALean.ContSet.Taylm.Real.Theorems.SumOuter

@[expose] public section

/-!
# `ContSet/Taylm/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ==================================  `Taylm.degree_single`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A unit vector has degree one -/
theorem Taylm.degree_single (k : Fin n) : Taylm.degree (Pi.single k 1 : Fin n → ℕ) = 1 := by
  simp [Taylm.degree, Finset.sum_pi_single']


-- ===================================  `Taylm.monomial_add`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A monomial of a sum of exponents is the product of the monomials. -/
theorem Taylm.monomial_add (e₁ e₂ : Fin n → ℕ) (t : Vec ℝ n) :
    Taylm.monomial (e₁ + e₂) t = Taylm.monomial e₁ t * Taylm.monomial e₂ t := by
  simp [Taylm.monomial, pow_add, Finset.prod_mul_distrib]


-- ==================================  `Taylm.monomial_zero`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The monomial of the zero exponent is `1`. -/
theorem Taylm.monomial_zero (t : Vec ℝ n) : Taylm.monomial 0 t = 1 := by
  simp [Taylm.monomial]


-- ===================================  `Taylm.const_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Taylm.const` encloses the constant -/
theorem Taylm.const_outer (c : ℝ) (N : ℕ) : (Taylm.const n c N).Encloses fun _ => c := by
  intro t _
  simp [Taylm.const, Taylm.poly, Taylm.monomial_zero]


-- ===================================  `Taylm.mtimes_outer`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Row `i` encloses `Σⱼ M i j fⱼ`, the image of the enclosed functions under `M`. -/
theorem Taylm.mtimes_outer {k m : ℕ} (M : Mat ℝ k m) {T : Fin m → Taylm n}
    {f : Fin m → Vec ℝ n → ℝ} (h : ∀ j, (T j).Encloses (f j)) (i : Fin k) :
    (Taylm.mtimes M T i).Encloses fun t => ∑ j, M i j * f j t :=
  Taylm.sum_outer fun j => Taylm.smul_outer (M i j) (h j)


-- ===================================  `Taylm.polyOf_ofFn`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The polynomial of a term family is the sum of its terms. -/
theorem Taylm.polyOf_ofFn {h : ℕ} (F : Fin h → ℝ × (Fin n → ℕ)) (t : Vec ℝ n) :
    Taylm.polyOf (List.ofFn F) t = ∑ j, (F j).1 * Taylm.monomial (F j).2 t := by
  simp [Taylm.polyOf, List.sum_ofFn]


-- ===================================  `Taylm.trace_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Taylm.trace` encloses the trace -/
theorem Taylm.trace_outer {k : ℕ} {A : Fin k → Fin k → Taylm n}
    {f : Fin k → Fin k → Vec ℝ n → ℝ} (h : ∀ i j, (A i j).Encloses (f i j)) :
    (Taylm.trace A).Encloses fun t => ∑ i, f i i t :=
  Taylm.sum_outer fun i => h i i


-- ===================================  `Taylm.uplus_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Taylm.uplus` encloses the function -/
theorem Taylm.uplus_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.uplus.Encloses f := h


-- ==================================  `Taylm.weight_append`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `weight` is a sum over the term list, so it adds over `++`, which is how `plus` joins two
models. -/
@[simp] theorem Taylm.weight_append (L₁ L₂ : List (ℝ × (Fin n → ℕ))) (h : ℝ) :
    Taylm.weight (L₁ ++ L₂) h = Taylm.weight L₁ h + Taylm.weight L₂ h := by
  simp [Taylm.weight]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
