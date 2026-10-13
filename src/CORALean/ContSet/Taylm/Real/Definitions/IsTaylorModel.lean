import CORALean.ContSet.Taylm.Real.Taylm
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Taylor models in the source's sense

[1, Def. 1]: `(P, I)` is an `n`-th order Taylor model of `f` around `x₀` on `D` when `f` is
`n + 1` times continuously differentiable on an open set containing `D`, `P` is the `n`-th order
Taylor polynomial of `f` at `x₀`, and `f(x) ∈ P(x - x₀) + I` on `D`. Read in the normalized
coordinates the source's own implementation stores (the source's Section 3, "normalized to the
interval `[-1, 1]` with expansion point `0`"): `D` is the box and `x₀ = 0`.

`Taylm.Encloses` is the last clause alone, and is what every operation here keeps: once the
coefficients are rounded the polynomial is no longer the Taylor polynomial ([1, Thm. 3]).

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- The `N`-th order Taylor polynomial of `f` at `0`, `Σₖ₌₀ᴺ Dᵏf(0)(t, …, t) / k!`. -/
noncomputable def Taylm.taylorPoly (f : Vec ℝ n → ℝ) (N : ℕ) (t : Vec ℝ n) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), iteratedFDeriv ℝ k f 0 (fun _ => t) / (k.factorial : ℝ)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 1] at the model's own order: smooth enough near the box, the Taylor polynomial at
`0`, and the remainder interval enclosing the difference on the box. -/
def Taylm.IsTaylorModel (T : Taylm n) (f : Vec ℝ n → ℝ) : Prop :=
  (∃ U : Set (Vec ℝ n), IsOpen U ∧ Taylm.box n ⊆ U ∧ ContDiffOn ℝ (T.maxOrder + 1) f U) ∧
    (∀ t, T.poly t = Taylm.taylorPoly f T.maxOrder t) ∧ T.Encloses f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
