module

public import CORALean.ContSet.Taylm.Real.Definitions.CodeList
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The scaling constant of a code list

[1, Thm. 2]'s second claim, that a code list keeps the `(n+1)`-st order scaling, carried through
the operations whose constants `Thm. 1`'s lemmas give in closed form: `+`, `·`, negation,
constants, and the intrinsics `exp`, `sin`, `cos`, whose derivative bounds need no domain.
`IsScalingFragment` is that part of the code lists; `codeScale N e C` the constant a run of `e`
from inputs scaled by `C` is scaled by — a function of `N` and `C`, never of `h`.

## Inputs
* `m` – number of variables
* `N` – expansion order
* `C` – input scaling constant

## Output
* scaling constant of a run of the code list

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- The code lists `codeScale` follows: only `exp`, `sin` and `cos` among the intrinsics. -/
def Taylm.CodeList.IsScalingFragment {α : Type} {m : ℕ} : Taylm.CodeList α m → Prop
  | .var _ => True
  | .const _ => True
  | .add a b => a.IsScalingFragment ∧ b.IsScalingFragment
  | .mul a b => a.IsScalingFragment ∧ b.IsScalingFragment
  | .neg a => a.IsScalingFragment
  | .intr s a => (s = .exp ∨ s = .sin ∨ s = .cos) ∧ a.IsScalingFragment


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The scaling constant of a run of `e` at order `N` from inputs scaled by `C`. -/
noncomputable def Taylm.codeScale {m : ℕ} (N : ℕ) (C : ℝ) : Taylm.CodeList ℝ m → ℝ
  | .var _ => C
  | .const c => |c|
  | .add a b => Taylm.codeScale N C a + Taylm.codeScale N C b
  | .mul a b => 4 * (Taylm.codeScale N C a * Taylm.codeScale N C b)
  | .neg a => Taylm.codeScale N C a
  | .intr .exp a =>
    Real.exp (Taylm.codeScale N C a) * ∑ k : Fin (N + 1), (8 * Taylm.codeScale N C a) ^ (k : ℕ)
      + Real.exp (3 * Taylm.codeScale N C a) * (2 * Taylm.codeScale N C a) ^ (N + 1)
  | .intr _ a =>
    1 * ∑ k : Fin (N + 1), (8 * Taylm.codeScale N C a) ^ (k : ℕ)
      + 1 * (2 * Taylm.codeScale N C a) ^ (N + 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
