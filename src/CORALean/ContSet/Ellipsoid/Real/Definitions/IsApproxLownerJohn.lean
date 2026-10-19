module

public import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The approximate Löwner-John ellipse

[1, Def. 1.2]: for `ε > 0` the ellipse `E(E, s)` is an `ε`-approximate Löwner-John ellipse of a
convex set `C ⊆ ℝⁿ` if `E(E/n², s) ⊆ C ⊆ E((1+ε) E, s)`, stated as printed, at the shape
matrices `E/n²` and `(1+ε) E` about the same center (`ofShape`, the checked constructor, as
`1 + ε` could be negative for `ε ≤ -1`, where the paper's `ε > 0` does not hold). For `ε = 0` and
the Löwner-John ellipse of [1, Thm. 1.1] that is `E(E/n², s) ⊆ C ⊆ E(E, s)`.

## Inputs
* `ε` – approximation factor
* `C` – convex set
* `E` – ellipsoid

## Output
* `E/n²` lies in `C` which lies in `(1+ε)E`

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 1.2]: `E(E/n², s) ⊆ C ⊆ E((1+ε)E, s)`. -/
noncomputable def Ellipsoid.IsApproxLownerJohn (ε : ℝ) (C : Set (Vec ℝ n)) (E : Ellipsoid n) :
    Prop :=
  (Ellipsoid.ofShape ((1 / (n : ℝ) ^ 2) • E.Q) E.q).construct ⊆ C
    ∧ C ⊆ (Ellipsoid.ofShape ((1 + ε) • E.Q) E.q).construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
