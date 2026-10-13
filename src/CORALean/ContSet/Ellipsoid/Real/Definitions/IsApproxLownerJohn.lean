import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Data.Real.Basic

/-!
# The approximate Löwner-John ellipse

[1, Def. 1.2]: for `ε > 0` the ellipse `E(E, s)` is an `ε`-approximate Löwner-John ellipse of a
convex set `C ⊆ ℝⁿ` if `E(E/n², s) ⊆ C ⊆ E((1+ε) E, s)`. Scaling the shape matrix `E` by `c²`
scales the generator by `c`, so in the generator form the inner ellipse has the generator `G/n`
and the outer one `√(1+ε) G`, about the same centre. For `ε = 0` and the Löwner-John ellipse of
[1, Thm. 1.1] that is `E(E/n², s) ⊆ C ⊆ E(E, s)`.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 1.2]: `E(E/n², s) ⊆ C ⊆ E((1+ε)E, s)`, as generators `G/n` and `√(1+ε) G`. -/
def Ellipsoid.IsApproxLownerJohn (ε : ℝ) (C : Set (Vec ℝ n)) (E : Ellipsoid n) : Prop :=
  (⟨E.k, E.q, (1 / (n : ℝ)) • E.G⟩ : Ellipsoid n).construct ⊆ C
    ∧ C ⊆ (⟨E.k, E.q, Real.sqrt (1 + ε) • E.G⟩ : Ellipsoid n).construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
