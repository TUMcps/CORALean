module

public import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetOfCert
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

/-!
# AH-polytope in AH-polytope, sufficiently, as printed

`[1, Thm. 1]` as the paper states it: for a full-dimensional `Px`, `x̄ + X Px ⊆ ȳ + Y Py` if
there exist `Γ`, `β` and `Λ ≥ 0` with `X = Y Γ`, `ȳ - x̄ = Y β`, `Λ Hx = Hy Γ` and
`Λ hx ≤ hy + Hy β` (`[1, Thm. 1, Eq. 12]`). `ahPolytope_subset_of_cert` proves the inclusion
from a given certificate with no full-dimensionality at all; this is the printed statement,
hypothesis and existential included, read off it.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nx ny qx qy : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], as printed: for a full-dimensional `Px`, the conditions (12) suffice for
`x̄ + X Px ⊆ ȳ + Y Py`. -/
theorem HPolytope.ahPolytope_subset_of_exists_cert {xbar ybar : Vec ℝ n} {X : Mat ℝ n nx}
    {Y : Mat ℝ n ny} {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx} {Hy : Mat ℝ qy ny} {hy : Vec ℝ qy}
    (_hfull : (interior (HPolytope.ineqs Hx hx).construct).Nonempty)
    (h : ∃ (Γ : Mat ℝ ny nx) (β : Vec ℝ ny) (Λ : Mat ℝ qy qx), X = Y * Γ ∧
        ybar - xbar = Y *ᵥ β ∧ (∀ i j, 0 ≤ Λ i j) ∧ Λ * Hx = Hy * Γ ∧
        Λ *ᵥ hx ≤ hy + Hy *ᵥ β) :
    HPolytope.ahPolytope xbar X (HPolytope.ineqs Hx hx)
      ⊆ HPolytope.ahPolytope ybar Y (HPolytope.ineqs Hy hy) := by
  obtain ⟨_, _, _, hX, hβ, hΛ, h1, h2⟩ := h
  exact HPolytope.ahPolytope_subset_of_cert hX hβ hΛ h1 h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
