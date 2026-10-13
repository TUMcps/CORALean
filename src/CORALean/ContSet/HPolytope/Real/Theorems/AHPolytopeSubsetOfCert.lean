module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIneqsOfCert

@[expose] public section

/-!
# AH-polytope in AH-polytope, sufficiently

`[1, Thm. 1]`: `x̄ + X Px ⊆ ȳ + Y Py` if `X = Y Γ`, `ȳ - x̄ = Y β`, and some `Λ ≥ 0` has
`Λ Hx = Hy Γ`, `Λ hx ≤ hy + Hy β` (`[1, Thm. 1, Eq. 12]`). By `mem_ineqs_of_cert`,
`-β + Γ Px ⊆ Py` (`[1, Thm. 1, Eq. 17]`), and `Y` maps that into the circumbody. The printed
hypothesis that `Px` is full-dimensional is used only for the converse
(`ahPolytope_subset_iff_of_injective`), and is not needed here.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nx ny qx qy : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_subset_of_cert {xbar ybar : Vec ℝ n} {X : Mat ℝ n nx}
    {Y : Mat ℝ n ny} {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx} {Hy : Mat ℝ qy ny} {hy : Vec ℝ qy}
    {Γ : Mat ℝ ny nx} {β : Vec ℝ ny} {Λ : Mat ℝ qy qx}
    (hX : X = Y * Γ) (hβ : ybar - xbar = Y *ᵥ β)
    (hΛ : ∀ i j, 0 ≤ Λ i j) (h1 : Λ * Hx = Hy * Γ) (h2 : Λ *ᵥ hx ≤ hy + Hy *ᵥ β) :
    HPolytope.ahPolytope xbar X (HPolytope.ineqs Hx hx)
      ⊆ HPolytope.ahPolytope ybar Y (HPolytope.ineqs Hy hy) := by -- --- PROOF ---
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨Γ *ᵥ p - β, HPolytope.mem_ineqs_of_cert hΛ h1 h2 hp, ?_⟩
  -- `x̄ + Y Γ p = ȳ + Y (Γ p - β)` because `ȳ - x̄ = Y β`
  rw [hX, ← mulVec_mulVec, mulVec_sub, ← hβ]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
