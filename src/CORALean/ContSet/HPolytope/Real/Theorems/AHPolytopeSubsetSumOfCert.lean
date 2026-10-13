import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
import CORALean.ContSet.HPolytope.Real.Theorems.MemIneqsOfCert
import Mathlib.Data.Matrix.Basic

/-!
# An AH-polytope in a Minkowski sum of AH-polytopes, sufficiently

`[1, Prop. 2]`: `x̄ + X Px ⊆ ⨁ᵢ (ȳᵢ + Yᵢ Pᵢ)` if `Λᵢ Hx = Hᵢ Γᵢ`, `Λᵢ hx ≤ hᵢ + Hᵢ βᵢ`,
`∑ᵢ (ȳᵢ - Yᵢ βᵢ) = x̄` and `∑ᵢ Yᵢ Γᵢ = X` (`[1, Prop. 2, Eq. 24]`). Each summand gets its own affine
image `-βᵢ + Γᵢ Px ⊆ Pᵢ` (`mem_ineqs_of_cert`), and the images add up to the inbody. Only
sufficient: deciding `P = P₁ ⊕ P₂` is NP-complete.

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

variable {n nx qx N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_subset_sum_of_cert {ny qy : Fin N → ℕ} {xbar : Vec ℝ n}
    {X : Mat ℝ n nx} {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx} {ybar : Fin N → Vec ℝ n}
    {Y : (i : Fin N) → Mat ℝ n (ny i)} {Hy : (i : Fin N) → Mat ℝ (qy i) (ny i)}
    {hy : (i : Fin N) → Vec ℝ (qy i)} {Λ : (i : Fin N) → Mat ℝ (qy i) qx}
    {Γ : (i : Fin N) → Mat ℝ (ny i) nx} {β : (i : Fin N) → Vec ℝ (ny i)}
    (hΛ : ∀ i j k, 0 ≤ Λ i j k) (h1 : ∀ i, Λ i * Hx = Hy i * Γ i)
    (h2 : ∀ i, Λ i *ᵥ hx ≤ hy i + Hy i *ᵥ β i)
    (hc : ∑ i, (ybar i - Y i *ᵥ β i) = xbar) (hX : ∑ i, Y i * Γ i = X) :
    HPolytope.ahPolytope xbar X (HPolytope.ineqs Hx hx) ⊆
      {x | ∃ q : (i : Fin N) → Vec ℝ (ny i),
        (∀ i, q i ∈ (HPolytope.ineqs (Hy i) (hy i)).construct) ∧
        x = ∑ i, (ybar i + Y i *ᵥ q i)} := by -- --- PROOF ---
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨fun i => Γ i *ᵥ p - β i, fun i => HPolytope.mem_ineqs_of_cert (hΛ i) (h1 i) (h2 i) hp,
    ?_⟩
  -- the summands' offsets and maps add up to the inbody's
  rw [← hc, ← hX, Matrix.sum_mulVec, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_sub, mulVec_mulVec]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
