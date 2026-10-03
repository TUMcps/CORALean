import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
import CORALean.ContSet.HPolytope.Real.Theorems.MemIneqsOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.EqZeroOfMulVecNonpos
import Mathlib.Analysis.Convex.Combination

/-!
# An AH-polytope in a convex hull of AH-polytopes, sufficiently

`[1, Cor. 3]`: `x̄ + X Px ⊆ conv(⋃ᵢ (ȳᵢ + Yᵢ Pᵢ))` if `Λᵢ Hx = Hᵢ Γᵢ`,
`Λᵢ hx ≤ λᵢ hᵢ + Hᵢ βᵢ`, `λ ≥ 0` and `(1, x̄, X) = ∑ᵢ (λᵢ, λᵢ ȳᵢ - Yᵢ βᵢ, Yᵢ Γᵢ)`
(`[1, Cor. 3, Eq. 28]`). `[1, Prop. 3]` mapped through `Yᵢ`, with the same gap: `{Hᵢ y ≤ λᵢ hᵢ}`
is `λᵢ Pᵢ` only for a nonempty bounded `Pᵢ`, and at `Yᵢ = I`, `ȳᵢ = 0` the printed
statement inherits that proposition's counterexample at an empty `Pᵢ`.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nx qx N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_subset_convexHull_ahPolytope_of_cert {ny qy : Fin N → ℕ}
    {xbar : Vec ℝ n} {X : Mat ℝ n nx} {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx}
    {ybar : Fin N → Vec ℝ n} {Y : (i : Fin N) → Mat ℝ n (ny i)}
    {Hy : (i : Fin N) → Mat ℝ (qy i) (ny i)} {hy : (i : Fin N) → Vec ℝ (qy i)}
    (hne : ∀ i, (HPolytope.ineqs (Hy i) (hy i)).construct.Nonempty)
    (hb : ∀ i, Bornology.IsBounded (HPolytope.ineqs (Hy i) (hy i)).construct)
    {Λ : (i : Fin N) → Mat ℝ (qy i) qx} {lam : Fin N → ℝ} {β : (i : Fin N) → Vec ℝ (ny i)}
    {Γ : (i : Fin N) → Mat ℝ (ny i) nx} (hΛ : ∀ i j k, 0 ≤ Λ i j k) (hlam : ∀ i, 0 ≤ lam i)
    (h1 : ∀ i, Λ i * Hx = Hy i * Γ i) (h2 : ∀ i, Λ i *ᵥ hx ≤ lam i • hy i + Hy i *ᵥ β i)
    (hsum : ∑ i, lam i = 1) (hc : ∑ i, (lam i • ybar i - Y i *ᵥ β i) = xbar)
    (hX : ∑ i, Y i * Γ i = X) :
    HPolytope.ahPolytope xbar X (HPolytope.ineqs Hx hx)
        ⊆ convexHull ℝ (⋃ i, HPolytope.ahPolytope (ybar i) (Y i)
        (HPolytope.ineqs (Hy i) (hy i))) := by -- --- PROOF ---
  rintro _ ⟨p, hp, rfl⟩
  have hq : ∀ i, Γ i *ᵥ p - β i ∈ (HPolytope.ineqs (Hy i) (lam i • hy i)).construct :=
    fun i => HPolytope.mem_ineqs_of_cert (hΛ i) (h1 i) (h2 i) hp
  -- `qᵢ = λᵢ zᵢ` with `zᵢ ∈ Pᵢ`, as for `[1, Prop. 3]`
  have hz : ∀ i, ∃ z ∈ (HPolytope.ineqs (Hy i) (hy i)).construct,
      Γ i *ᵥ p - β i = lam i • z := by
    intro i
    have hqi := HPolytope.mem_ineqs_iff.mp (hq i)
    rcases (hlam i).lt_or_eq with hpos | hzero
    · refine ⟨(lam i)⁻¹ • (Γ i *ᵥ p - β i), HPolytope.mem_ineqs_iff.mpr fun k => ?_, ?_⟩
      · rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hpos]
        simpa [mul_comm] using hqi k
      · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · refine ⟨(hne i).some, (hne i).some_mem, ?_⟩
      rw [← hzero, zero_smul]
      refine HPolytope.eq_zero_of_mulVec_nonpos (hne i) (hb i) fun k => ?_
      simpa [← hzero] using hqi k
  choose z hzmem hzeq using hz
  -- each summand is `λᵢ (ȳᵢ + Yᵢ zᵢ)`
  have hx' : xbar + X *ᵥ p = ∑ i, lam i • (ybar i + Y i *ᵥ z i) := by
    rw [← hc, ← hX, Matrix.sum_mulVec, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_add, ← mulVec_smul, ← hzeq i, mulVec_sub, mulVec_mulVec]
    abel
  rw [hx']
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hlam i) hsum
    fun i _ => subset_convexHull ℝ _ (Set.mem_iUnion.mpr ⟨i, z i, hzmem i, rfl⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
