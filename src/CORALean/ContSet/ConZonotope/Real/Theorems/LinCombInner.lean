import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
import CORALean.ContSet.ConZonotope.Real.Theorems.SumUnivLinComb
import CORALean.ContSet.HPolytope.Real.Operations.AbsLeOfUnitBoxRows
import CORALean.ContSet.HPolytope.Real.Operations.RowsOfMemHalfScaledComap

/-!
# `ConZonotope.linComb` is no larger than the hull

The reverse of `linComb_outer`, and with it the operation is exactly the convex
hull of the two sets. What a weighted coefficient block gives back is a point of
its own set: above weight zero by dividing through, and at weight zero because
the weighted box pins the block to the origin, leaving the other side's point
alone.

Both sets have to be nonempty, and that is not a technicality: at weight zero
the combination is a point of the second set, which is a *segment* only if the
first has a point to run from. `linComb_outer` needs neither hypothesis, so the
`LinComb` instance is unaffected.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A weighted coefficient block is a point of the set, weighted: `w⁻¹` where
there is something to divide by, and the origin where there is not. -/
theorem ConZonotope.aux_smul_mem (cZ : ConZonotope α) (hne : cZ.construct.Nonempty) {w : ℝ}
    (hw : 0 ≤ w) {u : Vec ℝ cZ.h} (hrows : ∀ i, cZ.domain.A i u ≤ w * cZ.domain.b i)
    (heqs : ∀ i, cZ.domain.Ae i u = w * cZ.domain.be i) :
    ∃ y ∈ cZ.construct, w • y = w • cZ.c + ∑ j, u j • cZ.G j := by -- --- PROOF ---
  rcases eq_or_lt_of_le hw with hzero | hpos
  -- weight zero: the box rows of `domain` are the ones that pin the block
  · obtain ⟨y, hy⟩ := hne
    refine ⟨y, hy, ?_⟩
    have hbox : ∀ j, |u j| ≤ w := by
      intro j
      refine HPolytope.abs_le_of_unitBox_rows hw (fun i => ?_) j
      have hA : cZ.domain.A (Fin.castAdd cZ.P.m i) = (HPolytope.unitBox cZ.h).A i := by
        show Fin.append (HPolytope.unitBox cZ.h).A cZ.P.A (Fin.castAdd cZ.P.m i) = _
        rw [Fin.append_left]
      have hb : cZ.domain.b (Fin.castAdd cZ.P.m i) = (HPolytope.unitBox cZ.h).b i := by
        show Fin.append (HPolytope.unitBox cZ.h).b cZ.P.b (Fin.castAdd cZ.P.m i) = _
        rw [Fin.append_left]
      rw [← hA, ← hb]
      exact hrows _
    have hu : ∀ j, u j = 0 := fun j => abs_nonpos_iff.mp (by rw [hzero]; exact hbox j)
    rw [← hzero, zero_smul, zero_smul, zero_add]
    exact (Finset.sum_eq_zero fun j _ => by rw [hu j, zero_smul]).symm
  -- above it, the block divided by its weight is a coefficient of the set itself
  · have hne' : w ≠ 0 := ne_of_gt hpos
    have hdom : w⁻¹ • u ∈ cZ.domain.construct := by
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hpos]
        exact hrows i
      · rw [map_smul, smul_eq_mul, heqs i, ← mul_assoc, inv_mul_cancel₀ hne', one_mul]
    obtain ⟨hbox, hP⟩ := ConZonotope.mem_domain_iff.mp hdom
    refine ⟨cZ.c + ∑ j, (w⁻¹ • u) j • cZ.G j, ⟨w⁻¹ • u, hbox, hP, rfl⟩, ?_⟩
    have hterm : ∀ j, w • (w⁻¹ • u) j • cZ.G j = u j • cZ.G j := fun j => by
      rw [Pi.smul_apply, smul_eq_mul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hne', one_mul]
    rw [smul_add, Finset.smul_sum, Finset.sum_congr rfl fun j _ => hterm j]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.linComb_inner (cZ₁ cZ₂ : ConZonotope α) (h₁ : cZ₁.construct.Nonempty)
    (h₂ : cZ₂.construct.Nonempty) :
    (cZ₁.linComb cZ₂).construct ⊆ segments cZ₁.construct cZ₂.construct := by -- --- PROOF ---
  rintro x ⟨β, hβ, hP, rfl⟩
  set lam : ℝ := (β (Fin.natAdd (cZ₁.h + cZ₂.h) 0) + 1) / 2 with hlam
  have habs := hβ (Fin.natAdd (cZ₁.h + cZ₂.h) 0)
  rw [abs_le] at habs
  have hl0 : 0 ≤ lam := by rw [hlam]; linarith [habs.1]
  have hl1 : lam ≤ 1 := by rw [hlam]; linarith [habs.2]
  -- the two blocks, each against the weight its side of the combination carries
  obtain ⟨hrow₁, hrow₂⟩ := HPolytope.mem_and_iff.mp hP
  obtain ⟨hA₁, hAe₁⟩ := HPolytope.rows_of_mem_halfScaled_comap (w := lam) rfl hrow₁
  obtain ⟨hA₂, hAe₂⟩ := HPolytope.rows_of_mem_halfScaled_comap (w := 1 - lam)
    (show (-(β (Fin.natAdd (cZ₁.h + cZ₂.h) 0)) + 1) / 2 = 1 - lam by rw [hlam]; ring) hrow₂
  obtain ⟨y₁, hy₁mem, hy₁⟩ := ConZonotope.aux_smul_mem cZ₁ h₁ hl0
    (u := fun j => β (Fin.castAdd 1 (Fin.castAdd cZ₂.h j))) hA₁ hAe₁
  obtain ⟨y₂, hy₂mem, hy₂⟩ := ConZonotope.aux_smul_mem cZ₂ h₂ (by linarith)
    (u := fun j => β (Fin.castAdd 1 (Fin.natAdd cZ₁.h j))) hA₂ hAe₂
  refine ⟨y₁, hy₁mem, y₂, hy₂mem, lam, ⟨hl0, hl1⟩, ?_⟩
  -- the value: the two weighted sums, and the centres the fresh generator moves
  rw [ConZonotope.sum_univ_linComb, Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [ConZonotope.linComb, Fin.append_left, Fin.append_right]
  rw [hy₁, hy₂, hlam]
  module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
