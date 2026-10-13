import CORALean.ContSet.ConZonotope.Real.Operations.Compact

/-!
# `compact` loses nothing, exactly

`compact_ 'zeros'` denotes the same set. A coefficient vector of the original is read at the
kept generators, which loses nothing since the dropped ones add no point and no constraint reads
them; a coefficient vector of the result is padded with zeros, which meets every constraint the
original has, the dropped equality rows being `0 = 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over all of `Fin h` that vanishes off `S` is the sum over the kept indices. -/
theorem ConZonotope.aux_sum_kept {M : Type} [AddCommMonoid M] {h : ℕ} (S : Finset (Fin h))
    (f : Fin h → M) (hf : ∀ j, j ∉ S → f j = 0) :
    ∑ j, f j = ∑ l : Fin S.card, f (S.orderIsoOfFin rfl l).1 := by
  rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => hf j hj,
    ← Finset.sum_coe_sort S f]
  exact (Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv fun x => f x).symm

/-- The embedding puts a kept coefficient where its generator is. -/
theorem ConZonotope.aux_embed_apply {h : ℕ} (S : Finset (Fin h)) (v : Vec ℝ S.card)
    (l : Fin S.card) :
    ConZonotope.compactEmbed S v (S.orderIsoOfFin rfl l).1 = v l := by -- --- PROOF ---
  show (∑ l', v l' • (Pi.single (S.orderIsoOfFin rfl l').1 (1 : ℝ) : Vec ℝ h))
    (S.orderIsoOfFin rfl l).1 = _
  rw [Finset.sum_apply, Finset.sum_eq_single l]
  · show v l • (Pi.single (S.orderIsoOfFin rfl l).1 (1 : ℝ) : Fin h → ℝ) (S.orderIsoOfFin rfl l).1
      = v l
    rw [Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro l' _ hne
    have : (S.orderIsoOfFin rfl l).1 ≠ (S.orderIsoOfFin rfl l').1 := fun he =>
      hne ((S.orderIsoOfFin rfl).injective (Subtype.ext he)).symm
    show v l' • (Pi.single (S.orderIsoOfFin rfl l').1 (1 : ℝ) : Fin h → ℝ)
      (S.orderIsoOfFin rfl l).1 = 0
    rw [Pi.single_eq_of_ne this, smul_zero]
  · exact fun h => absurd (Finset.mem_univ l) h

/-- A dropped coordinate is zero. -/
theorem ConZonotope.aux_embed_off {h : ℕ} (S : Finset (Fin h)) (v : Vec ℝ S.card) (j : Fin h)
    (hj : j ∉ S) : ConZonotope.compactEmbed S v j = 0 := by -- --- PROOF ---
  show (∑ l', v l' • (Pi.single (S.orderIsoOfFin rfl l').1 (1 : ℝ) : Vec ℝ h)) j = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun l' _ => ?_
  have : j ≠ (S.orderIsoOfFin rfl l').1 := fun he => hj (he ▸ (S.orderIsoOfFin rfl l').2)
  show v l' • (Pi.single (S.orderIsoOfFin rfl l').1 (1 : ℝ) : Fin h → ℝ) j = 0
  rw [Pi.single_eq_of_ne this, smul_zero]

/-- A functional that ignores the dropped coordinates reads the embedded kept ones alike. -/
theorem ConZonotope.aux_functional_embed {h : ℕ} (S : Finset (Fin h)) (φ : Vec ℝ h →ₗ[ℝ] ℝ)
    (hφ : ∀ j, j ∉ S → φ (Pi.single j (1 : ℝ) : Vec ℝ h) = 0) (β : Vec ℝ h) :
    φ (ConZonotope.compactEmbed S fun l => β (S.orderIsoOfFin rfl l).1) = φ β := by -- --- PROOF ---
  have hβ : β = ∑ j, β j • (Pi.single j (1 : ℝ) : Vec ℝ h) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hβ]
  rw [map_sum, ConZonotope.aux_sum_kept S _ fun j hj => by simp [hφ j hj]]
  show φ (∑ l, β (S.orderIsoOfFin rfl l).1 • (Pi.single (S.orderIsoOfFin rfl l).1 (1 : ℝ) :
    Vec ℝ h)) = _
  simp [map_sum]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.compact_exact (cZ : ConZonotope α) :
    cZ.compact.construct = cZ.construct := by -- --- PROOF ---
  -- what a dropped generator is: zero, and read by no constraint
  have hdrop : ∀ j, j ∉ cZ.compactGens → cZ.G j = 0
      ∧ (∀ i, cZ.P.A i (Pi.single j (1 : ℝ) : Vec ℝ cZ.h) = 0)
      ∧ ∀ i, cZ.P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ cZ.h) = 0 := by
    intro j hj
    simp only [ConZonotope.compactGens, Finset.mem_filter, Finset.mem_univ, true_and,
      not_or, not_exists, not_not] at hj
    exact hj
  -- an equality row that is not kept is `0 = 0`
  have hrow : ∀ i, i ∉ ConZonotope.compactEqs cZ.P → cZ.P.Ae i = 0 ∧ cZ.P.be i = 0 := by
    intro i hi
    simpa [ConZonotope.compactEqs] using hi
  ext x
  constructor
  · rintro ⟨β', hβ', hP', hx'⟩
    -- pad the coefficients with zeros at the dropped generators
    have hoff : ∀ j, j ∉ cZ.compactGens → ConZonotope.compactEmbed cZ.compactGens β' j = 0 :=
      fun j hj => ConZonotope.aux_embed_off cZ.compactGens β' j hj
    refine ⟨ConZonotope.compactEmbed cZ.compactGens β', fun j => ?_,
      ⟨fun i => hP'.1 i, fun i => ?_⟩, ?_⟩
    · by_cases hj : j ∈ cZ.compactGens
      · obtain ⟨l, hl⟩ := (cZ.compactGens.orderIsoOfFin rfl).surjective ⟨j, hj⟩
        rw [show j = (cZ.compactGens.orderIsoOfFin rfl l).1 from by rw [hl],
          ConZonotope.aux_embed_apply]
        exact hβ' l
      · rw [hoff j hj, abs_zero]; exact zero_le_one
    · by_cases hi : i ∈ ConZonotope.compactEqs cZ.P
      · -- a kept row is `compact`'s own
        have := hP'.2 (((ConZonotope.compactEqs cZ.P).orderIsoOfFin rfl).symm ⟨i, hi⟩)
        change cZ.P.Ae ((ConZonotope.compactEqs cZ.P).orderIsoOfFin rfl
          (((ConZonotope.compactEqs cZ.P).orderIsoOfFin rfl).symm ⟨i, hi⟩)).1
          (ConZonotope.compactEmbed cZ.compactGens β') =
          cZ.P.be ((ConZonotope.compactEqs cZ.P).orderIsoOfFin rfl
          (((ConZonotope.compactEqs cZ.P).orderIsoOfFin rfl).symm ⟨i, hi⟩)).1 at this
        rw [OrderIso.apply_symm_apply] at this
        exact this
      · obtain ⟨h1, h2⟩ := hrow i hi
        rw [h1, h2]; simp
    · rw [hx']
      refine congrArg (cZ.c + ·) ?_
      rw [ConZonotope.aux_sum_kept cZ.compactGens _ fun j hj => by
        rw [hoff j hj, zero_smul]]
      exact Finset.sum_congr rfl fun l _ => by rw [ConZonotope.aux_embed_apply]; rfl
  · rintro ⟨β, hβ, hP, hx⟩
    refine ⟨fun l => β (cZ.compactGens.orderIsoOfFin rfl l).1, fun l => hβ _, ⟨fun i => ?_,
      fun r => ?_⟩, ?_⟩
    · -- the kept coefficients read the same constraint as the whole vector
      have := ConZonotope.aux_functional_embed cZ.compactGens (cZ.P.A i)
        (fun j hj => (hdrop j hj).2.1 i) β
      exact this ▸ hP.1 i
    · have := ConZonotope.aux_functional_embed cZ.compactGens
        (cZ.P.Ae ((ConZonotope.compactEqs cZ.P).orderIsoOfFin rfl r).1)
        (fun j hj => (hdrop j hj).2.2 _) β
      exact this ▸ hP.2 _
    · rw [hx]
      refine congrArg (cZ.c + ·) ?_
      exact ConZonotope.aux_sum_kept cZ.compactGens (fun j => β j • cZ.G j) fun j hj => by
        rw [(hdrop j hj).1, smul_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
