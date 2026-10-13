import CORALean.ContSet.PolyZonotope.Real.Operations.PartZonotope
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialSplit
import Mathlib.Algebra.BigOperators.Fin

/-!
# `partZonotope` encloses

At a factor vector `a ∈ [-1,1]ᵖ` the new factor of a pattern is set to the monomial of that pattern
(odd), or to `2 · monomial - 1` (even, where the monomial lies in `[0,1]`): either lies in
`[-1,1]`, and the generator's value is reproduced, `G · P · vm = (G/2) · P · (2 vm - 1) + (G/2) · P`
for an even pattern. This is an enclosure only: the new factors are independent of each other and
of `a`, which `partZonotope_outer` does not claim to be tight.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The value a pattern's new factor takes. -/
noncomputable def PolyZonotope.aux_patValue {p : ℕ} (V : Finset (Fin p)) (a : Fin p → ℝ)
    (π : Fin p → ℕ) : ℝ :=
  if ∀ k ∈ V, π k % 2 = 0 then 2 * ∏ k ∈ V, a k ^ π k - 1 else ∏ k ∈ V, a k ^ π k

/-- A pattern's new factor stays in `[-1, 1]`. -/
theorem PolyZonotope.aux_abs_patValue_le {p : ℕ} (V : Finset (Fin p)) {a : Fin p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (π : Fin p → ℕ) :
    |PolyZonotope.aux_patValue V a π| ≤ 1 := by -- --- PROOF ---
  -- the monomial of the pattern is at most one in absolute value
  have h1 : |∏ k ∈ V, a k ^ π k| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => ?_
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (ha k)
  unfold PolyZonotope.aux_patValue
  split_ifs with hev
  -- an even pattern: the monomial is in `[0, 1]`, so `2 vm - 1` is in `[-1, 1]`
  · have h0 : 0 ≤ ∏ k ∈ V, a k ^ π k :=
      Finset.prod_nonneg fun k hk => by
        have : Even (π k) := Nat.even_iff.mpr (hev k hk)
        exact this.pow_nonneg _
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  · exact h1

/-- The two blocks of generators of `partZonotope`. -/
theorem PolyZonotope.aux_sum_univ_partZonotope_h {pZ : PolyZonotope α} {V : Finset (Fin pZ.p)}
    (f : Fin (pZ.h + pZ.h) → α) :
    ∑ j : Fin (pZ.partZonotope V).h, f j
      = ∑ i, f (Fin.castAdd pZ.h i) + ∑ i, f (Fin.natAdd pZ.h i) :=
  Fin.sum_univ_add f

/-- The old and the new factors of `partZonotope`. -/
theorem PolyZonotope.aux_prod_univ_partZonotope_p {pZ : PolyZonotope α} {V : Finset (Fin pZ.p)}
    (f : Fin (pZ.p + (pZ.partPatterns V).length) → ℝ) :
    ∏ r : Fin (pZ.partZonotope V).p, f r
      = (∏ k, f (Fin.castAdd _ k)) * ∏ g, f (Fin.natAdd pZ.p g) :=
  Fin.prod_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

/-- `partZonotope` encloses the original. -/
theorem PolyZonotope.partZonotope_outer (pZ : PolyZonotope α) (V : Finset (Fin pZ.p)) :
    pZ.construct ⊆ (pZ.partZonotope V).construct := by -- --- PROOF ---
  rintro _ ⟨a, β, ha, hβ, rfl⟩
  have hmem : ∀ i, pZ.partPattern V i ∈ pZ.partPatterns V := fun i =>
    List.mem_dedup.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hlt : ∀ i, (pZ.partPatterns V).idxOf (pZ.partPattern V i) < (pZ.partPatterns V).length :=
    fun i => List.idxOf_lt_length_iff.mpr (hmem i)
  have hget : ∀ i, (pZ.partPatterns V)[(pZ.partPatterns V).idxOf (pZ.partPattern V i)]'(hlt i)
      = pZ.partPattern V i := fun i => List.getElem_idxOf (hlt i)
  let a' : Fin (pZ.p + (pZ.partPatterns V).length) → ℝ := Fin.append a
    (fun g => PolyZonotope.aux_patValue V a ((pZ.partPatterns V).get g))
  refine ⟨a', β, ?_, hβ, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun g => ?_)
    · simpa [a'] using ha k
    · simpa [a'] using PolyZonotope.aux_abs_patValue_le V ha _
  · have hgen : ∀ i, PolyZonotope.monomial pZ.E a i • pZ.G i
        = PolyZonotope.monomial (pZ.partZonotope V).E a' (Fin.castAdd pZ.h i)
            • (pZ.partZonotope V).G (Fin.castAdd pZ.h i)
          + PolyZonotope.monomial (pZ.partZonotope V).E a' (Fin.natAdd pZ.h i)
            • (pZ.partZonotope V).G (Fin.natAdd pZ.h i) := by
      intro i
      have hsplit := PolyZonotope.monomial_split pZ.E V a i
      -- the monomial of the second block: only the factors outside `V`
      have hshift : PolyZonotope.monomial (pZ.partZonotope V).E a' (Fin.natAdd pZ.h i)
          = ∏ k, a k ^ (if k ∈ V then 0 else pZ.E k i) := by
        unfold PolyZonotope.monomial
        rw [PolyZonotope.aux_prod_univ_partZonotope_p (V := V) (fun r => a' r ^ _)]
        simp only [PolyZonotope.partZonotope, a', Fin.append_left, Fin.append_right,
          Fin.addCases_left, Fin.addCases_right, pow_zero, Finset.prod_const_one, mul_one]
      -- the monomial of the first block: also the new factor of the generator's group
      have hmain : PolyZonotope.monomial (pZ.partZonotope V).E a' (Fin.castAdd pZ.h i)
          = (∏ k, a k ^ (if k ∈ V then 0 else pZ.E k i))
            * (if ∀ k ∈ V, pZ.E k i = 0 then 1
                else PolyZonotope.aux_patValue V a (pZ.partPattern V i)) := by
        unfold PolyZonotope.monomial
        rw [PolyZonotope.aux_prod_univ_partZonotope_p (V := V) (fun r => a' r ^ _)]
        simp only [PolyZonotope.partZonotope, a', Fin.append_left, Fin.append_right,
          Fin.addCases_left, Fin.addCases_right]
        congr 1
        -- the new factors: only the group of the generator is read, unless its pattern is zero
        by_cases hz : ∀ k ∈ V, pZ.E k i = 0
        · have hz' : ¬ ∃ x ∈ V, ¬ pZ.E x i = 0 := by
            rintro ⟨x, hx, h⟩
            exact h (hz x hx)
          rw [if_pos hz]
          simp [hz']
        · rw [if_neg hz]
          simp only [hz, not_false_eq_true, true_and]
          rw [Finset.prod_eq_single ⟨(pZ.partPatterns V).idxOf (pZ.partPattern V i), hlt i⟩]
          · simp [hget i]
          · intro g _ hg
            have : (pZ.partPatterns V).idxOf (pZ.partPattern V i) ≠ g.val := fun h =>
              hg (Fin.ext h.symm)
            simp [this]
          · simp
      -- the pattern's value, read back at the exponents of `i`
      have hpat : ∀ k ∈ V, pZ.partPattern V i k = pZ.E k i := fun k hk => by
        simp [PolyZonotope.partPattern, hk]
      have hvm : ∏ k ∈ V, a k ^ pZ.partPattern V i k = ∏ k ∈ V, a k ^ pZ.E k i :=
        Finset.prod_congr rfl fun k hk => by rw [hpat k hk]
      have hev : (∀ k ∈ V, pZ.partPattern V i k % 2 = 0) ↔ ∀ k ∈ V, pZ.E k i % 2 = 0 :=
        forall₂_congr fun k hk => by rw [hpat k hk]
      rw [hsplit, hmain, hshift]
      simp only [PolyZonotope.partZonotope, Fin.append_left, Fin.append_right]
      -- the three kinds of generator: zero pattern, odd pattern, even pattern
      by_cases hz : ∀ k ∈ V, pZ.E k i = 0
      · -- zero pattern: the generator is unchanged
        have hv1 : ∏ k ∈ V, a k ^ pZ.E k i = 1 :=
          Finset.prod_eq_one fun k hk => by rw [hz k hk, pow_zero]
        have hsh : ¬ ((∀ k ∈ V, pZ.E k i % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k i = 0) :=
          fun h => h.2 hz
        rw [if_pos hz, if_neg hsh, if_neg hsh, hv1]
        simp
      · -- even pattern: the halves add up, odd pattern: the new factor is the monomial
        by_cases he : ∀ k ∈ V, pZ.E k i % 2 = 0
        · have hsh : (∀ k ∈ V, pZ.E k i % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k i = 0 := ⟨he, hz⟩
          rw [if_neg hz, if_pos hsh, if_pos hsh]
          unfold PolyZonotope.aux_patValue
          rw [if_pos (hev.mpr he), hvm]
          rw [smul_smul, smul_smul, ← add_smul]
          congr 1
          ring
        · have hsh : ¬ ((∀ k ∈ V, pZ.E k i % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k i = 0) :=
            fun h => he h.1
          rw [if_neg hz, if_neg hsh, if_neg hsh]
          unfold PolyZonotope.aux_patValue
          rw [if_neg (fun h => he (hev.mp h)), hvm]
          simp
    -- the generators sum over the two blocks
    have hsum : ∑ j : Fin (pZ.partZonotope V).h,
        PolyZonotope.monomial (pZ.partZonotope V).E a' j • (pZ.partZonotope V).G j
        = ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i := by
      rw [PolyZonotope.aux_sum_univ_partZonotope_h (V := V) (fun j =>
        PolyZonotope.monomial (pZ.partZonotope V).E a' j • (pZ.partZonotope V).G j),
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (hgen i).symm
    rw [hsum]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
