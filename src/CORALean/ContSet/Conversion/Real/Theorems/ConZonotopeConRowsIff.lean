module

public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono

@[expose] public section

/-!
# A constrained zonotope's rows, each held to its interval: `conRows_iff`

Over the unit cube a row `a β ≤ b` never falls below `-Σ|aⱼ|`, so the lower end `conLo` cuts
nothing, and the interval rows say exactly what the polytope says.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem ConZonotope.aux_apply_eq_sum {h : ℕ} (f : Vec ℝ h →ₗ[ℝ] ℝ) (β : Vec ℝ h) :
    f β = ∑ j, ConZonotope.coeffs f j * β j := by -- --- PROOF ---
  have hsingle : ∀ j k : Fin h, (Pi.single j (1:ℝ) : Vec ℝ h) k = if k = j then 1 else 0 :=
    fun j k => Pi.single_apply j (1:ℝ) k
  have hβ : β = ∑ j, β j • (Pi.single j (1:ℝ) : Vec ℝ h) := by
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · rw [Pi.smul_apply, smul_eq_mul, hsingle, if_pos rfl, mul_one]
    · intro j _ hj
      rw [Pi.smul_apply, smul_eq_mul, hsingle, if_neg (Ne.symm hj), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  conv_lhs => rw [hβ]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_smul, smul_eq_mul, ConZonotope.coeffs, mul_comm]

/-- What a row can reach over the unit cube, which is what the supplied lower
bound has to clear. -/
theorem ConZonotope.aux_abs_sum_le {h : ℕ} (c β : Vec ℝ h) (hβ : ∀ j, |β j| ≤ 1) :
    |∑ j, c j * β j| ≤ ∑ j, |c j| :=
  calc |∑ j, c j * β j| ≤ ∑ j, |c j * β j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |c j| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hβ j)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The rows held to `[conLo, conHi]` say of the coefficients exactly what the coefficient
polytope says. -/
theorem ConZonotope.conRows_iff (cZ : ConZonotope (Vec ℝ n)) (β : Vec ℝ cZ.h)
    (hβ : ∀ j, |β j| ≤ 1) : -- --- STMT ---
    (∀ i, ConZonotope.conLo cZ i ≤ (ConZonotope.conA cZ *ᵥ β) i
        ∧ (ConZonotope.conA cZ *ᵥ β) i ≤ ConZonotope.conHi cZ i)
      ↔ β ∈ cZ.P.construct := by -- --- PROOF ---
  have hlin : ∀ i : Fin cZ.P.m, (ConZonotope.conA cZ *ᵥ β) (Fin.castAdd cZ.P.me i)
      = cZ.P.A i β := by
    intro i
    show ∑ j, ConZonotope.conA cZ (Fin.castAdd cZ.P.me i) j * β j = _
    rw [ConZonotope.aux_apply_eq_sum (cZ.P.A i) β]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ConZonotope.conA, Fin.append_left]
  have heq : ∀ i : Fin cZ.P.me, (ConZonotope.conA cZ *ᵥ β) (Fin.natAdd cZ.P.m i)
      = cZ.P.Ae i β := by
    intro i
    show ∑ j, ConZonotope.conA cZ (Fin.natAdd cZ.P.m i) j * β j = _
    rw [ConZonotope.aux_apply_eq_sum (cZ.P.Ae i) β]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ConZonotope.conA, Fin.append_right]
  -- the free lower bound: no row falls below minus its own absolute row sum
  have hfree : ∀ i : Fin cZ.P.m,
      -∑ j, |ConZonotope.coeffs (cZ.P.A i) j| ≤ cZ.P.A i β := by
    intro i
    rw [ConZonotope.aux_apply_eq_sum (cZ.P.A i) β]
    have h := ConZonotope.aux_abs_sum_le (ConZonotope.coeffs (cZ.P.A i)) β hβ
    rw [abs_le] at h
    exact h.1
  constructor
  · intro hsat
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h := (hsat (Fin.castAdd cZ.P.me i)).2
      rw [hlin i] at h
      simpa only [ConZonotope.conHi, Fin.append_left] using h
    · have h := hsat (Fin.natAdd cZ.P.m i)
      rw [heq i] at h
      simp only [ConZonotope.conLo, ConZonotope.conHi, Fin.append_right] at h
      exact le_antisymm h.2 h.1
  -- back: an inequality needs only its upper bound, an equality both ends at once
  · rintro ⟨hle, hE⟩
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hlin i]
      simp only [ConZonotope.conLo, ConZonotope.conHi, Fin.append_left]
      exact ⟨min_le_of_left_le (hfree i), hle i⟩
    · rw [heq i]
      simp only [ConZonotope.conLo, ConZonotope.conHi, Fin.append_right]
      exact ⟨(hE i).ge, (hE i).le⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
