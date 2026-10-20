module

public import CORALean.ContSet.Zonotope.Float.Operations.UnitIntervalMul
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `[-1, 1] ⊗ Z` holds every `s z`, `|s| ≤ 1`, `z ∈ Z`

The nominal part `c + ∑ βⱼ gⱼ` scales to the factors `s, sβ₁, …` of the generators `c, g₁, …`,
all in `[-1, 1]`, about the center `0`; a point `e` of the box scales to `se`, `|seᵢ| ≤ |eᵢ|`,
inside the symmetric hull.

## Inputs
* `Z` – zonotope
* `s` – scalar
* `z` – point

## Hypotheses
* `hs` – scalar in the unit interval
* `hz` – point lies in the zonotope

## Conclusion
* scaled point lies in the computed zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.unitIntervalMul_outer (Z : Zonotope (Vec 𝕋 n)) {s : ℝ} (hs : |s| ≤ 1) {z : Vec ℝ n}
    (hz : z ∈ Z.construct) : s • z ∈ Z.unitIntervalMul.construct := by -- --- PROOF ---
  obtain ⟨a, ha, e, he, rfl⟩ := hz
  obtain ⟨β, hβ, ha⟩ := Zonotope.mem_nominalSet_iff.mp ha
  refine ⟨s • a, Zonotope.mem_nominalSet_iff.mpr ⟨Fin.cons s (fun j => s * β j), fun j => ?_,
    fun i => ?_⟩, s • e, fun i => ?_, (smul_add s a e).symm⟩
  · -- the factors: `s` for the center, `sβⱼ` for each generator
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hs
    · simp only [Fin.cons_succ, abs_mul]
      exact mul_le_one₀ hs (abs_nonneg _) (hβ j)
  · -- `s(c + ∑ βⱼ gⱼ) = 0 + s c + ∑ (sβⱼ) gⱼ`
    show s * a i = toReal (zero : 𝕋) + ∑ j : Fin (Z.h + 1),
      toReal ((Fin.cons Z.c Z.G : Fin (Z.h + 1) → Vec 𝕋 n) j i) *
        (Fin.cons s (fun j => s * β j) : Fin (Z.h + 1) → ℝ) j
    rw [Fin.sum_univ_succ, ha i, toReal_zero]
    simp only [Fin.cons_zero, Fin.cons_succ, zero_add, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  · -- `|s eᵢ| ≤ |eᵢ| ≤ max(|E̲ᵢ|, |Ēᵢ|)`
    have hei : toReal (Z.I_error.inf i) ≤ e i ∧ e i ≤ toReal (Z.I_error.sup i) := he i
    have hm : |e i| ≤ max |toReal (Z.I_error.inf i)| |toReal (Z.I_error.sup i)| := by
      rcases le_total 0 (e i) with h0 | h0
      · exact le_max_of_le_right (by rw [abs_of_nonneg h0]; exact hei.2.trans (le_abs_self _))
      · exact le_max_of_le_left (by
          rw [abs_of_nonpos h0]; exact (neg_le_neg hei.1).trans (neg_le_abs _))
    have hse : |s * e i| ≤ |e i| := by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hs
    show toReal (neg (maximum (absolute (Z.I_error.inf i)) (absolute (Z.I_error.sup i)))) ≤ s * e i
        ∧
      s * e i ≤ toReal (maximum (absolute (Z.I_error.inf i)) (absolute (Z.I_error.sup i)))
    rw [toReal_neg, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le.mp (hse.trans hm)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
