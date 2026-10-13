import CORALean.ContSet.Zonotope.Real.Operations.EnclosePointsStursberg
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel

/-!
# `Zonotope.enclosePointsStursberg` contains every point

Writing `w = Uᵀ (p - mean)` for the rotated point, `U w = p - mean` as `U Uᵀ = 1`, and each
coordinate `wᵢ` lies in `[m2ᵢ, m1ᵢ]`, so `wᵢ` is the box centre plus a coefficient `βᵢ` in
`[-1, 1]` times the half-width, the generator's factor. Outer only: the box is an enclosure, and
the result does not depend on `U` being the SVD's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.enclosePointsStursberg_mem [NeZero N] (pts : Fin N → Vec ℝ n) {U : Mat ℝ n n}
    (hU : U * Uᵀ = 1) (j : Fin N) :
    pts j ∈ (Zonotope.enclosePointsStursberg pts U).construct := by -- --- PROOF ---
  set mean : Vec ℝ n := (1 / (N : ℝ)) • ∑ j, pts j with hmean
  set w : Fin N → Vec ℝ n := fun j => Uᵀ *ᵥ (pts j - mean) with hw
  set m1 : Fin n → ℝ := fun i => Finset.univ.sup' Finset.univ_nonempty fun j => w j i with hm1
  set m2 : Fin n → ℝ := fun i => Finset.univ.inf' Finset.univ_nonempty fun j => w j i with hm2
  -- each rotated coordinate lies in its box
  have hle1 : ∀ i, w j i ≤ m1 i := fun i =>
    Finset.le_sup' (fun j => w j i) (Finset.mem_univ j)
  have hle2 : ∀ i, m2 i ≤ w j i := fun i =>
    Finset.inf'_le (fun j => w j i) (Finset.mem_univ j)
  -- the coefficient: the offset from the box centre, over the half-width
  refine ⟨fun i => (w j i - (m1 i + m2 i) / 2) / ((m1 i - m2 i) * (1 / 2)), ?_, ?_⟩
  · intro (i : Fin n)
    show |(w j i - (m1 i + m2 i) / 2) / ((m1 i - m2 i) * (1 / 2))| ≤ 1
    have h0 : 0 ≤ (m1 i - m2 i) * (1 / 2) := by linarith [hle1 i, hle2 i]
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp
    · rw [abs_div, abs_of_pos h, div_le_one h, abs_le]
      constructor <;> nlinarith [hle1 i, hle2 i]
  · -- `U w = p - mean`, and the generators sum to `U` of the half-widths times `β`
    have hUw : U *ᵥ w j = pts j - mean := by
      rw [hw]; simp only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    have hsum : (∑ i, ((w j i - (m1 i + m2 i) / 2) / ((m1 i - m2 i) * (1 / 2))) •
        (((m1 i - m2 i) * (1 / 2 : ℝ)) • fun r => U r i))
        = U *ᵥ (w j - (1 / 2 : ℝ) • (m1 + m2)) := by
      funext r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
        Pi.sub_apply, Pi.add_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases (show 0 ≤ (m1 i - m2 i) * (1 / 2) by linarith [hle1 i, hle2 i]).eq_or_lt with h | h
      · have : w j i = (m1 i + m2 i) / 2 := by nlinarith [hle1 i, hle2 i]
        rw [← h, this]; ring
      · have hne : m1 i - m2 i ≠ 0 := by intro h'; rw [h'] at h; simp at h
        field_simp
    show pts j = (mean + U *ᵥ ((1 / 2 : ℝ) • (m1 + m2))) +
      ∑ i : Fin n, ((w j i - (m1 i + m2 i) / 2) / ((m1 i - m2 i) * (1 / 2))) •
        (((m1 i - m2 i) * (1 / 2 : ℝ)) • fun r => U r i)
    rw [hsum, Matrix.mulVec_sub, hUw]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
