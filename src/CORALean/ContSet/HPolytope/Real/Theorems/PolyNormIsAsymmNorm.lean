module

public import CORALean.ContSet.HPolytope.Real.Theorems.PolyNormLeIff
public import CORALean.ContSet.HPolytope.Real.Theorems.EqZeroOfMulVecNonpos
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The polyhedral norm is an asymmetric norm

`[1, Lemma 1]`: `S_P` satisfies the triangle inequality and is positively homogeneous;
for a symmetric `S_P` it is a norm; and its unit ball is `P`. The first two hold at any
right-hand sides — a ratio of a sum is a sum of ratios. The last two need every `hᵢ > 0`
(the origin inside `P`), where the printed `hᵢ ≠ 0` allows `P = [1, 2]`, whose unit ball
`{S ≤ 1}` contains `0` (`polyNorm_isAsymmNorm_counterexample`). With `hᵢ > 0` the unit
ball is the rows read off, and definiteness is `P`'s boundedness: `S(x) = S(-x) = 0` puts
`x` in the recession cone `{H x ≤ 0}`.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {s n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.polyNorm_isAsymmNorm {H : Mat ℝ s n} {h : Vec ℝ s} :
    (∀ x y, HPolytope.polyNorm H h (x + y) ≤ HPolytope.polyNorm H h x + HPolytope.polyNorm H h y) ∧
      (∀ (a : ℝ) x, 0 < a → HPolytope.polyNorm H h (a • x) = a * HPolytope.polyNorm H h x) ∧
      ((∀ i, 0 < h i) →
        (∀ x, HPolytope.polyNorm H h x ≤ 1 ↔ x ∈ (HPolytope.ineqs H h).construct) ∧
        (Bornology.IsBounded (HPolytope.ineqs H h).construct →
          (∀ x, HPolytope.polyNorm H h x = HPolytope.polyNorm H h (-x)) →
          ∀ x, HPolytope.polyNorm H h x = 0 ↔ x = 0)) := by -- --- PROOF ---
  -- every ratio is below the fold, and the fold is nonnegative
  have hge : ∀ x i, (H *ᵥ x) i / h i ≤ HPolytope.polyNorm H h x := fun x i =>
    (HPolytope.polyNorm_le_iff.mp le_rfl).2 i
  have h0 : ∀ x, 0 ≤ HPolytope.polyNorm H h x := fun x => (HPolytope.polyNorm_le_iff.mp le_rfl).1
  refine ⟨fun x y => ?_, fun a x ha => ?_, fun hpos => ⟨fun x => ?_, fun hb hsym x => ?_⟩⟩
  · refine HPolytope.polyNorm_le_iff.mpr ⟨add_nonneg (h0 x) (h0 y), fun i => ?_⟩
    rw [mulVec_add, Pi.add_apply, add_div]
    exact add_le_add (hge x i) (hge y i)
  -- `a S(x)` is the fold for `a x`, both ways
  · refine le_antisymm (HPolytope.polyNorm_le_iff.mpr ⟨mul_nonneg ha.le (h0 x), fun i => ?_⟩) ?_
    · rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hge x i) ha.le
    · rw [← le_div_iff₀' ha]
      refine HPolytope.polyNorm_le_iff.mpr ⟨div_nonneg (h0 _) ha.le, fun i => ?_⟩
      rw [le_div_iff₀' ha, ← mul_div_assoc, ← smul_eq_mul, ← Pi.smul_apply, ← mulVec_smul]
      exact hge _ i
  · rw [HPolytope.polyNorm_le_iff, HPolytope.mem_ineqs_iff]
    simp only [zero_le_one, true_and]
    exact forall_congr' fun i => div_le_one (hpos i)
  -- `S(x) = S(-x) = 0` leaves `H x = 0`, and a bounded `P` has no such direction
  · constructor
    · intro hx
      have hP : (HPolytope.ineqs H h).construct.Nonempty :=
        ⟨0, HPolytope.mem_ineqs_iff.mpr fun i => by simpa using (hpos i).le⟩
      refine HPolytope.eq_zero_of_mulVec_nonpos hP hb fun i => ?_
      have := hge x i
      rw [hx, div_le_iff₀ (hpos i), zero_mul] at this
      exact this
    · rintro rfl
      refine le_antisymm (HPolytope.polyNorm_le_iff.mpr ⟨le_rfl, fun i => ?_⟩) (h0 0)
      simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
