import CORALean.ContSet.ZonoBundle.Float.Operations.Parallelotope
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.RightInvQBound
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

/-!
# `ZonoBundle.parallelotope` holds every point it is built for

A point `x` with `H x` in the box and `|x| ≤ m` splits as `Λ (H x) + (1 - Λ H) x`: the first
part is in `Λ * zonotope(B)` by `Zonotope.mtimes_outer`, and the second, at most `q m` per
coordinate by `Zonotope.rightInvQ_bound`, joins the error box by `Interval.plus_outer`. Nothing
about `H` is assumed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.parallelotope_contains (Λ H : Mat 𝕋 n n) (B : Interval (Vec 𝕋 n)) (m : 𝕋)
    {x : Vec ℝ n} (hB : toRealMat H *ᵥ x ∈ B.construct) (hm : ∀ j, |x j| ≤ toReal m) :
    x ∈ (ZonoBundle.parallelotope Λ H B m).construct := by -- --- PROOF ---
  -- the part along `Λ`, in the mapped box
  obtain ⟨z, hz, e, he, hze⟩ := Zonotope.mtimes_outer Λ B.zonotope
    ⟨_, Interval.zonotope_contains B hB, rfl⟩
  set r : Vec ℝ n := ((1 : Mat ℝ n n) - toRealMat Λ * toRealMat H) *ᵥ x with hr
  have hze' : z + e = toRealMat Λ *ᵥ (toRealMat H *ᵥ x) := hze
  have hx : x = z + (e + r) := by
    rw [← add_assoc, hze', hr, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    abel
  -- the residual, at most `q m` in every coordinate
  have hres : r ∈ (⟨fun _ => neg (mulUp (Zonotope.rightInvQ Λ H) m),
      fun _ => mulUp (Zonotope.rightInvQ Λ H) m⟩ : Interval (Vec 𝕋 n)).construct := by
    intro i
    have hm0 : 0 ≤ toReal m := le_trans (abs_nonneg _) (hm i)
    have hrow := Zonotope.rightInvQ_bound Λ H i
    -- a row of `1 - Λ H` against `x`, each entry at most `m`
    have hri : r i = ∑ j, ((1 : Mat ℝ n n) - toRealMat Λ * toRealMat H) i j * x j := rfl
    have hbound : |r i| ≤ toReal (mulUp (Zonotope.rightInvQ Λ H) m) := by
      rw [hri]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (mul_le_mulUp _ _))
      calc ∑ j, |((1 : Mat ℝ n n) - toRealMat Λ * toRealMat H) i j * x j|
          ≤ ∑ j, |((1 : Mat ℝ n n) - toRealMat Λ * toRealMat H) i j| * toReal m :=
            Finset.sum_le_sum fun j _ => by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hm j) (abs_nonneg _)
        _ = (∑ j, |((1 : Mat ℝ n n) - toRealMat Λ * toRealMat H) i j|) * toReal m :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ toReal (Zonotope.rightInvQ Λ H) * toReal m := mul_le_mul_of_nonneg_right hrow hm0
    -- the two faces of the residual box
    have := abs_le.mp hbound
    show toReal (neg (mulUp (Zonotope.rightInvQ Λ H) m)) ≤ r i
      ∧ r i ≤ toReal (mulUp (Zonotope.rightInvQ Λ H) m)
    rw [toReal_neg]
    exact this
  rw [hx]
  exact ⟨z, hz, e + r, Interval.plus_outer _ _ ⟨e, he, r, hres, rfl⟩, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
