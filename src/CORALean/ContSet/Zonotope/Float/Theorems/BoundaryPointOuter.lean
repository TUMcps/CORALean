module

public import CORALean.ContSet.Zonotope.Float.Operations.BoundaryPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.BoundaryRatioGe
public import CORALean.ContSet.Zonotope.Real.Operations.BoundaryPoint

@[expose] public section

/-!
# `Zonotope.boundaryPoint` encloses the exact boundary point

Outer: the exact layer's boundary point of the zonotope the stored floats describe,
`startPoint + t* dir` with `t*` the largest step staying in it, lies in the float box whenever that
is returned. The step `t*` is at least `0` (a supremum of non-negative steps, or of none) and at
most the computed bound (`boundaryRatio_ge`), so the point is on the segment from `startPoint` to
`startPoint + t_max dir`, which the box encloses coordinate by coordinate. It is a box around that
segment, not the boundary point: the exit step is bounded above only, and the box does not shrink
to the exit as the rounding does.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.boundaryPoint_outer (Z : Zonotope (Vec 𝕋 (n + 1))) (dir start : Vec 𝕋 (n + 1)) :
    ∀ J ∈ Z.boundaryPoint dir start,
      CORALean.Real.Zonotope.boundaryPoint (nominal Z) (toRealVec dir) (toRealVec start)
        ∈ J.construct := by -- --- PROOF ---
  intro J (hJ : Z.boundaryPoint dir start = some J)
  unfold Zonotope.boundaryPoint at hJ
  obtain ⟨U, hU, rfl⟩ := Option.map_eq_some_iff.mp hJ
  set T := maximum zero U with hT
  have hT0 : 0 ≤ toReal T := by rw [hT, toReal_maximum, toReal_zero]; exact le_max_left _ _
  -- the exact step: non-negative, and at most the computed bound
  set S : Set ℝ := {t | 0 ≤ t ∧ toRealVec start + t • toRealVec dir ∈ (nominal Z).construct}
    with hS
  have hlo : 0 ≤ sSup S := Real.sSup_nonneg fun t ht => ht.1
  have hup : sSup S ≤ toReal T := by
    refine Real.sSup_le (fun t ht => ?_) hT0
    rw [hT, toReal_maximum, toReal_zero]
    exact le_max_of_le_right (Zonotope.boundaryRatio_ge Z dir start t ht.1 ht.2 U hU)
  intro i
  show toReal (addDown (start i) (minimum zero (mulDown T (dir i)))) ≤
      toReal (start i) + sSup S * toReal (dir i) ∧
    toReal (start i) + sSup S * toReal (dir i) ≤
      toReal (addUp (start i) (maximum zero (mulUp T (dir i))))
  have hm1 := mulDown_le_mul T (dir i)
  have hm2 := mul_le_mulUp T (dir i)
  have hd := addDown_le_add (start i) (minimum zero (mulDown T (dir i)))
  have hu := add_le_addUp (start i) (maximum zero (mulUp T (dir i)))
  rw [toReal_minimum, toReal_zero] at hd
  rw [toReal_maximum, toReal_zero] at hu
  -- the step times the coordinate lies between zero and `T` times the coordinate
  have hbet : min 0 (toReal T * toReal (dir i)) ≤ sSup S * toReal (dir i) ∧
      sSup S * toReal (dir i) ≤ max 0 (toReal T * toReal (dir i)) := by
    rcases le_total 0 (toReal (dir i)) with hd0 | hd0
    · exact ⟨le_trans (min_le_left _ _) (mul_nonneg hlo hd0),
        le_trans (mul_le_mul_of_nonneg_right hup hd0) (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hup hd0),
        le_trans (mul_nonpos_of_nonneg_of_nonpos hlo hd0) (le_max_left _ _)⟩
  constructor
  · refine le_trans hd ?_
    have : min 0 (toReal (mulDown T (dir i))) ≤ min 0 (toReal T * toReal (dir i)) :=
      min_le_min le_rfl hm1
    linarith [hbet.1]
  · refine le_trans ?_ hu
    have : max 0 (toReal T * toReal (dir i)) ≤ max 0 (toReal (mulUp T (dir i))) :=
      max_le_max le_rfl hm2
    linarith [hbet.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
