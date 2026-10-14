module

public import CORALean.ContSet.Capsule.Real.Operations.ConvHull
public import CORALean.ContSet.Capsule.Real.Theorems.NormSubCentreLe
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# `Capsule.convHull` encloses the hull

A point `λ x + (1 - λ) y` of the segments between the two capsules sits, in its centre part, at
`c_ + (2λ - 1) g_`, and the rest, `λ (x - c) + (1 - λ) (y - S.c)`, is under
`λ (‖g‖₂ + r) + (1 - λ) (‖S.g‖₂ + S.r)`, so under the larger. Outer only: the hull is not a
capsule, and the enclosure is strict in general.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point on a segment between the two capsules lies in `Capsule.convHull`. -/
theorem Capsule.convHull_outer (C S : Capsule n) :
    Set.linComb C.construct S.construct ⊆ (C.convHull S).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, y, hy, l, ⟨hl0, hl1⟩, rfl⟩
  have h1 := Capsule.norm₂_sub_centre_le hx
  have h2 := Capsule.norm₂_sub_centre_le hy
  -- the segment parameter: the centre part is `c_ + (2 l - 1) g_`
  refine ⟨2 * l - 1, Set.mem_Icc.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have key : l • x + (1 - l) • y - ((C.convHull S).c + (2 * l - 1) • (C.convHull S).g) =
      l • (x - C.c) + (1 - l) • (y - S.c) := by
    ext i
    simp only [Capsule.convHull, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  show ‖l • x + (1 - l) • y - ((C.convHull S).c + (2 * l - 1) • (C.convHull S).g)‖₂ ≤ _
  rw [key]
  refine (norm₂_add_le _ _).trans ?_
  rw [norm₂_smul, norm₂_smul, abs_of_nonneg hl0, abs_of_nonneg (by linarith)]
  have a1 := mul_le_mul_of_nonneg_left (h1.trans (le_max_left C.radius S.radius)) hl0
  have a2 := mul_le_mul_of_nonneg_left (h2.trans (le_max_right C.radius S.radius))
    (by linarith : 0 ≤ 1 - l)
  show _ ≤ max C.radius S.radius
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
