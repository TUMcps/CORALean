module

public import CORALean.ContSet.Zonotope.Float.Operations.BallCert
public import CORALean.ContSet.Zonotope.Float.Theorems.RightInvQBound
public import CORALean.ContSet.Zonotope.Real.Theorems.RightInvReach

@[expose] public section

/-!
# `Zonotope.ballCert` makes a box of vectors reachable

Read as reals, the checked rows are the hypotheses of `Zonotope.rightInv_reach`: the row sums of
`|1 - G H|` are below `rightInvQ ≤ 1/2`, and `2 B ∑ₖ |Hⱼₖ|` is below
`mulUp (B + B) (radius H j) ≤ δ`.

## Inputs
* `G` – generator matrix
* `H` – candidate right inverse
* `B` – box radius
* `δ` – coefficient bound

## Hypotheses
* `hc` – certificate returns true

## Conclusion
* radius positive and every vector in the box is reached within the bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ballCert_reach {G : Mat 𝕋 n h} {H : Mat 𝕋 h n} {B δ : 𝕋}
    (hc : Zonotope.ballCert G H B δ = true) :
    0 < toReal B ∧ ∀ d : Vec ℝ n, (∀ i, |d i| ≤ toReal B) →
      ∃ β : Vec ℝ h, toRealMat G *ᵥ β = d ∧ ∀ j, |β j| ≤ toReal δ := by -- --- PROOF ---
  simp only [Zonotope.ballCert, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at hc
  obtain ⟨⟨hB, hq⟩, hδ⟩ := hc
  have hBpos : 0 < toReal B := by
    have := toReal_lt_of_ltStrict hB
    rwa [toReal_zero] at this
  refine ⟨hBpos, fun d hd => ?_⟩
  have hq' : toReal (Zonotope.rightInvQ G H) ≤ 1 / 2 := by
    have := toReal_le_of_le hq
    rwa [toReal_half, toReal_one] at this
  -- the real hypotheses: the row sums of `1 - G H`, then the bound on each row of `H`
  refine CORALean.Real.Zonotope.rightInv_reach (toRealMat G) (toRealMat H) hq'
    (fun i => Zonotope.rightInvQ_bound G H i) (fun j => ?_) d hd
  have h1 := toReal_le_of_le (hδ j)
  have h3 := add_le_addUp B B
  have h4 := sum_abs_le_radius (d := H) j
  have h5 : (toReal B + toReal B) * ∑ k, |toReal (H j k)|
      ≤ toReal (mulUp (addUp B B) (radius H j)) :=
    le_trans (mul_le_mul h3 h4 (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by linarith))
      (mul_le_mulUp _ _)
  show 2 * toReal B * ∑ k, |toReal (H j k)| ≤ toReal δ
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
