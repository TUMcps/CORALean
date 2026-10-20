module

public import CORALean.ContSet.HPolytope.Float.Operations.RescaleCols
public import CORALean.ContSet.HPolytope.Float.Theorems.MemSetRhsNominal
public import CORALean.Global.Float.MulDownGap

@[expose] public section

/-!
# What `HPolytope.rescaleCols` keeps

A coefficient vector `δ` in the unit box whose image `ξ = ξm + diag(ξr) δ` lies in the nominal
part lies in the rescaled one. A row read at `ξ` splits into the row at `ξm`, the stored scaled
row at `δ` and the scaling's rounding against `δ` (`sum_mul_affine_split`), the last at most the
row's gap either way (`abs_sum_mulDown_gap_le`). So the scaled row reads `δ` within its slack of
`b - A ξm` less that rounding, a value between the two ends the operation hands `setRhs`
(`HPolytope.mem_setRhs_nominal`), and the same for every equality.

## Inputs
* `P` – H-polytope
* `ξm` – vector of length `n`
* `ξr` – vector of length `n`
* `δ` – vector of length `n`
* `ξ` – vector of length `n`

## Hypotheses
* `hδ` – `∀ j, |δ j| ≤ 1`
* `hξ` – `ξ` is `ξm + diag(ξr) δ` coordinatewise
* `hP` – `ξ` lies in `P.nominal`

## Conclusion
* A unit-box `δ` whose image `ξm + diag(ξr) δ` is in the nominal part is in the rescaled one
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A unit-box `δ` whose image `ξm + diag(ξr) δ` is in the nominal part is in the rescaled one. -/
theorem HPolytope.mem_rescaleCols_nominal (P : HPolytope 𝕋 (Vec 𝕋 n)) (ξm ξr : Vec 𝕋 n)
    {δ ξ : Vec ℝ n} (hδ : ∀ j, |δ j| ≤ 1) (hξ : ∀ j, ξ j = toReal (ξm j) + toReal (ξr j) * δ j)
    (hP : ξ ∈ P.nominal.construct) : -- --- CONCL ---
    δ ∈ (P.rescaleCols ξm ξr).nominal.construct := by -- --- PROOF ---
  obtain ⟨hin, heq⟩ := HPolytope.mem_nominal_iff.mp hP
  -- the rounding of a scaled row against `δ`
  set dev : Vec 𝕋 n → ℝ := fun a =>
    ∑ j, (toReal (a j) * toReal (ξr j) - toReal (mulDown (a j) (ξr j))) * δ j with hdev
  set gap : Vec 𝕋 n → 𝕋 := fun a =>
    sumUp fun j => subUp (mulUp (a j) (ξr j)) (mulDown (a j) (ξr j)) with hgap
  -- a row's new bound at `δ`, between its two ends
  have hends : ∀ (a : Vec 𝕋 n) (c : 𝕋),
      toReal (subDown (subDown c (dotUp a ξm)) (gap a))
          ≤ toReal c - ∑ j, toReal (a j) * toReal (ξm j) - dev a
        ∧ toReal c - ∑ j, toReal (a j) * toReal (ξm j) - dev a
          ≤ toReal (addUp (subUp c (dotDown a ξm)) (gap a)) := by
    intro a c
    have hg := abs_le.mp (abs_sum_mulDown_gap_le a ξr δ hδ)
    have h1 := le_dotUp a ξm
    have h2 := dotDown_le a ξm
    have h3 := subDown_le_sub c (dotUp a ξm)
    have h4 := subDown_le_sub (subDown c (dotUp a ξm)) (gap a)
    have h5 := sub_le_subUp c (dotDown a ξm)
    have h6 := add_le_addUp (subUp c (dotDown a ξm)) (gap a)
    constructor <;> linarith [hg.1, hg.2]
  refine HPolytope.mem_setRhs_nominal _ _ _ (fun k => hends (P.A k) (P.b k))
    (fun k => hends (P.Ae k) (P.be k)) (fun k => ?_) (fun k => ?_)
  -- an inequality: the old row at `ξ`, less the part at `ξm` and the rounding
  · have hk := hin k
    have hs := sum_mul_affine_split (P.A k) ξm ξr δ ξ hξ
    simp only [mulVec, dotProduct, toRealMat] at hk
    show ∑ j, toReal (mulDown (P.A k j) (ξr j)) * δ j ≤ _ + |toReal (P.b_error k)|
    linarith
  -- an equality, read the same way from both sides
  · have hk := abs_le.mp (heq k)
    have hs := sum_mul_affine_split (P.Ae k) ξm ξr δ ξ hξ
    simp only [mulVec, dotProduct, toRealMat] at hk
    show |∑ j, toReal (mulDown (P.Ae k j) (ξr j)) * δ j - _| ≤ |toReal (P.be_error k)|
    rw [abs_le]
    constructor <;> linarith [hk.1, hk.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
