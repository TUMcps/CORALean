module

public import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevLo
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevHi
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# What rounding a scaled row costs, bounded over a domain

For `x` in the domain, `(s v - ṽ)ᵀ x` lies between `scaleDevLo` and `scaleDevHi`, where `ṽ` is
`s v` rounded down: each entry's deviation is between the two roundings of `s vⱼ` less the stored
entry, and each product between its rounded corners (`mul_between_corners`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.scaleDev_between (v : Vec 𝕋 n) (s : 𝕋) (dom : Interval (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ dom.construct) :
    toReal (HPolytope.scaleDevLo v s dom)
        ≤ ∑ j, (toReal s * toReal (v j) - toReal (mulDown (v j) s)) * x j
      ∧ ∑ j, (toReal s * toReal (v j) - toReal (mulDown (v j) s)) * x j
        ≤ toReal (HPolytope.scaleDevHi v s dom) := by -- --- PROOF ---
  have hdev : ∀ j, toReal (subDown (mulDown (v j) s) (mulDown (v j) s))
        ≤ toReal s * toReal (v j) - toReal (mulDown (v j) s)
      ∧ toReal s * toReal (v j) - toReal (mulDown (v j) s)
        ≤ toReal (subUp (mulUp (v j) s) (mulDown (v j) s)) := by
    intro j
    have h3 := mulDown_le_mul (v j) s
    have h4 := mul_le_mulUp (v j) s
    have h5 := subDown_le_sub (mulDown (v j) s) (mulDown (v j) s)
    have h6 := sub_le_subUp (mulUp (v j) s) (mulDown (v j) s)
    constructor <;> nlinarith
  have hxj : ∀ j, toReal (dom.inf j) ≤ x j ∧ x j ≤ toReal (dom.sup j) := hx
  have hprod := fun j => Interval.mul_between_corners (hdev j).1 (hdev j).2 (hxj j).1 (hxj j).2
  exact ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun j _ => (hprod j).1),
    le_trans (Finset.sum_le_sum fun j _ => (hprod j).2) (sum_le_sumUp _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
