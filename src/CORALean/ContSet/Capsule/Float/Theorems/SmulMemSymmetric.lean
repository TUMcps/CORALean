module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# A generator's rounding at a segment parameter lies in the symmetric box of its bound

`t δ` lies in the box `[-m, m]` when `|t| ≤ 1` and `|δ| ≤ m` entrywise: each entry `|t δᵢ|` is at
most `|δᵢ|`. A capsule's points are `c + t g + w` for `t ∈ [-1, 1]`, so this is where the rounding
`δ` of a stored generator goes (#185).

## Inputs
* `m` – float bound vector
* `δ` – real vector
* `t` – segment parameter

## Hypotheses
* `ht` – `t` lies in `[-1, 1]`
* `hδ` – `δ` is entrywise at most `m`

## Conclusion
* `t • δ` lies in the symmetric box of `m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `t δ` lies in the symmetric box of `m` when `|t| ≤ 1` and `|δ| ≤ m` entrywise. -/
theorem Capsule.smul_mem_symmetric {m : Vec 𝕋 n} {δ : Vec ℝ n} {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hδ : ∀ i, |δ i| ≤ toReal (m i)) :
    t • δ ∈ (Interval.symmetric m).construct := by -- --- PROOF ---
  rw [Interval.mem_vec_iff]
  intro i
  have h : |t * δ i| ≤ toReal (m i) := by
    rw [abs_mul]
    exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr ht)) (hδ i)
  have hi := abs_le.mp h
  simp only [Interval.symmetric, Pi.neg_apply, toReal_neg', Pi.smul_apply, smul_eq_mul]
  exact ⟨hi.1, hi.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
