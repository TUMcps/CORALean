module

public import CORALean.ContSet.HPolytope.Float.Operations.SetRhs
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff

@[expose] public section

/-!
# What `HPolytope.setRhs` keeps

A point that reads every inequality within its slack of a value `rᵢ` between `loᵢ` and `hiᵢ`,
and every equality within its slack of a value `rEᵢ` between `loEᵢ` and `hiEᵢ`, lies in the
nominal part of the result: the stored bound is the lower end, and the width the slack gained
covers the rest of the way, on either side of an equality.
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

/-- A point within its slacks of right-hand sides between `lo` and `hi` (`loE` and `hiE`) is in
the nominal part `setRhs` builds. -/
theorem HPolytope.mem_setRhs_nominal (P : HPolytope 𝕋 (Vec 𝕋 n)) {lo hi : Vec 𝕋 P.m}
    {loE hiE : Vec 𝕋 P.me} {y : Vec ℝ n} (r : Fin P.m → ℝ) (rE : Fin P.me → ℝ)
    (hr : ∀ i, toReal (lo i) ≤ r i ∧ r i ≤ toReal (hi i))
    (hrE : ∀ i, toReal (loE i) ≤ rE i ∧ rE i ≤ toReal (hiE i))
    (hA : ∀ i, (toRealMat P.A *ᵥ y) i ≤ r i + |toReal (P.b_error i)|)
    (hE : ∀ i, |(toRealMat P.Ae *ᵥ y) i - rE i| ≤ |toReal (P.be_error i)|) : -- --- CONCL ---
    y ∈ (P.setRhs lo hi loE hiE).nominal.construct := by -- --- PROOF ---
  refine HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
  -- an inequality: the lower end plus the width reaches past `rᵢ`
  · set w := addUp (absolute (P.b_error i)) (subUp (hi i) (lo i))
    show (toRealMat P.A *ᵥ y) i ≤ toReal (lo i) + |toReal w|
    have h1 := add_le_addUp (absolute (P.b_error i)) (subUp (hi i) (lo i))
    have h2 := sub_le_subUp (hi i) (lo i)
    rw [toReal_absolute] at h1
    linarith [hA i, (hr i).2, le_abs_self (toReal w)]
  -- an equality: `rEᵢ` lies within the width above the lower end
  · set w := addUp (absolute (P.be_error i)) (subUp (hiE i) (loE i))
    show |(toRealMat P.Ae *ᵥ y) i - toReal (loE i)| ≤ |toReal w|
    have h1 := add_le_addUp (absolute (P.be_error i)) (subUp (hiE i) (loE i))
    have h2 := sub_le_subUp (hiE i) (loE i)
    rw [toReal_absolute] at h1
    have hz := abs_le.mp (hE i)
    have hw := le_abs_self (toReal w)
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2, (hrE i).1, (hrE i).2,
      abs_nonneg (toReal (P.be_error i))]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
