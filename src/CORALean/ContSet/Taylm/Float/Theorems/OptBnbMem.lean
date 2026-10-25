module

public import CORALean.ContSet.Taylm.Float.Operations.OptBnb
public import CORALean.ContSet.Taylm.Float.Theorems.BranchAndBoundMem
public import CORALean.ContSet.Taylm.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `Taylm.optBnb` encloses

Outer: a function the float model encloses lies in the result at every point of the normalized
box. The branch and bound's range of the polynomial plus the remainder with the error box absorbed
(`absorbRounding_nominal`), the ends rounded outward;
sound for every `ε` and `fuel`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `ε` – tolerance
* `fuel` – step budget
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `ht` – point lies in the unit box

## Conclusion
* the branch and bound enclosure contains the function's value
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.optBnb_mem {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (ε : 𝕋) (fuel : ℕ)
    {t : Vec ℝ n} (ht : t ∈ Real.Taylm.box n) : -- --- CONCL ---
    toReal (T.optBnb ε fuel).inf ≤ f t ∧ f t ≤ toReal (T.optBnb ε fuel).sup := by -- --- PROOF ---
  -- the normalized box as a float box
  have hX : Taylm.IsInBox (fun _ => ⟨neg one, one⟩ : Fin n → Interval 𝕋) t := fun k => by
    have := abs_le.1 (ht k)
    simp only [toReal_neg, toReal_one]
    exact this
  have hb := Taylm.branchAndBound_mem T.terms (fun _ => ⟨neg one, one⟩) ε false fuel hX
  have hr := Taylm.absorbRounding_nominal h t ht
  simp only [Taylm.nominal, Taylm.absorbRounding, Real.Taylm.poly] at hr
  have h1 := addDown_le_add (Taylm.branchAndBound T.terms (fun _ => ⟨neg one,
      one⟩) ε false fuel).inf
    (addDown T.rem.inf T.I_error.inf)
  have h2 := add_le_addUp (Taylm.branchAndBound T.terms (fun _ => ⟨neg one, one⟩) ε false fuel).sup
    (addUp T.rem.sup T.I_error.sup)
  simp only [Taylm.optBnb, Taylm.absorbRounding]
  constructor <;> linarith [hb.1, hb.2, hr.1, hr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
