module

public import CORALean.ContSet.Taylm.Float.Operations.BoundsMono
public import CORALean.ContSet.Taylm.Float.Theorems.PolyBoundsMonoMem

@[expose] public section

/-!
# `Taylm.boundsMono` holds the enclosed function

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `t` – point of the box

## Hypotheses
* `h` – the model encloses the function
* `ht` – `t` lies in the box `[-1, 1]ⁿ`

## Conclusion
* `f t` lies in the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.boundsMono_mem {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    {t : Vec ℝ n} (ht : t ∈ Real.Taylm.box n) : -- --- CONCL ---
    toReal T.boundsMono.inf ≤ f t ∧ f t ≤ toReal T.boundsMono.sup := by -- --- PROOF ---
  have a := h t ht
  have hP := Taylm.polyBoundsMono_mem T.terms ht
  have := addDown_le_add T.rem.inf (Taylm.polyBoundsMono T.terms).inf
  have := addDown_le_add (addDown T.rem.inf (Taylm.polyBoundsMono T.terms).inf) T.I_error.inf
  have := add_le_addUp T.rem.sup (Taylm.polyBoundsMono T.terms).sup
  have := add_le_addUp (addUp T.rem.sup (Taylm.polyBoundsMono T.terms).sup) T.I_error.sup
  simp only [Taylm.inflated, Real.Taylm.poly] at a
  simp only [Taylm.boundsMono]
  constructor <;> linarith [a.1, a.2, hP.1, hP.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
