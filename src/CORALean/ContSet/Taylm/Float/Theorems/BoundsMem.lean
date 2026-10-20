module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PolyBoundsMem

@[expose] public section

/-!
# An enclosed function stays in the float `bounds` on the box

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `ht` – point lies in the unit box

## Conclusion
* the function value lies within the model's float bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bounds_mem {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) :
    toReal T.bounds.inf ≤ f t ∧ f t ≤ toReal T.bounds.sup := by -- --- PROOF ---
  have h₁ := h t ht
  have h₂ := Taylm.polyBounds_mem T.terms ht
  have := addDown_le_add (Taylm.polyBounds T.terms).inf T.rem.inf
  have := add_le_addUp (Taylm.polyBounds T.terms).sup T.rem.sup
  have := addDown_le_add (addDown (Taylm.polyBounds T.terms).inf T.rem.inf) T.I_error.inf
  have := add_le_addUp (addUp (Taylm.polyBounds T.terms).sup T.rem.sup) T.I_error.sup
  simp only [Taylm.bounds, Taylm.inflated, Real.Taylm.poly] at *
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
