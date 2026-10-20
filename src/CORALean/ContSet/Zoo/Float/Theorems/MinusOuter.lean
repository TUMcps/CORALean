module

public import CORALean.ContSet.Zoo.Float.Operations.Basic
public import CORALean.ContSet.Zoo.Float.Theorems.EnclosesIff
public import CORALean.ContSet.Taylm.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter

@[expose] public section

/-!
# `Zoo.minus` encloses

Every member of the result encloses the combined function: the Taylor model by
`Taylm.minus_outer`, the interval by `Interval.minus_outer` on the two box values (outer: the
rounding goes outward).

## Inputs
* `Z₁` – first zoo
* `Z₂` – second zoo
* `f` – first function
* `g` – second function

## Hypotheses
* `h₁` – `Z₁` encloses `f`
* `h₂` – `Z₂` encloses `g`

## Conclusion
* the difference zoo encloses `f - g`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.minus_outer {Z₁ Z₂ : Zoo 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : Z₁.Encloses f)
    (h₂ : Z₂.Encloses g) : -- --- CONCL ---
    (Z₁.minus Z₂).Encloses fun t => f t - g t := by -- --- PROOF ---
  rw [Zoo.encloses_iff] at h₁ h₂ ⊢
  refine ⟨fun T hT => ?_, fun I hI t ht => ?_⟩
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hT
    exact Taylm.minus_outer (h₁.1 a ha) (h₂.1 b hb)
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hI
    exact Interval.minus_outer _ _ (Set.sub_mem_sub (h₁.2 a ha t ht) (h₂.2 b hb t ht))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
