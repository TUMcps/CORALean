module

public import CORALean.ContSet.Zonotope.Float.Definitions.ContainsAt
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `Zonotope.plus` puts the weights side by side

`Zonotope.plus` puts the generators of its second operand after those of the first and pays the
center's rounding into the error box, so the sum of points at `β₁` and `β₂` is a point of the sum
at `Fin.append β₁ β₂`.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope
* `β₁` – weights of the first's generators
* `β₂` – weights of the second's generators
* `x₁` – point of the first
* `x₂` – point of the second

## Hypotheses
* `h₁` – `x₁` is in `Z₁` at `β₁`
* `h₂` – `x₂` is in `Z₂` at `β₂`

## Conclusion
* the sum is in the sum at the weights side by side
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   23-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sum of points at `β₁` and `β₂` is at the weights side by side in the sum. -/
theorem Zonotope.containsAt_plus {Z₁ Z₂ : Zonotope (Vec 𝕋 n)} {β₁ : Vec ℝ Z₁.h}
    {β₂ : Vec ℝ Z₂.h} {x₁ x₂ : Vec ℝ n} (h₁ : Z₁.ContainsAt β₁ x₁)
    (h₂ : Z₂.ContainsAt β₂ x₂) : -- --- CONCL ---
    (Z₁.plus Z₂).ContainsAt (Fin.append β₁ β₂) (x₁ + x₂) := by -- --- PROOF ---
  obtain ⟨hβ₁, e₁, he₁, hx₁⟩ := h₁
  obtain ⟨hβ₂, e₂, he₂, hx₂⟩ := h₂
  -- the stored center is below the exact sum, by this much
  have hr := Interval.sub_mem_residual (stored := fun i => addDown (Z₁.c i) (Z₂.c i))
    (x := fun i => toReal (Z₁.c i) + toReal (Z₂.c i))
    (lo := fun i => addDown (Z₁.c i) (Z₂.c i)) (hi := fun i => addUp (Z₁.c i) (Z₂.c i))
    (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  refine ⟨?_, _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨e₁, he₁, e₂, he₂, rfl⟩,
    _, hr, rfl⟩, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_)
    · simpa using hβ₁ l
    · simpa using hβ₂ l
  · show _ = toReal (addDown (Z₁.c i) (Z₂.c i)) + ∑ j : Fin (Z₁.h + Z₂.h),
      toReal (Fin.append Z₁.G Z₂.G j i) * Fin.append β₁ β₂ j + _
    rw [Fin.sum_univ_add]
    simp only [Pi.add_apply, hx₁ i, hx₂ i, Fin.append_left, Fin.append_right]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
