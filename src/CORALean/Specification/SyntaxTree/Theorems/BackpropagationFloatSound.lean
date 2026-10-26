module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.BackpropagationFloat
public import CORALean.Specification.SyntaxTree.Operations.ValueFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat

@[expose] public section

/-!
# `backpropagation` over floats keeps every solution

For a sound float tree `t`, a target `value` inside `t.value` and a point `x` of the box with `t(x)
∈ value`, `backpropagationFloat(t,value,int)` returns a box that holds `x` (the `CORA:emptySet`
error is not thrown, nor `CORA:outOfDomain`). So a float `contractForwardBackward`, which starts
from `value = [0,0]` and `int = dom`, never removes a real zero of the function from the domain,
whatever the rounding.

## Inputs
* `B` – box of the variables
* `t` – tree
* `int` – current box
* `x` – point
* `v` – target interval

## Hypotheses
* `h` – the tree is sound over the box
* `hv` – the target lies within the tree's value
* `hB` – the point lies in the box
* `hx` – the point lies in the current box
* `hs` – the tree's value at the point lies in the target

## Conclusion
* backpropagation succeeds with a box containing the point
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `backpropagationFloat` of a sound float tree returns a box holding every solution. -/
theorem SyntaxTree.backpropagationFloat_sound {B : Float.Interval (Vec 𝕋 n)}
    (t : Float.SyntaxTree 𝕋 n) (h : SyntaxTree.IsSoundFloat B t) {int : Float.Interval (Vec 𝕋 n)}
    {x : Fin n → ℝ} (v : Float.SyntaxTree.Dom 𝕋) (hv : v.IsWithin t.value)
    (hB : Float.SyntaxTree.IsInBox B x) (hx : Float.SyntaxTree.IsInBox int x)
    (hs : v.contains (t.eval x)) : -- --- CONCL ---
    ∃ r, SyntaxTree.backpropagationFloat t v int = .ok r ∧ Float.SyntaxTree.IsInBox r
      x := by -- --- PROOF ---
  induction t generalizing v with
  | var i w =>
    have hc : v.contains (x i) := hs
    have hcond : ¬ (ltStrict (minimum (v.sup 0) (int.sup i))
        (maximum (v.inf 0) (int.inf i)) = true ∨
        ltStrict (v.sup 0) (v.inf 0) = true) := by
      rintro (hlt | hlt)
      · have := toReal_lt_of_ltStrict hlt
        simp only [toReal_maximum, toReal_minimum] at this
        linarith [max_le hc.1 (hx i).1, le_min hc.2 (hx i).2]
      · linarith [toReal_lt_of_ltStrict hlt, hc.1, hc.2]
    refine ⟨⟨Function.update int.inf i (maximum (v.inf 0) (int.inf i)),
      Function.update int.sup i (minimum (v.sup 0) (int.sup i))⟩,
      by simp only [SyntaxTree.backpropagationFloat, if_neg hcond], fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, toReal_maximum, toReal_minimum]
      exact ⟨max_le hc.1 (hx j).1, le_min hc.2 (hx j).2⟩
    · simp only [Function.update_of_ne hj]
      exact hx j
  -- the next step
  | unary op w funHan t' ih =>
    obtain ⟨hsub, _, hu⟩ := h
    obtain ⟨val, hval, hc, hw⟩ := hu v hv (t'.eval x) (SyntaxTree.encloses_of_soundFloat hsub x hB)
      hs
    obtain ⟨r, hr, hxr⟩ := ih hsub val hw hc
    exact ⟨r, by simp only [SyntaxTree.backpropagationFloat, hval]; exact hr, hxr⟩
  | binary op w funHan t₁ t₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂, _, hb⟩ := h
    obtain ⟨c₁, c₂, w₁, w₂⟩ := hb v hv (t₁.eval x) (t₂.eval x)
      (SyntaxTree.encloses_of_soundFloat h₁ x hB) (SyntaxTree.encloses_of_soundFloat h₂ x hB) hs
    obtain ⟨r₁, hr₁, hx₁⟩ := ih₁ h₁ _ w₁ c₁
    obtain ⟨r₂, hr₂, hx₂⟩ := ih₂ h₂ _ w₂ c₂
    exact ⟨Float.Interval.intersection r₁ r₂,
      by simp only [SyntaxTree.backpropagationFloat, hr₁, hr₂], fun j => by
        simp only [Float.Interval.intersection, toReal_maximum, toReal_minimum]
        exact ⟨max_le (hx₁ j).1 (hx₂ j).1, le_min (hx₁ j).2 (hx₂ j).2⟩⟩
  -- the next step
  | numLeft op w funHan c t' ih =>
    obtain ⟨hsub, _, hb⟩ := h
    obtain ⟨_, c₂, _, w₂⟩ := hb v hv (toReal c) (t'.eval x) SyntaxTree.contains_intervalFloat
      (SyntaxTree.encloses_of_soundFloat hsub x hB) hs
    obtain ⟨r, hr, hxr⟩ := ih hsub _ w₂ c₂
    exact ⟨r, by simp only [SyntaxTree.backpropagationFloat]; exact hr, hxr⟩
  | numRight op w funHan t' c ih =>
    -- take apart the hypothesis
    obtain ⟨hsub, _, hb⟩ := h
    obtain ⟨c₁, _, w₁, _⟩ := hb v hv (t'.eval x) (toReal c)
      (SyntaxTree.encloses_of_soundFloat hsub x hB) SyntaxTree.contains_intervalFloat hs
    obtain ⟨r, hr, hxr⟩ := ih hsub _ w₁ c₁
    exact ⟨r, by simp only [SyntaxTree.backpropagationFloat]; exact hr, hxr⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
