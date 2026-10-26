module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound

@[expose] public section

/-!
# `backpropagation` keeps every solution

For a sound tree `t`, a target `value` inside `t.value` and a point `x` of the box with `t(x) ∈
value`,
`backpropagation(t,value,int)` returns a box that holds `x` (the `CORA:emptySet` error is not
thrown, nor
`CORA:outOfDomain`). So `contractForwardBackward`, which starts from `value = [0,0]` and `int =
dom`,
keeps every zero of the function in the domain.

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
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `backpropagation` of a sound tree returns a box holding every solution. -/
theorem SyntaxTree.backpropagation_isSound {B : Real.Interval (Vec ℝ n)} (t : SyntaxTree n)
    (h : IsSound B t) {int : Real.Interval (Vec ℝ n)} {x : Fin n → ℝ} (v : Dom)
    (hv : Dom.IsWithin v t.value) (hB : IsInBox B x) (hx : IsInBox int x)
    (hs : Dom.contains v (t.eval x)) : -- --- CONCL ---
    ∃ r, backpropagation t v int = .ok r ∧ IsInBox r x := by -- --- PROOF ---
  induction t generalizing v with
  | var i w =>
    have hc : Dom.contains v (x i) := hs
    have hcond : ¬ (¬ (max (v.inf 0) (int.inf i) ≤ min (v.sup 0) (int.sup i)) ∨
        v.sup 0 < v.inf 0) := by
      push Not
      exact ⟨max_le_iff.2 ⟨hc.1, (hx i).1⟩ |>.trans (le_min hc.2 (hx i).2), hc.1.trans hc.2⟩
    refine ⟨⟨Function.update int.inf i (max (v.inf 0) (int.inf i)),
      Function.update int.sup i (min (v.sup 0) (int.sup i))⟩,
      by simp only [backpropagation, hcond, if_false], fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      exact ⟨max_le hc.1 (hx j).1, le_min hc.2 (hx j).2⟩
    · simp only [Function.update_of_ne hj]
      exact hx j
  -- the next step
  | unary op w funHan t' ih =>
    obtain ⟨hsub, _, hu⟩ := h
    obtain ⟨val, hval, hc, hw⟩ := hu v hv (t'.eval x) (encloses_of_isSound hsub x hB) hs
    obtain ⟨r, hr, hxr⟩ := ih hsub val hw hc
    exact ⟨r, by simp only [backpropagation, hval]; exact hr, hxr⟩
  | binary op w funHan t₁ t₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂, _, hb⟩ := h
    obtain ⟨c₁, c₂, w₁, w₂⟩ := hb v hv (t₁.eval x) (t₂.eval x) (encloses_of_isSound h₁ x hB)
      (encloses_of_isSound h₂ x hB) hs
    obtain ⟨r₁, hr₁, hx₁⟩ := ih₁ h₁ _ w₁ c₁
    obtain ⟨r₂, hr₂, hx₂⟩ := ih₂ h₂ _ w₂ c₂
    exact ⟨_, by simp only [backpropagation, hr₁, hr₂], isInBox_intersection hx₁ hx₂⟩
  -- the next step
  | numLeft op w funHan c t' ih =>
    obtain ⟨hsub, _, hb⟩ := h
    obtain ⟨_, c₂, _, w₂⟩ := hb v hv c (t'.eval x) SyntaxTree.contains_interval (encloses_of_isSound
        hsub x hB) hs
    obtain ⟨r, hr, hxr⟩ := ih hsub _ w₂ c₂
    exact ⟨r, by simp only [backpropagation]; exact hr, hxr⟩
  | numRight op w funHan t' c ih =>
    -- take apart the hypothesis
    obtain ⟨hsub, _, hb⟩ := h
    obtain ⟨c₁, _, w₁, _⟩ := hb v hv (t'.eval x) c (encloses_of_isSound hsub x hB)
        SyntaxTree.contains_interval hs
    obtain ⟨r, hr, hxr⟩ := ih hsub _ w₁ c₁
    exact ⟨r, by simp only [backpropagation]; exact hr, hxr⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
