module

public import CORALean.ContSet.Interval.Real.Operations.Atan2
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqArctanOfRePos
public import CORALean.ContSet.Interval.Real.Theorems.DivMemCornerHull

@[expose] public section

/-!
# `Interval.atan2` is an enclosure in the right half-plane

CORA's corner hull (`Interval.atan2`) encloses `atan2 y x` for `y ∈ I₁`, `x ∈ I₂` when
`0 < inf I₂`, in every coordinate: there `atan2 y x = arctan (y / x)`, the quotient on a box lies
between its corner quotients (`div_mem_corner_hull`), and `arctan` is monotone. Off the cut
(`x ≤ 0 ∧ y = 0`), the one place the code is wrong (`Interval.atan2_cora_counterexample`), so
the rule is sound where the box does not reach it; a box meeting the upper or lower half-plane
only is not covered here.

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box
* `y` – ordinate point
* `x` – abscissa point

## Hypotheses
* `hx` – lower bounds of `I₂` positive
* `hy` – `y` lies in `I₁`
* `hxm` – `x` lies in `I₂`

## Conclusion
* the vector of arguments lies in the result box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.atan2_enclosure_of_pos_inf_x {I₁ I₂ : Interval (Vec ℝ n)}
    (hx : ∀ i, 0 < I₂.inf i) {y x : Vec ℝ n} (hy : y ∈ I₁.construct) (hxm : x ∈ I₂.construct) :
    (fun i => Complex.arg ⟨x i, y i⟩) ∈ (I₁.atan2 I₂).construct := by -- --- PROOF ---
  intro i
  obtain ⟨hy₁, hy₂⟩ : I₁.inf i ≤ y i ∧ y i ≤ I₁.sup i := hy i
  obtain ⟨hx₁, hx₂⟩ : I₂.inf i ≤ x i ∧ x i ≤ I₂.sup i := hxm i
  have hpos : 0 < I₂.inf i := hx i
  -- every corner is an arctangent of a quotient, and so is the point
  have hc : ∀ a b : ℝ, 0 < a → Complex.arg ⟨a, b⟩ = Real.arctan (b / a) :=
    fun a b ha => arg_eq_arctan_of_re_pos (z := ⟨a, b⟩) ha
  have hpos2 : 0 < I₂.sup i := lt_of_lt_of_le hpos (hx₁.trans hx₂)
  have hxp : 0 < x i := lt_of_lt_of_le hpos hx₁
  obtain ⟨hlo, hhi⟩ := div_mem_corner_hull hpos hy₁ hy₂ hx₁ hx₂
  have hm := Real.arctan_strictMono.monotone
  refine ⟨?_, ?_⟩
  · show min (min (Complex.arg ⟨I₂.inf i, I₁.inf i⟩) (Complex.arg ⟨I₂.sup i, I₁.inf i⟩))
        (min (Complex.arg ⟨I₂.inf i, I₁.sup i⟩) (Complex.arg ⟨I₂.sup i, I₁.sup i⟩)) ≤
        Complex.arg ⟨x i, y i⟩
    simp only [hc _ _ hpos, hc _ _ hpos2, hc _ _ hxp]
    rw [← hm.map_min, ← hm.map_min, ← hm.map_min]
    exact hm hlo
  · show Complex.arg ⟨x i, y i⟩ ≤
        max (max (Complex.arg ⟨I₂.inf i, I₁.inf i⟩) (Complex.arg ⟨I₂.sup i, I₁.inf i⟩))
          (max (Complex.arg ⟨I₂.inf i, I₁.sup i⟩) (Complex.arg ⟨I₂.sup i, I₁.sup i⟩))
    simp only [hc _ _ hpos, hc _ _ hpos2, hc _ _ hxp]
    rw [← hm.map_max, ← hm.map_max, ← hm.map_max]
    exact hm hhi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
