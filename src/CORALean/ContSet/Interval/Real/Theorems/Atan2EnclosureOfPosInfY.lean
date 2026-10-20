module

public import CORALean.ContSet.Interval.Real.Operations.Atan2
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqPiDivTwoSubArctanOfImPos
public import CORALean.ContSet.Interval.Real.Theorems.DivMemCornerHull

@[expose] public section

/-!
# `Interval.atan2` is an enclosure in the upper half-plane

When `0 < inf I₁` in every coordinate, `atan2 y x = π/2 - arctan (x / y)`: the quotient on the
box lies between its corner quotients (`div_mem_corner_hull`) and `π/2 - arctan` is antitone,
which swaps the corners the extremes sit at but not the four-corner hull. The box then misses the
branch cut, `x ≤ 0 ∧ y = 0`, the one place CORA's rule fails
(`Interval.atan2_cora_counterexample`).

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box
* `y` – ordinate point
* `x` – abscissa point

## Hypotheses
* `hy₀` – lower bounds of `I₁` positive
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

theorem Interval.atan2_enclosure_of_pos_inf_y {I₁ I₂ : Interval (Vec ℝ n)}
    (hy₀ : ∀ i, 0 < I₁.inf i) {y x : Vec ℝ n} (hy : y ∈ I₁.construct) (hxm : x ∈ I₂.construct) :
    (fun i => Complex.arg ⟨x i, y i⟩) ∈ (I₁.atan2 I₂).construct := by -- --- PROOF ---
  intro i
  obtain ⟨hy₁, hy₂⟩ : I₁.inf i ≤ y i ∧ y i ≤ I₁.sup i := hy i
  obtain ⟨hx₁, hx₂⟩ : I₂.inf i ≤ x i ∧ x i ≤ I₂.sup i := hxm i
  have hpos : 0 < I₁.inf i := hy₀ i
  -- every corner is `π/2 - arctan` of a quotient, and so is the point
  have hc : ∀ a b : ℝ, 0 < b → Complex.arg ⟨a, b⟩ = Real.pi / 2 - Real.arctan (a / b) :=
    fun a b hb => arg_eq_pi_div_two_sub_arctan_of_im_pos (z := ⟨a, b⟩) hb
  have hpos2 : 0 < I₁.sup i := lt_of_lt_of_le hpos (hy₁.trans hy₂)
  have hyp : 0 < y i := lt_of_lt_of_le hpos hy₁
  obtain ⟨hlo, hhi⟩ := div_mem_corner_hull hpos hx₁ hx₂ hy₁ hy₂
  have hm : Antitone fun q : ℝ => Real.pi / 2 - Real.arctan q :=
    fun a b hab => by
      have := Real.arctan_strictMono.monotone hab
      show Real.pi / 2 - Real.arctan b ≤ Real.pi / 2 - Real.arctan a
      linarith
  -- `S` antitone: the lower end of the quotient hull gives the upper end of the arguments
  refine ⟨?_, ?_⟩
  · show min (min (Complex.arg ⟨I₂.inf i, I₁.inf i⟩) (Complex.arg ⟨I₂.sup i, I₁.inf i⟩))
        (min (Complex.arg ⟨I₂.inf i, I₁.sup i⟩) (Complex.arg ⟨I₂.sup i, I₁.sup i⟩)) ≤
        Complex.arg ⟨x i, y i⟩
    simp only [hc _ _ hpos, hc _ _ hpos2, hc _ _ hyp]
    have h := hm hhi
    simp only [Antitone.map_max hm] at h
    refine le_trans (le_of_eq ?_) h
    simp only [min_assoc, min_left_comm]
  · show Complex.arg ⟨x i, y i⟩ ≤
        max (max (Complex.arg ⟨I₂.inf i, I₁.inf i⟩) (Complex.arg ⟨I₂.sup i, I₁.inf i⟩))
          (max (Complex.arg ⟨I₂.inf i, I₁.sup i⟩) (Complex.arg ⟨I₂.sup i, I₁.sup i⟩))
    simp only [hc _ _ hpos, hc _ _ hpos2, hc _ _ hyp]
    have h := hm hlo
    simp only [Antitone.map_min hm] at h
    refine le_trans h (le_of_eq ?_)
    simp only [max_assoc, max_left_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
