module

public import CORALean.ContSet.Interval.Real.Operations.Atan2
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqNegPiDivTwoSubArctanOfImNeg
public import CORALean.ContSet.Interval.Real.Theorems.DivMemCornerHull

@[expose] public section

/-!
# `Interval.atan2` is an enclosure in the lower half-plane

When `sup I₁ < 0` in every coordinate, `atan2 y x = -(π/2) - arctan (x / y)`: the quotient
`x / y = (-x) / (-y)` on the box lies between its corner quotients (`div_mem_corner_hull`) and
`-(π/2) - arctan` is antitone, which swaps the corners the extremes sit at but not the
four-corner hull. The box then misses the
branch cut, `x ≤ 0 ∧ y = 0`, the one place CORA's rule fails
(`Interval.atan2_cora_counterexample`).

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box
* `y` – ordinate point
* `x` – abscissa point

## Hypotheses
* `hy₀` – upper bounds of `I₁` negative
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

theorem Interval.atan2_enclosure_of_neg_sup_y {I₁ I₂ : Interval (Vec ℝ n)}
    (hy₀ : ∀ i, I₁.sup i < 0) {y x : Vec ℝ n} (hy : y ∈ I₁.construct)
    (hxm : x ∈ I₂.construct) : -- --- CONCL ---
    (fun i => Complex.arg ⟨x i, y i⟩) ∈ (I₁.atan2 I₂).construct := by -- --- PROOF ---
  intro i
  obtain ⟨hy₁, hy₂⟩ : I₁.inf i ≤ y i ∧ y i ≤ I₁.sup i := hy i
  obtain ⟨hx₁, hx₂⟩ : I₂.inf i ≤ x i ∧ x i ≤ I₂.sup i := hxm i
  have hneg : I₁.sup i < 0 := hy₀ i
  -- every corner is `-(π/2) - arctan` of a quotient, and so is the point
  have hc : ∀ a b : ℝ, b < 0 → Complex.arg ⟨a, b⟩ = -(Real.pi / 2) - Real.arctan (a / b) :=
    fun a b hb => arg_eq_neg_pi_div_two_sub_arctan_of_im_neg (z := ⟨a, b⟩) hb
  have hneg1 : I₁.inf i < 0 := lt_of_le_of_lt (hy₁.trans hy₂) hneg
  have hyn : y i < 0 := lt_of_le_of_lt hy₂ hneg
  -- `x / y = (-x) / (-y)`, a quotient by a positive number
  obtain ⟨hlo, hhi⟩ := div_mem_corner_hull (n := -x i) (n₁ := -I₂.sup i) (n₂ := -I₂.inf i)
    (d₁ := -I₁.sup i) (d₂ := -I₁.inf i) (d := -y i) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
  simp only [neg_div_neg_eq] at hlo hhi
  have hm : Antitone fun q : ℝ => -(Real.pi / 2) - Real.arctan q :=
    fun a b hab => by
      have := Real.arctan_strictMono.monotone hab
      show -(Real.pi / 2) - Real.arctan b ≤ -(Real.pi / 2) - Real.arctan a
      linarith
  -- `S` antitone: the lower end of the quotient hull gives the upper end of the arguments
  refine ⟨?_, ?_⟩
  · show min (min (Complex.arg ⟨I₂.inf i, I₁.inf i⟩) (Complex.arg ⟨I₂.sup i, I₁.inf i⟩))
        (min (Complex.arg ⟨I₂.inf i, I₁.sup i⟩) (Complex.arg ⟨I₂.sup i, I₁.sup i⟩)) ≤
        Complex.arg ⟨x i, y i⟩
    simp only [hc _ _ hneg, hc _ _ hneg1, hc _ _ hyn]
    have h := hm hhi
    simp only [Antitone.map_max hm] at h
    refine le_trans (le_of_eq ?_) h
    simp only [min_assoc, min_comm, min_left_comm]
  · show Complex.arg ⟨x i, y i⟩ ≤
        max (max (Complex.arg ⟨I₂.inf i, I₁.inf i⟩) (Complex.arg ⟨I₂.sup i, I₁.inf i⟩))
          (max (Complex.arg ⟨I₂.inf i, I₁.sup i⟩) (Complex.arg ⟨I₂.sup i, I₁.sup i⟩))
    simp only [hc _ _ hneg, hc _ _ hneg1, hc _ _ hyn]
    have h := hm hlo
    simp only [Antitone.map_min hm] at h
    refine le_trans h (le_of_eq ?_)
    simp only [max_assoc, max_comm, max_left_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
