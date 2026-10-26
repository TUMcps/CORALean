module

public import CORALean.ContSet.HPolytope.Float.Operations.IneqsContainBall
public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `HPolytope.ineqsContainBall` is sound

A point within `δ` of `β₀` in every coordinate reads a row at most `δ` times the row's absolute
sum away from `β₀`'s reading, and the test bounded both, rounded outward, by the bound with its
slack.

## Inputs
* `P` – H-polytope
* `β₀` – vector of length `n`
* `δ` – scalar
* `β` – vector of length `n`
* `i` – index below `P.m`

## Hypotheses
* `h` – `P.ineqsContainBall β₀ δ` holds
* `hδ` – `0 ≤ toReal δ`
* `hβ` – `β` is within `δ` of `β₀` in every coordinate

## Conclusion
* A passed test keeps every point within `δ` of `β₀` inside every inequality row
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row applied to a short vector moves by at most its absolute sum times the bound. -/
private theorem HPolytope.aux_row_move {m : ℕ} (M : Mat 𝕋 m n) (v : Vec ℝ n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hv : ∀ j, |v j| ≤ δ) (i : Fin m) : -- --- CONCL ---
    |(toRealMat M *ᵥ v) i| ≤ δ * toReal (radius M i) := by -- --- PROOF ---
  calc |(toRealMat M *ᵥ v) i| = |∑ j, toReal (M i j) * v j| := rfl
    _ ≤ ∑ j, |toReal (M i j) * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |toReal (M i j)| * δ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = δ * ∑ j, |toReal (M i j)| := by rw [← Finset.sum_mul]; ring
    _ ≤ δ * toReal (radius M i) := mul_le_mul_of_nonneg_left (sum_abs_le_radius i) hδ


-- =======================================  MAIN THEOREM  ======================================= --

/-- A passed test keeps every point within `δ` of `β₀` inside every inequality row. -/
theorem HPolytope.ineqsContainBall_sound {P : HPolytope 𝕋 (Vec 𝕋 n)} {β₀ : Vec 𝕋 n} {δ : 𝕋}
    (h : P.ineqsContainBall β₀ δ = true) (hδ : 0 ≤ toReal δ) {β : Vec ℝ n}
    (hβ : ∀ j, |β j - toReal (β₀ j)| ≤ toReal δ) (i : Fin P.m) : -- --- CONCL ---
    (toRealMat P.A *ᵥ β) i ≤ toReal (P.b i) + |toReal (P.b_error i)| := by -- --- PROOF ---
  simp only [HPolytope.ineqsContainBall, List.all_eq_true, List.mem_finRange, true_implies] at h
  -- the row at `β` is the row at `β₀` plus the row at the move
  have hsplit : (toRealMat P.A *ᵥ β) i
      = ∑ j, toReal (P.A i j) * toReal (β₀ j)
        + (toRealMat P.A *ᵥ fun j => β j - toReal (β₀ j)) i := by
    simp only [Matrix.mulVec, dotProduct, toRealMat]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 := toReal_le_of_le (h i)
  have h2 := add_le_addUp (dotUp (P.A i) β₀) (mulUp δ (radius P.A i))
  have h3 := le_dotUp (P.A i) β₀
  have h4 := mul_le_mulUp δ (radius P.A i)
  have h5 := (abs_le.mp (HPolytope.aux_row_move P.A _ hδ hβ i)).2
  have h6 := addDown_le_add (P.b i) (absolute (P.b_error i))
  rw [toReal_absolute] at h6
  rw [hsplit]
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
