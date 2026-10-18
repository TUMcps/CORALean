module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLin
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# The center is the best expansion point

[1, Prop. 2]: `abstrErrLin`'s box is smallest at `zs = Z.c`. The radius `γ`
carries `|c - zs|` as an additive term in every coordinate, and a quadratic form
with nonnegative entries is monotone in a nonnegative argument, so any other
expansion point only inflates the box.

`hH` is what the proposition's `H` gives for free — it is an entrywise bound on
an absolute value — and the corollary is false without it: at `d = n = 1`, a
negative `H` turns the minimum into a maximum.

The printed proof argues the other half differently, and wrongly: it says the
second-derivative range `{ξ(z, z✱) | z ∈ Ẑ}` "is independent of `z✱`", so that
`max |Jᵢ|` is unaffected by it. That range is the convex hull of `Ẑ` and `z✱`,
which equals `Ẑ` exactly when `z✱ ∈ Ẑ` and is strictly larger otherwise, so the
max is affected. The corollary survives because the dependence runs one way: an
`H` valid for some `z✱` is valid at the center, which is why the same `H` stands
on both sides here.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {d n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A quadratic form with nonnegative entries grows with its argument. -/
theorem aux_quad_mono {M : Mat ℝ d d} (hM : ∀ j k, 0 ≤ M j k) {γ δ : Vec ℝ d}
    (hγ : ∀ j, 0 ≤ γ j) (h : ∀ j, γ j ≤ δ j) : γ ⬝ᵥ (M *ᵥ γ) ≤ δ ⬝ᵥ (M *ᵥ δ) := by
  simp only [dotProduct, mulVec]
  refine Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul (h j) (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (hM j k))
    (Finset.sum_nonneg fun k _ => mul_nonneg (hM j k) (hγ k)) (le_trans (hγ j) (h j))


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: the error box at the center of `Z` is inside the one at any
other expansion point. -/
theorem abstrErrLin_center_subset {H : Fin n → Mat ℝ d d} (hH : ∀ i j k, 0 ≤ H i j k)
    (Z : Zonotope (Vec ℝ d)) (zs : Vec ℝ d) :
    construct (abstrErrLin H Z Z.c) ⊆ construct (abstrErrLin H Z zs) := by -- --- PROOF ---
  set γc : Vec ℝ d := fun j => |Z.c j - Z.c j| + ∑ k, |Z.G k j| with hγc
  set γ : Vec ℝ d := fun j => |Z.c j - zs j| + ∑ k, |Z.G k j| with hγ
  have hnn : ∀ j, 0 ≤ γc j := fun j =>
    add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => abs_nonneg _)
  -- the two radii differ by `|c - zs|` alone, which is where the center wins
  have hle : ∀ j, γc j ≤ γ j := fun j => by
    simp only [hγc, hγ, sub_self, abs_zero, zero_add]
    have := abs_nonneg (Z.c j - zs j)
    linarith
  intro w hw i
  have hmono := aux_quad_mono (hH i) hnn hle
  have h1 : -(γc ⬝ᵥ (H i *ᵥ γc) / 2) ≤ w i := (hw i).1
  have h2 : w i ≤ γc ⬝ᵥ (H i *ᵥ γc) / 2 := (hw i).2
  exact ⟨by show -(γ ⬝ᵥ (H i *ᵥ γ) / 2) ≤ w i; linarith,
    by show w i ≤ γ ⬝ᵥ (H i *ᵥ γ) / 2; linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
