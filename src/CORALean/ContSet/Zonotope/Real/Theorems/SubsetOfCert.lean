module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Zonotope in zonotope, sufficiently

`[1, Thm. 3]`: `⟨x̄, X⟩ ⊆ ⟨ȳ, Y⟩` if `X = Y Γ`, `ȳ - x̄ = Y β` and `‖(Γ, β)‖∞ ≤ 1`, the
largest absolute row sum of `Γ` beside `β`. Read off directly: `x̄ + X a = ȳ + Y (Γ a - β)`,
and each coordinate of `Γ a - β` is at most that row's sum. Stated in generators, so over
any real module: `X = Y Γ` says each `Xⱼ = ∑ₖ Γₖⱼ Yₖ`.

Not necessary (`[1, Example 2]`), and that is what `Contains` asks of it: CORA's
`'approx:st'` is this condition, a linear program in `(Γ, β)`.

## Inputs
* `Zx` – inner zonotope
* `Zy` – outer zonotope
* `Γ` – generator coefficient matrix
* `β` – center coefficients

## Hypotheses
* `hX` – generators of `Zx` expressed through `Zy`
* `hβ` – center difference expressed through `Zy`
* `hn` – row sums at most one

## Conclusion
* `Zx` lies in `Zy`

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_subset_of_cert (Zx Zy : Zonotope α) (Γ : Mat ℝ Zy.h Zx.h)
    (β : Vec ℝ Zy.h) (hX : ∀ j, Zx.G j = ∑ k, Γ k j • Zy.G k)
    (hβ : Zy.c - Zx.c = ∑ k, β k • Zy.G k) (hn : ∀ k, ∑ j, |Γ k j| + |β k| ≤ 1) :
    Zx.construct ⊆ Zy.construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨fun k => ∑ j, Γ k j * a j - β k, fun k => ?_, ?_⟩
  -- a coordinate is at most its row's absolute sum
  · have h1 : |∑ j, Γ k j * a j| ≤ ∑ j, |Γ k j| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (ha j)
    calc |∑ j, Γ k j * a j - β k| ≤ |∑ j, Γ k j * a j| + |β k| := abs_sub _ _
      _ ≤ 1 := by linarith [hn k]
  -- `x̄ + X a = ȳ + Y (Γ a - β)`
  · have hc : Zx.c = Zy.c - ∑ k, β k • Zy.G k := by rw [← hβ]; abel
    rw [hc]
    simp only [hX, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
    rw [Finset.sum_comm (f := fun j k => (a j * Γ k j) • Zy.G k)]
    simp only [mul_comm (a _)]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
