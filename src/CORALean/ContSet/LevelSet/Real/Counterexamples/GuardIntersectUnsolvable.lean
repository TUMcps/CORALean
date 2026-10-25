module

public import CORALean.ContSet.LevelSet.Real.Operations.GuardIntersectUnsolvable
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# [1, Prop. 2] with eq. (11) as printed misses part of the guard

The guard `g(x) = x₂ + x₁² = 0` on `I = [-1, 1] × [-2, 2]`, solved for `x₂` (`k = 2`). Its
order-`2` expansion at the box's center `c = 0` is exact: `b = 0`, `a = (0, 1)`,
`v(x) = x₁²` and remainder `[0, 0]` — [1, Def. 7]'s values, read off by hand here, since `g` is
quadratic. Eq. (11) as printed, `(−b + aᵀc − Σ_{i≠k} a(i)x(i) + v(x)) / a(k)`, is `x₁²`, all of
it free of `x₂`, so `p_k = x₁²`, `D_p = 0` and eq. (12) gives `[D_l, D_u] = [0, 0]`. The model is
the parabola `x₂ = x₁²`, while the guard is `x₂ = -x₁²`: `(1, -1)` is in `I ∩ G` and not in the
model. With `- v(x)`, `GuardIntersectUnsolvableSubset`, the model is `x₂ = -x₁²`, exact.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the guard intersection with eq. (11) as printed misses part of the guard

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem guardIntersectUnsolvable_printed_counterexample : -- --- CONCL ---
    let I : Interval (Vec ℝ 2) := ⟨![-1, -2], ![1, 2]⟩
    let g : Vec ℝ 2 → ℝ := fun x => x 1 + x 0 ^ 2
    let a : Vec ℝ 2 := ![0, 1]
    let c : Vec ℝ 2 := 0
    let v : Vec ℝ 2 → ℝ := fun x => x 0 ^ 2
    let pk : Vec ℝ 2 → ℝ := fun x => x 0 ^ 2
    let Dp : Vec ℝ 2 → ℝ := fun _ => 0
    -- the expansion encloses `g` with the remainder `[0, 0]`
    (∀ x ∈ I.construct, g x - (0 + ∑ i, a i * (x i - c i) + v x) ∈ Set.Icc 0 0) ∧
    -- eq. (11) as printed, `+ v(x)`, split into `p_k + D_p`
    (∀ x, (-0 + ∑ i, a i * c i - ∑ i ∈ Finset.univ.erase 1, a i * x i + v x) / a 1
      = pk x + Dp x) ∧
    -- eq. (12)
    (∀ x ∈ I.construct, ∀ r ∈ Set.Icc (0 : ℝ) 0, 0 ≤ Dp x - r / a 1 ∧ Dp x - r / a 1 ≤ 0) ∧
    ¬ I.construct ∩ {x | g x = 0} ⊆
      (guardIntersectUnsolvable I 1 pk 0 0).construct := by -- --- PROOF ---
  intro I g a c v pk Dp
  refine ⟨fun x _ => ?_, fun x => ?_, fun x _ r hr => ?_, fun hsub => ?_⟩
  · simp [g, a, c, v, Fin.sum_univ_two]
  · simp [a, c, v, pk, Dp, Fin.sum_univ_two, Finset.sum_erase_eq_sub]
  · have hr0 : r = 0 := le_antisymm hr.2 hr.1
    simp [Dp, hr0]
  · -- `(1, -1)` is on the guard, in the box, and off the parabola `x₂ = x₁²`
    have hy : (![1, -1] : Vec ℝ 2) ∈ I.construct ∩ {x | g x = 0} := by
      refine ⟨fun i => ?_, ?_⟩
      · show (![-1, -2] : Vec ℝ 2) i ≤ (![1, -1] : Vec ℝ 2) i ∧
          (![1, -1] : Vec ℝ 2) i ≤ (![1, 2] : Vec ℝ 2) i
        fin_cases i <;> norm_num
      · show (![1, -1] : Vec ℝ 2) 1 + (![1, -1] : Vec ℝ 2) 0 ^ 2 = 0
        norm_num
    obtain ⟨x, _, b, hb, hxb⟩ := hsub hy
    have hb0 : b = 0 := funext fun i => by
      have h : (Pi.single 1 0 : Vec ℝ 2) i ≤ b i ∧ b i ≤ (Pi.single 1 0 : Vec ℝ 2) i := hb i
      simp only [Pi.single_zero, Pi.zero_apply] at h
      exact le_antisymm h.2 h.1
    subst hb0
    have h0 := congrFun hxb 0
    have h1 := congrFun hxb 1
    simp [guardIntersectUnsolvable, intersectLevelSetBox, pk] at h0 h1
    rw [← h0] at h1
    norm_num at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
