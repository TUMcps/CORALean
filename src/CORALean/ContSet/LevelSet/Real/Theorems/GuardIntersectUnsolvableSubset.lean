module

public import CORALean.ContSet.LevelSet.Real.Operations.GuardIntersectUnsolvable
public import CORALean.ContSet.LevelSet.Real.Theorems.TaylorSeriesMem

@[expose] public section

/-!
# The unsolvable-guard model encloses the guard intersection

[1, Prop. 2], with eq. (11) corrected. Solving `0 = g(x) ∈ b + aᵀ(x - c) + v(x) ⊕ [l, u]` for
`x(k)` gives `x(k) ∈ (-b + aᵀc - Σ_{i≠k} a(i)x(i) - v(x)) / a(k) ⊕ -[l, u]/a(k)`: `v(x)` moves
to the other side with its sign flipped. [1] prints `+ v(x)` in (11) and in the proof's first
step, and with it the enclosure fails (`GuardIntersectUnsolvable`); [1]'s own
`Example 4` is computed with `- v(x)`. The split of (11) into `p_k + D_p` and the interval
`[D_l, D_u] ⊇ D_p(I) ⊕ -[l, u]/a(k)` of (12) are hypotheses, since they are taken on the
polynomial's monomials. [1] divides by `a(k)` without saying so; `a(k) ≠ 0` is supplied, and
`∂p_k/∂x(k) = 0` is not needed for the enclosure.

## Inputs
* `I` – box
* `κ` – Taylor order
* `k` – cut coordinate
* `g` – guard function
* `T` – Taylor series of `g` on `I`
* `pk` – polynomial part free of `x(k)`
* `Dp` – remaining part of the solved form
* `Dl` – lower remainder bound
* `Du` – upper remainder bound

## Hypotheses
* `hg` – `g` is `C^(κ+1)`
* `hκ` – `1 ≤ κ`
* `ha` – the gradient of `g` in `k` is nonzero
* `hsplit` – the solved form splits into `pk + Dp`
* `hD` – `[Dl, Du]` bounds `Dp` minus the scaled remainder

## Conclusion
* the box cut by the guard lies in the unsolvable-guard model

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same with any expansion of `g` that encloses it on the box. -/
theorem aux_guardIntersectUnsolvable_subset (I : Interval (Vec ℝ n)) (k : Fin n)
    {g : Vec ℝ n → ℝ} (b : ℝ) (a c : Vec ℝ n) (v : Vec ℝ n → ℝ) (l u : ℝ)
    (hT : ∀ x ∈ I.construct, g x - (b + ∑ i, a i * (x i - c i) + v x) ∈ Set.Icc l u)
    (ha : a k ≠ 0) (pk Dp : Vec ℝ n → ℝ)
    (hsplit : ∀ x, (-b + ∑ i, a i * c i - ∑ i ∈ Finset.univ.erase k, a i * x i - v x) / a k
      = pk x + Dp x)
    (Dl Du : ℝ)
    (hD : ∀ x ∈ I.construct, ∀ r ∈ Set.Icc l u, Dl ≤ Dp x - r / a k ∧ Dp x - r / a k ≤ Du) :
    I.construct ∩ {x | g x = 0} ⊆
      (guardIntersectUnsolvable I k pk Dl Du).construct := by -- --- PROOF ---
  rintro x ⟨hxI, hxg⟩
  have hxg : g x = 0 := hxg
  set r := g x - (b + ∑ i, a i * (x i - c i) + v x) with hr
  -- (13): x(k) = p_k(x) + D_p(x) - r/a(k)
  have hsum : ∑ i, a i * (x i - c i)
      = a k * x k + ∑ i ∈ Finset.univ.erase k, a i * x i - ∑ i, a i * c i := by
    rw [Finset.add_sum_erase _ (fun i => a i * x i) (Finset.mem_univ k)]
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hxk : x k = pk x + (Dp x - r / a k) := by
    rw [← add_sub_assoc, ← hsplit x]
    field_simp
    rw [hsum] at hr
    linarith
  -- `x` is `h(x)` plus that remainder in the `k`-th coordinate
  refine ⟨x, hxI, Pi.single k (Dp x - r / a k), fun i => ?_, ?_⟩
  · show (Pi.single k Dl : Vec ℝ n) i ≤ (Pi.single k (Dp x - r / a k) : Vec ℝ n) i ∧
      (Pi.single k (Dp x - r / a k) : Vec ℝ n) i ≤ (Pi.single k Du : Vec ℝ n) i
    by_cases hik : i = k
    · subst hik
      simp only [Pi.single_eq_same]
      exact hD x hxI r (hT x hxI)
    · simp [Pi.single_eq_of_ne hik]
  · funext i
    by_cases hik : i = k
    · subst hik
      simp [guardIntersectUnsolvable, intersectLevelSetBox, hxk]
    · simp [guardIntersectUnsolvable, intersectLevelSetBox, Function.update_of_ne hik,
        Pi.single_eq_of_ne hik]


-- =======================================  MAIN THEOREM  ======================================= --

theorem guardIntersectUnsolvable_subset {I : Interval (Vec ℝ n)} {κ : ℕ} (k : Fin n)
    {g : Vec ℝ n → ℝ} (T : TaylorSeries g I κ) (hg : ContDiff ℝ (κ + 1) g) (hκ : 1 ≤ κ)
    (ha : taylorGrad g I.center k ≠ 0) (pk Dp : Vec ℝ n → ℝ)
    (hsplit : ∀ x, (-g I.center + ∑ i, taylorGrad g I.center i * I.center i
      - ∑ i ∈ Finset.univ.erase k, taylorGrad g I.center i * x i - taylorHigher g κ I.center x)
        / taylorGrad g I.center k = pk x + Dp x)
    (Dl Du : ℝ) (hD : ∀ x ∈ I.construct, ∀ r ∈ Set.Icc T.l T.u,
      Dl ≤ Dp x - r / taylorGrad g I.center k ∧ Dp x - r / taylorGrad g I.center k ≤ Du)
    : -- --- CONCL ---
    I.construct ∩ {x | g x = 0} ⊆ (guardIntersectUnsolvable I k pk Dl Du).construct :=
  aux_guardIntersectUnsolvable_subset I k _ _ _ _ _ _ (fun _ hx => T.mem hg hκ hx) ha pk Dp
    hsplit Dl Du hD

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
