module

public import CORALean.ContSet.LevelSet.Real.Operations.GuardIntersectSolvable
public import CORALean.ContSet.LevelSet.Real.Theorems.TaylorSeriesMem

@[expose] public section

/-!
# The solvable-guard model encloses the guard intersection

[1, Prop. 1]: if the guard `{x | g(x) = 0}` equals `{x | x(k) = D_g(x)}` and `taylor(D_g, I, κ)`
is [1, Def. 7]'s expansion, then `I ∩ G ⊆ {T(x) | x ∈ I}` for the model of eq. (8). A point
`x` of the cut is `h(x)` plus `x(k) - p_k(x)` in the `k`-th coordinate, and that difference is
`D_g(x) - p_k(x)`, the Taylor remainder, inside `[l, u]` — eq. (9). [1, Def. 7]'s enclosure
needs `D_g` of class `C^{κ+1}` and `1 ≤ κ` (`TaylorSeriesMem`). [1]'s `∂D_g/∂x(k) = 0` is not
used: it matters for exactness, which the proposition does not claim. The auxiliary statement is
the same for any expansion that encloses `D_g`.

## Inputs
* `I` – box
* `κ` – Taylor order
* `k` – solved coordinate
* `g` – guard function
* `D` – function solving the guard for `x(k)`
* `T` – Taylor series of `D` on `I`

## Hypotheses
* `hG` – the guard is `x(k) = D x`
* `hD` – `D` is `C^(κ+1)`
* `hκ` – `1 ≤ κ`

## Conclusion
* the box cut by the guard lies in the solvable-guard model

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

/-- Eq. (9) with any polynomial part and remainder that enclose `D_g` on the box. -/
theorem aux_guardIntersectSolvable_subset (I : Interval (Vec ℝ n)) (k : Fin n)
    {g D : Vec ℝ n → ℝ} (hG : {x | g x = 0} = {x | x k = D x}) (b : ℝ) (a c : Vec ℝ n)
    (v : Vec ℝ n → ℝ) (l u : ℝ)
    (hT : ∀ x ∈ I.construct, D x - (b + ∑ i, a i * (x i - c i) + v x) ∈ Set.Icc l u) :
    I.construct ∩ {x | g x = 0} ⊆
      (guardIntersectSolvable I k b a c v l u).construct := by -- --- PROOF ---
  rintro x ⟨hxI, hxg⟩
  have hxk : x k = D x := by rw [hG] at hxg; exact hxg
  set pk := b + ∑ i, a i * (x i - c i) + v x with hpk
  have hr := hT x hxI
  refine ⟨x, hxI, Pi.single k (x k - pk), fun i => ?_, ?_⟩
  · -- the remainder sits in the `k`-th coordinate, zero elsewhere
    show (Pi.single k l : Vec ℝ n) i ≤ (Pi.single k (x k - pk) : Vec ℝ n) i ∧
      (Pi.single k (x k - pk) : Vec ℝ n) i ≤ (Pi.single k u : Vec ℝ n) i
    by_cases hik : i = k
    · subst hik
      simp only [Pi.single_eq_same]
      rw [hxk]
      exact hr
    · simp [Pi.single_eq_of_ne hik]
  · funext i
    by_cases hik : i = k
    · subst hik
      simp [guardIntersectSolvable, intersectLevelSetBox, hpk]
    · simp [guardIntersectSolvable, intersectLevelSetBox, Function.update_of_ne hik,
        Pi.single_eq_of_ne hik]


-- =======================================  MAIN THEOREM  ======================================= --

theorem guardIntersectSolvable_subset {I : Interval (Vec ℝ n)} {κ : ℕ} (k : Fin n)
    {g D : Vec ℝ n → ℝ} (hG : {x | g x = 0} = {x | x k = D x}) (T : TaylorSeries D I κ)
    (hD : ContDiff ℝ (κ + 1) D) (hκ : 1 ≤ κ) : -- --- CONCL ---
    I.construct ∩ {x | g x = 0} ⊆ (guardIntersectSolvable I k (D I.center) (taylorGrad D I.center)
      I.center (taylorHigher D κ I.center) T.l T.u).construct :=
  aux_guardIntersectSolvable_subset I k hG _ _ _ _ _ _ fun _ hx => T.mem hD hκ hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
