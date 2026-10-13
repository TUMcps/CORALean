module

public import CORALean.ContSet.LevelSet.Real.Operations.IntersectLevelSetBox

@[expose] public section

/-!
# `intersect(I, LS)` is exact when `p_k` stays in the box and ignores `x(k)`

[1, Thm. 1]'s exactness: under condition (4), `min_I p_k ≥ l(k)` and `max_I p_k ≤ u(k)` —
read pointwise, `p_k(I) ⊆ [l(k), u(k)]` — the model is exactly `I ∩ LS`. That needs one more
hypothesis than [1] prints: `p_k` must not depend on `x(k)`. The proof "replaces `x(k)` with
`p_k(x)`", and an image point `h(x)` lies on `LS` only if `p_k(h(x)) = p_k(x)`;
`IntersectLevelSetBoxCounterexample` shows the equality failing without it. [1]'s two uses,
`Prop. 1` and `Prop. 2`, both ask `∂p_k/∂x(k) = 0` before applying the theorem.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem intersectLevelSetBox_exact (I : Interval (Vec ℝ n)) (k : Fin n) (p : Vec ℝ n → ℝ)
    (h4 : ∀ x ∈ I.construct, I.inf k ≤ p x ∧ p x ≤ I.sup k)
    (hind : ∀ x t, p (Function.update x k t) = p x) :
    I.construct ∩ {x | x k = p x} = (intersectLevelSetBox I k p).construct := by -- --- PROOF ---
  apply Set.Subset.antisymm
  · rintro x ⟨hxI, hxk⟩
    refine ⟨x, hxI, 0, fun i => ⟨le_rfl, le_rfl⟩, ?_⟩
    simp only [intersectLevelSetBox, add_zero]
    have hk : x k = p x := hxk
    rw [← hk, Function.update_eq_self]
  · rintro y ⟨x, hxI, b, hb, rfl⟩
    -- the zero box holds only `0`
    have hb0 : b = 0 := funext fun i => le_antisymm (hb i).2 (hb i).1
    subst hb0
    simp only [intersectLevelSetBox, add_zero]
    refine ⟨fun i => ?_, ?_⟩
    · show I.inf i ≤ Function.update x k (p x) i ∧ Function.update x k (p x) i ≤ I.sup i
      by_cases hik : i = k
      · subst hik
        simpa using h4 x hxI
      · have hi : I.inf i ≤ x i ∧ x i ≤ I.sup i := hxI i
        simpa [Function.update_of_ne hik] using hi
    · simp [hind]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
