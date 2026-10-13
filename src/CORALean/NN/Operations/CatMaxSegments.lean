import CORALean.NN.Operations.CatMaxSegment

/-!
# Max pooling over a row of windows as a CAT function

[1, Sec. II (MaxPool to CAT)]'s `f_{mn r/(pq)} ∘ … ∘ f₁` after the reordering: of `a` coordinates
already pooled and `r` windows of `k + 1` behind them, pool the first window with
`Cat.maxSegment`, then the rest from `a + 1`. The dimensions `a + (k + 1) (r + 1)` and
`a + (k + 1) + (k + 1) r` are equal and not by definition, so each step is framed by two
affine identity maps that only rename coordinates, which the paper's arithmetic on indices
does silently.

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fₐ₊ᵣ ∘ … ∘ fₐ₊₁` on `a` pooled coordinates and `r` windows of `k + 1`. -/
def Cat.maxSegments (k : ℕ) : (a r : ℕ) → Cat 𝕋 (a + (k + 1) * r) (a + r)
  | a, 0 => .affine (selectMat fun i => ⟨i.val, by simp⟩)
      fun _ => zero
  | a, r + 1 =>
    let split : Cat 𝕋 (a + (k + 1) * (r + 1)) (a + (k + 1) + (k + 1) * r) :=
      .affine (selectMat fun i => ⟨i.val, by have := i.isLt; rw [Nat.mul_succ]; omega⟩)
        fun _ => zero
    let first := Cat.maxSegment a k ((k + 1) * r)
    let rest := Cat.maxSegments k (a + 1) r
    let rename : Cat 𝕋 (a + 1 + r) (a + (r + 1)) :=
      .affine (selectMat fun i => ⟨i.val, by have := i.isLt; omega⟩) fun _ => zero
    .comp rename (.comp rest (.comp first split))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
