module

public import CORALean.ContSet.HPolytope.Real.Operations.BilliardStep
public import CORALean.ContSet.HPolytope.Real.Theorems.BilliardEndMem

@[expose] public section

/-!
# A step of the Billiard Walk stays in the polytope

`[1, Thm. 1]` and `[1, Thm. 2]` are about a chain `x₀, x₁, …` in `Q`, produced by the steps 2-5 of
`[1, Alg.]`; each `x_{i+1}` that `HPolytope.billiardStep` returns satisfies every inequality, for
any `R`, any `τ ≥ 0`, any `η ∈ (0, 1]` and any direction. The step starts in the open polytope;
the point it returns can lie on the boundary only if `ℓ` equals a segment length exactly, which
the uniform draw of `η` hits with probability zero.

## Inputs
* `P` – H-polytope
* `R` – natural number
* `τ` – real number
* `x` – point
* `η` – real number
* `ξ` – space

## Hypotheses
* `hx` – `x` is strictly inside every inequality
* `hτ` – `0 ≤ τ`
* `hη₀` – `0 < η`
* `hη₁` – `η ≤ 1`

## Conclusion
* A step of the Billiard Walk stays in the polytope

## References

* [1] [B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control and
      optimization". IFAC Proceedings Volumes,
      2014.](../../../../../../references/2014/polyak-ifac-billiard-walk.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.billiardStep_mem (P : HPolytope E) (R : ℕ) (τ : ℝ) (x : E) (η : ℝ) (ξ : E)
    (hx : ∀ i, P.A i x < P.b i) (hτ : 0 ≤ τ) (hη₀ : 0 < η) (hη₁ : η ≤ 1) : -- --- CONCL ---
    ∀ y ∈ P.billiardStep R τ x η ξ,
      ∀ i, P.A i y ≤ P.b i := by -- --- PROOF ---
  intro y (hy : P.billiardStep R τ x η ξ = some y)
  -- the length is nonnegative: `log η ≤ 0`
  have hℓ : 0 ≤ -τ * Real.log η := by
    have := Real.log_nonpos hη₀.le hη₁
    nlinarith
  exact HPolytope.billiardEnd_mem P R x _ _ hx hℓ y hy

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
