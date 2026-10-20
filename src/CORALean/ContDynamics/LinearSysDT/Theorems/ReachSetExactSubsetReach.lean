module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSetExact
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter

@[expose] public section

/-!
# `reach` encloses the set the dynamics reach

`reach_outer` says the algorithm holds every trajectory; this says it holds the
whole exact set at once, which is the same three class guarantees applied to a
set rather than to a point — `reach_one_outer` is that step, reused verbatim.

What it buys: a bound obtained on `reach` by asking the representation, and a
bound obtained on `reachSetExact` by propagation, are bounds on nested sets, so the
tighter of the two is available at every step without either being trusted.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial set
* `U` – input set
* `k` – step

## Hypotheses
* `ho` – order positive

## Conclusion
* the exact reachable set lies in the computed one
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reachSetExact_subset_reach (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : S n) (k : ℕ) :
    sys.reachSetExact R₀ U k ⊆ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    rintro _ ⟨_, ⟨y, hy, rfl⟩, w, hw, rfl⟩
    show toRealMat sys.A *ᵥ y + w ∈
      construct (sys.reach ⟨sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩, U, 0, 1⟩ ⟨o, ho⟩)
    exact sys.reach_one_outer ho _ _ (ih hy) hw

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
