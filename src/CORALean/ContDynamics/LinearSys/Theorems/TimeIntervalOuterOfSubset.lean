module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterAt

@[expose] public section

/-!
# `timeInterval` encloses the exact reachable set of the step, for any enclosing end set

`timeInterval_outer_at`, quantified over the step's own time domain
`[0, Δt]` in one statement, through `reachExact`, and at the Taylor order `η`
itself rather than the `m + 2` it is admissible written as:
`reachExact Δt (toSet Xₖ)` is exactly the union over `t ∈ [0, Δt]` of the
image of `toSet Xₖ` under `exp (t • A)`, so unpacking one `t` and its
bounds from membership, and `η`'s own `m + 2` witness from `2 ≤ η`, is all
this adds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {ContSet : ℕ → Type} [∀ n, ContSetLike (ContSet n) (Vec ℝ n)]
variable [∀ n, Plus (ContSet n) (Vec ℝ n)] [∀ n, LinComb (ContSet n) (Vec ℝ n)]
variable [∀ n, Reduce (ContSet n) (Vec ℝ n)] [Mtimes (Mat ℝ) ContSet]
variable [Mtimes ℐ ContSet]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Reduce (ContSet n) (Vec ℝ n)] [Mtimes (Mat ℝ) ContSet] in
/-- The exact reachable set of the step, `reachExact Δt`, is inside
`timeInterval`'s, at the order `η` itself, for any `Xₖ₁` holding the image of `Xₖ`;
`timeInterval_outer` is this at `timePoint Δt Xₖ 1`. -/
theorem LinearSys.timeInterval_outer_of_subset (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) {η : ℕ}
    (hη : 2 ≤ η) (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (Xₖ Xₖ₁ : ContSet n)
    (hX : sys.reachExactAt Δt (toSet Xₖ) ⊆ toSet Xₖ₁) : -- --- CONCL ---
    sys.reachExact Δt (toSet Xₖ)
      ⊆ toSet (sys.timeInterval Δt η Xₖ Xₖ₁) := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ : ∃ m, η = m + 2 := ⟨η - 2, by omega⟩
  intro y hy
  obtain ⟨t, ⟨ht0, htr⟩, x₀, hx₀, rfl⟩ := Set.mem_iUnion₂.mp hy
  exact sys.timeInterval_outer_at hΔt hε Xₖ Xₖ₁ hX ht0 htr (Set.mem_image_of_mem _ hx₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
