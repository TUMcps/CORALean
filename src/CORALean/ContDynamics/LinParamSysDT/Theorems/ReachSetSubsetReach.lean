import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachSet
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOneOuter

/-!
# `reachSet` stays inside `reach`

`reach_outer_on`'s induction, off a represented set rather than off one
trajectory: each step's image at every `A ∈ construct sys.A`, plus every input in
`construct U`, is exactly what `reach_one_outer` already bounds.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Plus Reduce Mtimes

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.reachSet_subset_reach (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : S n) (k : ℕ) :
    sys.reachSet R₀ U k ⊆ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    rintro _ ⟨z, hz, w, hw, rfl⟩
    obtain ⟨A, hA, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hz
    show A *ᵥ y + w ∈ construct (sys.reach ⟨sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩, U, 0, 1⟩ ⟨o, ho⟩)
    exact sys.reach_one_outer ho _ _ hA (ih hy) hw

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
