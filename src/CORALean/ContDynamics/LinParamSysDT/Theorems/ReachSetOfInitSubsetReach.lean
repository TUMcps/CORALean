import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachParams
import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachSetOfInit
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOneOuter

/-!
# `reachSetOfInit` at `construct R₀` stays inside `reach`

`reach_outer_on`'s induction, off a bare set rather than off one trajectory:
each step's image at every `A ∈ construct sys.sys.A`, plus every input in
`construct sys.U`, is exactly what `reach_one_outer` already bounds.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Plus Reduce Mtimes

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.WithInput.reachSetOfInit_subset_reach (sys : LinParamSysDT.WithInput 𝕄 S n)
    (p : LinParamSysDT.ReachParams) (R₀ : S n) (k : ℕ) :
    sys.reachSetOfInit (construct R₀) k
      ⊆ construct (sys.sys.reach p.o p.ho R₀ sys.U k) := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    rintro _ ⟨z, hz, w, hw, rfl⟩
    obtain ⟨A, hA, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hz
    show A *ᵥ y + w ∈
      construct (sys.sys.reach p.o p.ho (sys.sys.reach p.o p.ho R₀ sys.U k) sys.U 1)
    exact sys.sys.reach_one_outer p.ho _ _ hA (ih hy) hw

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
