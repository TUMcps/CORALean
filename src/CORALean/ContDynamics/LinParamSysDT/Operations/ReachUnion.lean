module

public import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# `LinParamSysDT.reach`, packaged as `Reach`'s `SetUnion`

The steps `0` through `K = tFinal - tStart` of `reach`, one per branch of the
`SetUnion` — the `Reach.reach` field of the instance, computable wherever `reach`
is.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The steps `0` through `tFinal - tStart` of `reach`, from `R0` under inputs in
`U`, one `SetUnion` branch each. -/
def LinParamSysDT.reachUnion (sys : LinParamSysDT 𝕄 n)
    (params : Reach.InputParams (S n) (S n) ℕ) (options : LinParamSysDT.ReachOptions) :
    SetUnion (S n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let K := params.tFinal - params.tStart                           -- steps
  ⟨(List.range (K + 1)).map (fun k => sys.reach ⟨R₀, U, 0, k⟩ options)⟩  -- ⋃_{k ≤ K} R(k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
