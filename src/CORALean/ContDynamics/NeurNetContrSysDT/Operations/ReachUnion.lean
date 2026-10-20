module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# `NeurNetContrSysDT.reach`, packaged as `Reach`'s `SetUnion`

The steps `0` through `K = tFinal - tStart` of `reach`, one per branch of the
`SetUnion` — the `Reach.reach` field of the instance, computable wherever `reach` is.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input set
* `params` – reachability parameters
* `options` – reachability options

## Output
* the reachable sets of all steps, as a union
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The steps `0` through `tFinal - tStart` of `reach`, from `R0`, one `SetUnion`
branch each. -/
def NeurNetContrSysDT.reachUnion (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (U_ext : S sys.nExt) (params : Reach.Params (S n) ℕ)
    (options : NeurNetContrSysDT.ReachOptions) : SetUnion (S n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let K := params.tFinal - params.tStart                           -- steps
  ⟨(List.range (K + 1)).map (fun k => sys.reach U_ext ⟨R₀, 0, k⟩ options)⟩  -- ⋃_{k ≤ K} R(k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
