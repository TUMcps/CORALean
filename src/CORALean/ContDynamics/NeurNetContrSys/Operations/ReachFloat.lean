module

public import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachOptions
public import CORALean.ContDynamics.NeurNetContrSys.Operations.AugmentFloat
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachWith
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.ContSet.Zonotope.Float.Operations.CartProd
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.Project

@[expose] public section

/-!
# A neural-network-controlled linear plant, reached in floats

`NeurNetContrSys.reach` computed in `𝕋`, at float zonotopes: each control period stacks the
network's image under the period's initial set (`Zonotope.cartProd`), runs `N` steps of the
augmented system `[A B_nn; 0 0]`, `[B_ext; 0]`, `[c; 0]` (`augmentFloat`) sampled by
`discretizeEnclosureFloat` under `inputSolutionFloat` of `B_aug U_ext ⊕ [c; 0]`, the external
inputs `U_ext` entering as in `reach`, and projects back (`Zonotope.project`) — the
exact `discretize` and `inputSolution` replaced by their float enclosures. The order `η` is the
caller's; `reachFloat_outer` asks it to be admissible for the augmented matrix. It is
[1, Alg. 2] at a linear plant.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input zonotope
* `params` – reachability parameters
* `options` – reachability options

## Output
* the float reachable set at the end of the last control period

## References

* [1] N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at the end of `params.tFinal - params.tStart` control periods, each
`options.N` float steps of `options.Δt` of the augmented system, under the external inputs
`U_ext`. -/
def NeurNetContrSys.reachFloat (sys : NeurNetContrSys (LinearSys 𝕋 n) 𝒵[𝕋] n)
    (U_ext : Zonotope (Vec 𝕋 sys.nExt)) (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℕ)
    (options : NeurNetContrSys.ReachOptions 𝕋) :
    Zonotope (Vec 𝕋 n) :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let N := options.N
  let η := options.η
  let o := options.ρ
  let H := params.tFinal - params.tStart                           -- control periods
  let ext := sys.augmentFloat                                       -- [A B_nn; 0 0], [B_ext; 0]
  let U : Zonotope (Vec 𝕋 (n + sys.m)) :=                           -- B_aug U_ext ⊕ [c; 0]
    Plus.plus (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) ext.B U_ext) (Zonotope.point ext.c)
  let cp := fun (X : Zonotope (Vec 𝕋 n)) (Y : Zonotope (Vec 𝕋 sys.m)) =>
    X.cartProd Y                                                    -- R × Y
  let pr := fun (Z : Zonotope (Vec 𝕋 (n + sys.m))) =>
    Z.project (Fin.castAdd sys.m)                             -- the first n coordinates
  let rx := fun Z =>                                                -- N steps of ext from Z
    ((ext.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])
      ⟨Z, ext.inputSolutionFloat Δt η U, 0, N⟩ ⟨o, options.hZonotopeOrder⟩,
      [])
  (sys.reachWith cp pr rx R₀ H).1                                   -- R(HNΔt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
