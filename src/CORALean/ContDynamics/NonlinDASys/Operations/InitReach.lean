module

public import CORALean.ContDynamics.NonlinDASys.Definitions.LinPoint
public import CORALean.ContDynamics.NonlinDASys.Operations.LinReach
public import CORALean.ContSet.Zonotope.Real.Operations.Split

@[expose] public section

/-!
# `NonlinDASys.initReach`

CORA's `nonlinDASys/initReach`: `linReach` on every start set, and where the step asks for a split
(`dimForSplit` non-empty), the start set halved along that generator by `split` and `initReach`
run again on the two halves. `lin` gives the linearization of a start set, and `select` the
generator to split along or `none`: CORA decides by its performance index `perfInd > 1` and picks
by `priv_select`, heuristics with no guarantee attached, so both are arguments. A fuel bounds the
recursion, which CORA's code does not. The consistent initial algebraic state enters through
`lin`'s `y*`; the error bookkeeping (`error_x`, `error_y`) is not carried.

## Inputs
* `sys` – system
* `lin` – linearization of a start set
* `select` – choice of the generator to split along
* `U` – input zonotope
* `Δt` – step size
* `η` – Taylor order

## Output
* the step sets of the start sets after splitting, by fuel and start list
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `linReach` of `Rinit` at its linearization `L`: one entry of `initReach`'s result. -/
noncomputable def NonlinDASys.aux_initReachLin (sys : NonlinDASys n p m)
    (L : NonlinDASys.LinPoint n p m) (U : Zonotope (Vec ℝ m)) (Δt : ℝ) (η : ℕ)
    (Rinit : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n × Vec ℝ p) :=
  NonlinDASys.linReach (sys.f L.xs L.ys L.us) (sys.g L.xs L.ys L.us) L.A L.B L.C L.D L.E
    L.F_inv L.xs L.ys L.us Rinit U L.Verror L.Verror_y Δt η


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `initReach` for a DAE: `linReach` on each start set in `Rstart`, the sets `select`
picks a generator of split and done again, `fuel` levels deep. -/
noncomputable def NonlinDASys.initReach (sys : NonlinDASys n p m)
    (lin : Zonotope (Vec ℝ n) → NonlinDASys.LinPoint n p m)
    (select : (Z : Zonotope (Vec ℝ n)) → Option (Fin Z.h)) (U : Zonotope (Vec ℝ m)) (Δt : ℝ)
    (η : ℕ) : ℕ → List (Zonotope (Vec ℝ n)) →
      List (Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n × Vec ℝ p))
  | 0, Rstart => Rstart.map fun Rinit =>                                  -- no split left
    sys.aux_initReachLin (lin Rinit) U Δt η Rinit                         -- linReach
  | fuel + 1, Rstart => Rstart.flatMap fun Rinit =>
    match select Rinit with                                               -- dimForSplit
    | some j =>
      let Rsplit := Rinit.split j                                         -- split
      sys.initReach lin select U Δt η fuel [Rsplit.fst, Rsplit.snd]           -- initReach
    | none => [sys.aux_initReachLin (lin Rinit) U Δt η Rinit]             -- linReach

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
