module

public import CORALean.ContDynamics.NonlinearSys.Operations.InterpGainFloat
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `estimateGain`: the gain at the finite horizon, in floats

`estimateGain` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no
soundness statement reads it, so every rounding is upward and no theorem is owed. What a run
guarantees holds for whatever this returns. See [1].

## Inputs
* `ζδ` – tuning constant
* `lam` – step scaling
* `rabs1` – abstraction radius at the horizon
* `rabsOpt` – abstraction radius at the optimal step
* `scalings` – number of scalings
* `fuel` – number of halvings

## Output
* the float gain at the finite horizon

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Halve the bracket toward where `g` crosses `target`, `fuel` times, and hand
back the last midpoint. -/
def aux_estimateGainSearchFloat (g : 𝕋 → 𝕋) (target : 𝕋) : 𝕋 → 𝕋 → ℕ → 𝕋
  | lo, hi, 0 => half (addUp lo hi)
  | lo, hi, k + 1 =>
    let mid := half (addUp lo hi)
    if le (g mid) target then aux_estimateGainSearchFloat g target mid hi k
    else aux_estimateGainSearchFloat g target lo mid k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 16: the gain `φ⁽¹⁾` eq. (56) fixes, at the `λ'` the step
size search settled on. -/
def estimateGainFloat (ζδ lam rabs1 rabsOpt : 𝕋) (scalings fuel : ℕ) : 𝕋 :=
  -- 16. eq. (56): the right-hand side
  let target := divUp (mulUp lam rabsOpt) rabs1
  -- 16. eq. (56): the left-hand side
  let lhs := fun φ1 => (List.range scalings).foldl
    (fun p j => mulUp p (interpGainFloat ζδ φ1 j)) one
  -- 16. eq. (56): solve for φ⁽¹⁾ in [0,1]
  aux_estimateGainSearchFloat lhs target zero one fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
