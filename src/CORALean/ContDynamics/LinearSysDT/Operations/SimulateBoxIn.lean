module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# One interval-valued run of the dynamics

The float counterpart of `simulate`: a run of the step on boxes rather than on
points, so that the float step's rounding is carried (directed outward) instead of
silently lost. `simulateBoxIn` takes the start box and one input box per step;
`simulateBox` is the case CORA's `simulate` has, a float start and a float input
signal, each stored as a point interval.

The step is exactly `reach`'s, `A R ⊕ U`, at the float `Interval` class and
without `reduce` (a box has no order to give up); `simulate_mem_simulateBox` says
the real run lies in these boxes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Plus Mtimes CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The boxes `B_k` of a run from box `B₀` under input boxes `U k`:
`B_{k+1} = A B_k ⊕ U_k`, in float interval arithmetic. -/
def LinearSysDT.simulateBoxIn (sys : LinearSysDT 𝕋 n) (B₀ : Interval (Vec 𝕋 n))
    (U : ℕ → Interval (Vec 𝕋 n)) : ℕ → Interval (Vec 𝕋 n)
  | 0 => B₀
  | k + 1 =>
    plus (S := Interval (Vec 𝕋 n)) (mtimes (S := fun n => Interval (Vec 𝕋 n)) sys.A
      (sys.simulateBoxIn B₀ U k)) (U k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
