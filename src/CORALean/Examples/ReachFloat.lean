import CORALean.ContDynamics.LinearSysDT.Operations.CanonicalFloat
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfCheck
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfOutput
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Specification.Instances

/-!
# Reachability at a floating-point representation

Every declaration below is `:=` and nothing else, and that is the claim: the discrete-time
algorithms need no float counterpart, naming no scalar operation of their own. `LinearSysDT.reach`
is written against `Scalar 𝕋` and the operation classes, so a float representation supplies it as
an exact one does. `ReachClosedLoopFloat` and `ReachHybridFloat` do the same for a controller in
the loop and for a hybrid automaton. An algorithm needs a float counterpart precisely where it
computes a real number that is no set operation, as `LinearSys.discretize` is `exp (Δt • A)` and
asks for `Mtimes (Mat ℝ) S`, which no float representation can have; those have their own
`reachFloat`.

## Inputs
* `sys` – discrete-time system
* `o` – zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step count

## Hypotheses
* `ho` – zonotope order positive

## Output
* float reach set after the steps
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r : ℕ} {L : Type}

/-! ## A discrete-time linear system

CORA's `linearSysDT` is given in discrete time to begin with, so its matrix is
stored data and a float one denotes the affine map exactly, as a linear layer's
weights do. -/


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set after `k` steps, at a float zonotope. Everything it calls —
`mtimes`, `plus`, `reduce` — is the float representation's own. -/
def Example.reachZonotopeFloat (sys : LinearSysDT 𝕋 n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 n) :=
  sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩

/-- The same at a float box, where `reduce` is the identity. -/
def Example.reachIntervalFloat (sys : LinearSysDT 𝕋 n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Interval (Vec 𝕋 n)) (k : ℕ) : Interval (Vec 𝕋 n) :=
  sys.reach (S := ℐ𝒱[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩

-- Anonymous, since their content is that they elaborate.

/-- Every run of the system is enclosed, by the exact layer's theorem read at a
float representation. -/
example (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n))
    {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory (S := 𝒵[𝕋]) R₀ U
    x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer (S := 𝒵[𝕋]) ho R₀ U traj k

/-- One step, which is what a closed loop needs and `reach_outer` cannot give. -/
example (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R U : Zonotope (Vec 𝕋 n)) {x u : Vec ℝ n}
    (hx : x ∈ construct R) (hu : u ∈ construct U) :
    Scalar.toRealMat sys.A *ᵥ x + u ∈
      construct (sys.reach (S := 𝒵[𝕋]) ⟨R, U, 0, 1⟩ ⟨o, ho⟩) :=
  sys.reach_one_outer (S := 𝒵[𝕋]) ho R U hx hu

/-- A specification checked on the computed set answers for the state. -/
example (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n))
    (spec : Specification (Set (Vec ℝ n))) {x u : ℕ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (S := 𝒵[𝕋]) R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct
    (sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩))) :
    spec.Holds {x k} :=
  sys.holds_of_reach (S := 𝒵[𝕋]) ho R₀ U spec traj k h

/-- The same with nothing left to prove by hand: a halfspace description checked on the
computed zonotope by `Specification.check`, which runs. -/
example (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n))
    (spec : Specification (HPolytope 𝕋 (Vec 𝕋 n))) {x u : ℕ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (S := 𝒵[𝕋]) R₀ U x u) (k : ℕ) :
    spec.check (sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) →
    (spec.Holds {x k}) :=
  sys.holds_of_check (S := 𝒵[𝕋]) ho R₀ U spec traj k

/-! ## An output equation

`OutputEq` names no scalar operation of its own either — two `mtimes` and one
`plus` — so the output set is the same definition here as at an exact
representation, and its matrices are stored floats like the plant's. -/

/-- The output set at step `k`, at a float zonotope. The output dimension `r` is
free of the state dimension, which is what an output is for. -/
def Example.outputZonotopeFloat (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r)
    (o : ℕ) (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 r) :=
  out.outputSet (S := 𝒵[𝕋])
    (sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) U

/-- A specification checked on the output set answers for the output — the one
question this repository could not ask before. -/
example (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec 𝕋 n)) (spec : Specification (Set (Vec ℝ r))) {x u : ℕ → Vec ℝ n}
    (traj : sys.IsCanonicalTrajectory (S := 𝒵[𝕋]) R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct
      (out.outputSet (S := 𝒵[𝕋])
        (sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) U))) :
    spec.Holds {out.eval (x k) (u k)} :=
  sys.holds_of_output (S := 𝒵[𝕋]) out ho R₀ U spec traj k h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
