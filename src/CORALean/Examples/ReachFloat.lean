import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfCheck
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfOutput
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.HoldsOfCheck
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.HybridDynamics.Theorems.HoldsOfCheck
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.Basic
import CORALean.NN.Layers.Operations.ReluSlope
import CORALean.Specification.Instances

/-!
# Reachability at a floating-point representation

Every declaration below is `:=` and nothing else, and that is the claim: the
discrete-time algorithms need no float counterpart, naming no scalar operation of
their own. `LinearSysDT.reach`, `NeurNetContrSysDT.reach` and the whole hybrid
automaton are written against `Scalar 𝕋` and the operation classes, so a float
representation supplies them the same way an exact one does.

The `def`s below are `def` rather than `noncomputable def`, as are `Sigmoid`,
`Tanh`, `Softmax`, `maxPool` and `SigmoidPoly`: `Layer` stores no function.

An algorithm needs a float counterpart precisely where it computes a *real number
that is no set operation*, only a set operation having an error box to pay its
rounding into. In `ContDynamics` that is `MatExp/Enclosures.lean` and what
depends on it: `LinearSys.discretize` is `exp (Δt • A)` and asks for
`Mtimes (Mat ℝ) S`, which no float representation can have, and the four step
operations ask for `Mtimes ℐ S` at the *exact* interval-matrix family. Those
have their own `reachFloat` (`LinearSys`, `NonlinearSys`, ...), not read off here.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r : ℕ} {L : Type}

/-! ## A discrete-time linear system

CORA's `linearSysDT` is given in discrete time to begin with, so its matrix is
stored data and a float one denotes the affine map exactly, as a linear layer's
weights do. -/

/-- The reachable set after `k` steps, at a float zonotope. Everything it calls —
`mtimes`, `plus`, `reduce` — is the float representation's own. -/
def Example.reachZonotopeFloat (sys : LinearSysDT 𝕋 n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 n) :=
  sys.reach (S := fun k => Zonotope (Vec 𝕋 k)) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩

/-- The same at a float box, where `reduce` is the identity. -/
def Example.reachIntervalFloat (sys : LinearSysDT 𝕋 n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Interval (Vec 𝕋 n)) (k : ℕ) : Interval (Vec 𝕋 n) :=
  sys.reach (S := fun n => Interval (Vec 𝕋 n)) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩

-- Anonymous, since their content is that they elaborate.

/-- Every run of the system is enclosed, by the exact layer's theorem read at a
float representation. -/
example (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n))
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory (S := fun k => Zonotope (Vec 𝕋 k)) R₀ U
    x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := fun k => Zonotope (Vec 𝕋 k)) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer (S := fun k => Zonotope (Vec 𝕋 k)) ho R₀ U traj k

/-- One step, which is what a closed loop needs and `reach_outer` cannot give. -/
example (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R U : Zonotope (Vec 𝕋 n)) {x u : Vec ℝ n}
    (hx : x ∈ construct R) (hu : u ∈ construct U) :
    Scalar.toRealMat sys.A *ᵥ x + u ∈
      construct (sys.reach (S := fun k => Zonotope (Vec 𝕋 k)) ⟨R, U, 0, 1⟩ ⟨o, ho⟩) :=
  sys.reach_one_outer (S := fun k => Zonotope (Vec 𝕋 k)) ho R U hx hu

/-- A specification checked on the computed set answers for the state. -/
example (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n))
    (spec : Specification (Set (Vec ℝ n))) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory (S := fun k => Zonotope (Vec 𝕋 k)) R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct
    (sys.reach (S := fun k => Zonotope (Vec 𝕋 k)) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩))) :
    spec.Holds {x k} :=
  sys.holds_of_reach (S := fun k => Zonotope (Vec 𝕋 k)) ho R₀ U spec traj k h

/-- The same with nothing left to prove by hand: a halfspace description checked on the
computed zonotope by `Specification.check`, which runs. -/
example (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n))
    (spec : Specification (HPolytope 𝕋 (Vec 𝕋 n))) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory (S := fun k => Zonotope (Vec 𝕋 k)) R₀ U x u) (k : ℕ) :
    spec.check (sys.reach (S := fun k => Zonotope (Vec 𝕋 k)) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) →
    (spec.Holds {x k}) :=
  sys.holds_of_check (S := fun k => Zonotope (Vec 𝕋 k)) ho R₀ U spec traj k

/-! ## An output equation

`OutputEq` names no scalar operation of its own either — two `mtimes` and one
`plus` — so the output set is the same definition here as at an exact
representation, and its matrices are stored floats like the plant's. -/

/-- The output set at step `k`, at a float zonotope. The output dimension `r` is
free of the state dimension, which is what an output is for. -/
def Example.outputZonotopeFloat (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r)
    (o : ℕ) (ho : 0 < o) (R₀ U : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 r) :=
  out.outputSet (S := fun k => Zonotope (Vec 𝕋 k))
    (sys.reach (S := fun k => Zonotope (Vec 𝕋 k)) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) U

/-- A specification checked on the output set answers for the output — the one
question this repository could not ask before. -/
example (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec 𝕋 n)) (spec : Specification (Set (Vec ℝ r))) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory (S := fun k => Zonotope (Vec 𝕋 k)) R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct
      (out.outputSet (S := fun k => Zonotope (Vec 𝕋 k))
        (sys.reach (S := fun k => Zonotope (Vec 𝕋 k)) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) U))) :
    spec.Holds {out.eval (x k) (u k)} :=
  sys.holds_of_output (S := fun k => Zonotope (Vec 𝕋 k)) out ho R₀ U spec traj k h

/-! ## A network controlling a discrete plant

Both halves are float here — the plant's matrix and the controller's weights —
and neither the system type nor `reach` notices. -/

/-- Affine, ReLU, affine, in the loop with a two-state plant. -/
def Example.closedLoopFloat (A : Mat 𝕋 2 2) (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3)
    (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2) : NeurNetContrSysDT 𝕋 (fun k => Zonotope (Vec 𝕋 k)) 2 :=
  ⟨⟨A⟩, .layer (LinearLayer.mk W₁ b₁)
    (.layer (ReluLayer.mk (𝕋 := 𝕋) reluSlope rfl) (.layer (LinearLayer.mk W₂ b₂) .output))⟩


-- =====================================  MAIN DEFINITION  ====================================== --

def Example.reachClosedLoopFloat (sys : NeurNetContrSysDT 𝕋 (fun k => Zonotope (Vec 𝕋 k)) n)
    (o : ℕ) (ho : 0 < o) (R₀ : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 n) :=
  sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩

example (sys : NeurNetContrSysDT 𝕋 (fun k => Zonotope (Vec 𝕋 k)) n) {o : ℕ} (ho : 0 < o)
    (R₀ : Zonotope (Vec 𝕋 n)) {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory π R₀ x) (k : ℕ) :
    x k ∈ construct (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer (S := fun k => Zonotope (Vec 𝕋 k)) ho R₀ hπ traj k

/-- A box safe set checked on the closed loop's computed zonotope. -/
example (sys : NeurNetContrSysDT 𝕋 (fun k => Zonotope (Vec 𝕋 k)) n) {o : ℕ} (ho : 0 < o)
    (R₀ : Zonotope (Vec 𝕋 n)) (spec : Specification (Interval (Vec 𝕋 n))) {π : Vec ℝ n → Vec ℝ n}
    (hπ : sys.contr.Sound π) {x : ℕ → Vec ℝ n} (traj : sys.Trajectory π R₀ x) (k : ℕ) :
    spec.check (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩) → (spec.Holds {x k}) :=
  sys.holds_of_check (S := fun k => Zonotope (Vec 𝕋 k)) ho R₀ spec hπ traj k

/-! ## A hybrid automaton

The automaton, its runs and its invariant are propositions over whatever the
locations are described in — the state's representation and the guard's alike,
those being separate parameters — so they read at a float one with nothing to
add. `Transition.W` and `.w` read through `Scalar 𝕋` like `LinearSysDT.A`,
so that half is not what stops `Transition.jump` at a float representation.
What stops it is `OfInterval`: `jump` calls `CORALean.Real`'s, converting an
*exact* real box, and no float representation has that instance — one would have
to round the box into the representation's own floats before an `InflatedContSet`
error box exists to pay that rounding into, which is exactly what
`CORALean.Float.OfInterval` is for instead. `Transition.jumpFloat` is the float
route, `w` being stored floats already; `BouncingBallFloat` runs it. -/

example {HA : HybridAutomaton (fun k => Zonotope (Vec 𝕋 k)) (fun k => Zonotope (Vec 𝕋 k)) L 𝕋 n}
    {R : L → Zonotope (Vec 𝕋 n)}
    (hinv : HA.Invariant R) (spec : Specification (Set (Vec ℝ n))) {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.Run ℓ x ℓ' y) (hx : x ∈ construct (R ℓ))
    (h : spec.Holds (construct (R ℓ'))) : spec.Holds {y} :=
  HA.holds_of_invariant hinv spec run hx h

/-- The same, checked: the invariant at the location the run ends in, against a box. -/
example {HA : HybridAutomaton (fun k => Zonotope (Vec 𝕋 k)) (fun k => Zonotope (Vec 𝕋 k)) L 𝕋 n}
    {R : L → Zonotope (Vec 𝕋 n)}
    (hinv : HA.Invariant R) (spec : Specification (Interval (Vec 𝕋 n))) {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.Run ℓ x ℓ' y) (hx : x ∈ construct (R ℓ)) :
    spec.check (R ℓ') → (spec.Holds {y}) :=
  HybridAutomaton.holds_of_check hinv spec run hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
