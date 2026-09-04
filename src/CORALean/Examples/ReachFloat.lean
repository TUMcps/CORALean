import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfOutput
import CORALean.ContDynamics.LinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.ReLU

/-!
# Reachability at a floating-point representation

Every declaration below is `:=` and nothing else, and that is the claim: the
discrete-time algorithms need no float counterpart, naming no scalar operation of
their own. `LinearSysDT.reach`, `NeurNetContrSysDT.reach` and the whole hybrid
automaton are written against `Scalar 𝕋` and the operation classes, so a float
representation supplies them the same way an exact one does.

The `def`s are `def` rather than `noncomputable def`, which is the second half of
the claim: the exact versions are unusable because `Real.Zonotope`'s operations
do not run.

An algorithm needs a float counterpart precisely where it computes a *real number
that is no set operation*, only a set operation having an error box to pay its
rounding into. In `ContDynamics` that is `MatExp/Enclosures.lean` and what
depends on it: `LinearSys.discretize` is `exp (Δt • A)` and asks for
`Mtimes (Mat ℝ) S`, which no float representation can have, and the four step
operations ask for `Mtimes ℐ S` at the *exact* interval-matrix family.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r : ℕ} {L : Type}

/-! ## A discrete-time linear system

CORA's `linearSysDT` is given in discrete time to begin with, so its matrix is
stored data and a float one denotes the affine map exactly, as a linear layer's
weights do. -/

/-- The reachable set after `k` steps, at a float zonotope. Everything it calls —
`mtimes`, `plus`, `reduce` — is the float representation's own. -/
def Example.reachZonotopeFloat (sys : Real.LinearSysDT 𝕋 n) (o : ℕ)
    (R₀ U : Zonotope 𝕋 n) (k : ℕ) : Zonotope 𝕋 n :=
  sys.reach (S := Zonotope 𝕋) o R₀ U k

/-- The same at a float box, where `reduce` is the identity. -/
def Example.reachIntervalFloat (sys : Real.LinearSysDT 𝕋 n) (o : ℕ)
    (R₀ U : Interval 𝕋 n) (k : ℕ) : Interval 𝕋 n :=
  sys.reach (S := Interval 𝕋) o R₀ U k

-- Anonymous, since their content is that they elaborate.

/-- Every run of the system is enclosed, by the exact layer's theorem read at a
float representation. -/
example (sys : Real.LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : Zonotope 𝕋 n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory (S := Zonotope 𝕋) R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach (S := Zonotope 𝕋) o R₀ U k) :=
  sys.reach_outer o R₀ U traj k

/-- One step, which is what a closed loop needs and `reach_outer` cannot give. -/
example (sys : Real.LinearSysDT 𝕋 n) (o : ℕ) (R U : Zonotope 𝕋 n) {x u : Vec ℝ n}
    (hx : x ∈ construct R) (hu : u ∈ construct U) :
    Scalar.toRealMat sys.A *ᵥ x + u ∈ construct (sys.reach (S := Zonotope 𝕋) o R U 1) :=
  sys.reach_one_outer o R U hx hu

/-- A specification checked on the computed set answers for the state. -/
example (sys : Real.LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : Zonotope 𝕋 n)
    (spec : Specification (Vec ℝ n)) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory (S := Zonotope 𝕋) R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (sys.reach (S := Zonotope 𝕋) o R₀ U k))) :
    spec.Holds {x k} :=
  sys.holds_of_reach o R₀ U spec traj k h

/-! ## An output equation

`OutputEq` names no scalar operation of its own either — two `mtimes` and one
`plus` — so the output set is the same definition here as at an exact
representation, and its matrices are stored floats like the plant's. -/

/-- The output set at step `k`, at a float zonotope. The output dimension `r` is
free of the state dimension, which is what an output is for. -/
def Example.outputZonotopeFloat (sys : Real.LinearSysDT 𝕋 n) (out : Real.OutputEq 𝕋 n n r)
    (o : ℕ) (R₀ U : Zonotope 𝕋 n) (k : ℕ) : Zonotope 𝕋 r :=
  out.outputSet (sys.reach (S := Zonotope 𝕋) o R₀ U k) U

/-- A specification checked on the output set answers for the output — the one
question this repository could not ask before. -/
example (sys : Real.LinearSysDT 𝕋 n) (out : Real.OutputEq 𝕋 n n r) (o : ℕ)
    (R₀ U : Zonotope 𝕋 n) (spec : Specification (Vec ℝ r)) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory (S := Zonotope 𝕋) R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct
      (out.outputSet (sys.reach (S := Zonotope 𝕋) o R₀ U k) U))) :
    spec.Holds {out.eval (x k) (u k)} :=
  sys.holds_of_output out o R₀ U spec traj k h

/-! ## A network controlling a discrete plant

Both halves are float here — the plant's matrix and the controller's weights —
and neither the system type nor `reach` notices. -/

/-- Affine, ReLU, affine, in the loop with a two-state plant. -/
def Example.closedLoopFloat (A : Mat 𝕋 2 2) (W₁ : Mat 𝕋 3 2) (b₁ : Vec 𝕋 3)
    (W₂ : Mat 𝕋 2 3) (b₂ : Vec 𝕋 2) : Real.NeurNetContrSysDT 𝕋 (Zonotope 𝕋) 2 :=
  ⟨⟨A⟩, .cons (Layer.linear (S := Zonotope 𝕋) W₁ b₁)
    (.cons Layer.relu (.cons (Layer.linear W₂ b₂) .nil))⟩

def Example.reachClosedLoopFloat (sys : Real.NeurNetContrSysDT 𝕋 (Zonotope 𝕋) n)
    (o : ℕ) (R₀ : Zonotope 𝕋 n) (k : ℕ) : Zonotope 𝕋 n :=
  sys.reach o R₀ k

example (sys : Real.NeurNetContrSysDT 𝕋 (Zonotope 𝕋) n) (o : ℕ) (R₀ : Zonotope 𝕋 n)
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ x) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ k) :=
  sys.reach_outer o R₀ traj k

/-! ## A hybrid automaton

The automaton, its runs and its invariant are propositions over whatever the
locations are described in, so they read at a float representation with nothing
to add. Only `Transition.jump`, which computes, does not — and for the reason
the module docstring gives. -/

example {HA : Real.HybridAutomaton (Zonotope 𝕋) L 𝕋 n} {R : L → Zonotope 𝕋 n}
    (hinv : HA.Invariant R) (spec : Specification (Vec ℝ n)) {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.Run ℓ x ℓ' y) (hx : x ∈ construct (R ℓ))
    (h : spec.Holds (construct (R ℓ'))) : spec.Holds {y} :=
  HA.holds_of_invariant hinv spec run hx h

end CORALean.Float
