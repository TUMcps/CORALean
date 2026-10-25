import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.HybridDynamics.Theorems.HoldsOfCheck
import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.Specification.Instances

/-!
# A hybrid automaton, at a floating-point representation

The automaton, its runs and its invariant are propositions over whatever the locations are
described in, the state's representation and the guard's alike, so they read at a float one with
nothing to add. `Transition.W` and `.w` read through `Scalar 𝕋` like `LinearSysDT.A`, so that half
is not what stops `Transition.jump` at a float representation. What stops it is `OfInterval`:
`jump` converts an exact real box, and no float representation has that instance, which would have
to round the box before an `InflatedContSet` error box exists to pay for it. `Transition.jumpFloat`
is the float route, `w` being stored floats already; `BouncingBallFloat` runs it.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


namespace CORALean.Float

open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r : ℕ} {L : Type}

example {HA : HybridAutomaton 𝒵[𝕋] 𝒵[𝕋] L 𝕋 n}
    {R : L → Zonotope (Vec 𝕋 n)}
    (hinv : HA.IsInvariant R) (spec : Specification (Set (Vec ℝ n))) {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.IsRun ℓ x ℓ' y) (hx : x ∈ construct (R ℓ))
    (h : spec.Holds (construct (R ℓ'))) : spec.Holds {y} :=
  HA.holds_of_invariant hinv spec run hx h

/-- The same, checked: the invariant at the location the run ends in, against a box. -/
example {HA : HybridAutomaton 𝒵[𝕋] 𝒵[𝕋] L 𝕋 n}
    {R : L → Zonotope (Vec 𝕋 n)}
    (hinv : HA.IsInvariant R) (spec : Specification (Interval (Vec 𝕋 n))) {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.IsRun ℓ x ℓ' y) (hx : x ∈ construct (R ℓ)) :
    spec.check (R ℓ') → (spec.Holds {y}) :=
  HybridAutomaton.holds_of_check hinv spec run hx

end CORALean.Float

