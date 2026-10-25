module

public import CORALean.HybridDynamics.Definitions.IsInvariant
public import CORALean.HybridDynamics.Theorems.FlowOuterInputSolution
public import CORALean.HybridDynamics.Theorems.JumpIntersectionOuter

@[expose] public section

/-!
# `IsInvariant`, discharged from the computed enclosures

`IsInvariant.jump` falls out of `JumpIntersectionOuter` at `hjump`, one enclosure per transition
met. `IsInvariant.flow` quantifies over every dwell time and admissible input;
`FlowOuterInputSolution` discharges `u` structurally from `hconv`/`hclosed`/`hbdd`/`h0`. Two prices,
which `InvariantOfEnclosureCut` does not pay: `h0` asks the input set to hold the origin, which a
constant drift such as gravity breaks; and `hflow` asks one `R` to absorb the enclosure at every
dwell time, which under a nonzero drift grows without bound. `jumpIntersection` is
`Intersection.intersection` on the guard, so the guard is in the state's own family (#39).

## Inputs
* `HA` – hybrid automaton with guards in the state family
* `R` – reach set

## Hypotheses
* `hconv` – every input set convex
* `hclosed` – every input set closed
* `hbdd` – every input set bounded
* `h0` – every input set contains the origin
* `hflow` – every dwell time is enclosed by the sets
* `hjump` – every jump is enclosed by the sets

## Conclusion
* the sets are an invariant of the automaton
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Mtimes (Mat 𝕋) S] [OfInterval S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The set `hflow`'s remainder-side hypotheses are asked of: `τ`'s remainder
bound against the location's own input set. -/
noncomputable def aux_remainder [∀ n, OfPoint (S n) (Vec ℝ n)] (ℓ : Location S G L 𝕋 n) (τ : ℝ)
    (m : ℕ) : S n :=
  Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.inputSet


-- =======================================  MAIN THEOREM  ======================================= --

/-- `IsInvariant.jump` is `JumpIntersectionOuter` at `hjump`; `IsInvariant.flow` is
`FlowOuterInputSolution` at `hflow`, an order `m` chosen per dwell time `τ`
since `hε` cannot hold at one order for every one of them. -/
theorem HybridAutomaton.invariant_of_enclosure [∀ n, Intersection (S n) (Vec ℝ n)]
    [∀ n, OfPoint (S n) (Vec ℝ n)]
    (HA : HybridAutomaton S S L 𝕋 n) (R : L → S n)
    (hconv : ∀ ℓ : L, Convex ℝ (construct (HA.loc ℓ).inputSet))
    (hclosed : ∀ ℓ : L, IsClosed (construct (HA.loc ℓ).inputSet))
    (hbdd : ∀ ℓ : L, Bornology.IsBounded (construct (HA.loc ℓ).inputSet))
    (h0 : ∀ ℓ : L, (0 : Vec ℝ n) ∈ construct (HA.loc ℓ).inputSet)
    (hflow : ∀ (ℓ : L) (τ : ℝ), 0 < τ → ∃ m : ℕ,
      ‖τ • toRealMat (HA.loc ℓ).dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 ∧
      Convex ℝ (construct (aux_remainder (HA.loc ℓ) τ m)) ∧
      IsClosed (construct (aux_remainder (HA.loc ℓ) τ m)) ∧
      Bornology.IsBounded (construct (aux_remainder (HA.loc ℓ) τ m)) ∧
      construct (Plus.plus ((HA.loc ℓ).timeInterval τ (m + 2) (R ℓ))
        ((HA.loc ℓ).dynamics.inputSolution τ (m + 2) (HA.loc ℓ).inputSet)) ⊆ construct (R ℓ))
    (hjump : ∀ (ℓ : L) (e : Transition S L 𝕋 n), e ∈ (HA.loc ℓ).trans →
      construct (e.jumpIntersection (R ℓ)) ⊆ construct (R e.target)) :
    HA.IsInvariant R where
  flow {ℓ τ x u w} h h₀ {t} ht := by
    rcases h.nonneg.lt_or_eq with hτ | hτ0
    · -- `τ > 0`: `hflow`'s own order `m` both bounds the truncation and makes
      -- the remainder well-behaved, and its last conjunct finishes the goal
      obtain ⟨m, hε, hRconv, hRclosed, hRbdd, hsub⟩ := hflow ℓ τ hτ
      exact hsub (h.timeInterval_outer_inputSolution h₀ hτ hε (hconv ℓ) (hclosed ℓ) (hbdd ℓ)
        hRconv hRclosed hRbdd (h0 ℓ) ht.1 ht.2)
    · -- `τ = 0`: `Set.Icc 0 0` is `{0}`, and `h₀` already places `x 0`
      subst hτ0
      rwa [le_antisymm ht.2 ht.1]
  jump {ℓ e} hmem {z} hz hguard := hjump ℓ e hmem (e.jumpIntersection_outer hz hguard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
