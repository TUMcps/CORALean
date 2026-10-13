module

public import CORALean.HybridDynamics.Definitions.Invariant
public import CORALean.HybridDynamics.Theorems.FlowOuterInputSolution
public import CORALean.HybridDynamics.Theorems.JumpIntersectionOuter

@[expose] public section

/-!
# `Invariant`, discharged from the computed enclosures

`Invariant.jump` falls out of `JumpIntersectionOuter` at `hjump`, one enclosure per
transition met. `Invariant.flow` quantifies over every dwell time and every
admissible input `u`; `FlowOuterInputSolution` discharges `u` structurally from
`hconv`/`hclosed`/`hbdd`/`h0` about `ℓ.U`, so no `u` survives the criterion.

Two prices, and `InvariantOfEnclosureCut` is what pays neither. `h0` asks the
location's input set to hold the origin, which a constant drift — gravity —
already breaks. And `hflow` asks one `R` to absorb the enclosure at *every*
dwell time, the invariant nowhere in the statement; under a nonzero drift that
enclosure grows without bound and no compact `R` contains it.

`jumpIntersection` is `Intersection.intersection` on the guard, so this criterion
alone asks the guard to be in the state's own family (#39).

Kept for those locations. The fixpoint iteration that would find such an `R` is
left to CORA, as `NonlinearSysDT.confinement_of_subset` leaves its analogue.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
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
noncomputable def aux_remainder (ℓ : Location S G L 𝕋 n) (τ : ℝ) (m : ℕ) : S n :=
  Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.U


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Invariant.jump` is `JumpIntersectionOuter` at `hjump`; `Invariant.flow` is
`FlowOuterInputSolution` at `hflow`, an order `m` chosen per dwell time `τ`
since `hε` cannot hold at one order for every one of them. -/
theorem HybridAutomaton.invariant_of_enclosure [∀ n, Intersection (S n) (Vec ℝ n)]
    (HA : HybridAutomaton S S L 𝕋 n) (R : L → S n)
    (hconv : ∀ ℓ : L, Convex ℝ (construct (HA.loc ℓ).U))
    (hclosed : ∀ ℓ : L, IsClosed (construct (HA.loc ℓ).U))
    (hbdd : ∀ ℓ : L, Bornology.IsBounded (construct (HA.loc ℓ).U))
    (h0 : ∀ ℓ : L, (0 : Vec ℝ n) ∈ construct (HA.loc ℓ).U)
    (hflow : ∀ (ℓ : L) (τ : ℝ), 0 < τ → ∃ m : ℕ,
      ‖τ • toRealMat (HA.loc ℓ).dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 ∧
      Convex ℝ (construct (aux_remainder (HA.loc ℓ) τ m)) ∧
      IsClosed (construct (aux_remainder (HA.loc ℓ) τ m)) ∧
      Bornology.IsBounded (construct (aux_remainder (HA.loc ℓ) τ m)) ∧
      construct (Plus.plus ((HA.loc ℓ).timeIntervalStep τ (m + 2) (R ℓ))
        ((HA.loc ℓ).dynamics.inputSolution τ (m + 2) (HA.loc ℓ).U)) ⊆ construct (R ℓ))
    (hjump : ∀ (ℓ : L) (e : Transition S L 𝕋 n), e ∈ (HA.loc ℓ).trans →
      construct (e.jumpIntersection (R ℓ)) ⊆ construct (R e.target)) :
    HA.Invariant R where
  flow {ℓ τ x u} h h₀ {t} ht := by
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
