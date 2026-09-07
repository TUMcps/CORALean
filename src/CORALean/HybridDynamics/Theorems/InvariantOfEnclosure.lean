import CORALean.HybridDynamics.Invariant
import CORALean.HybridDynamics.Theorems.FlowOuterInputSolution
import CORALean.HybridDynamics.Theorems.JumpAndOuter

/-!
# `Invariant`, discharged from the computed enclosures

`Invariant.jump` falls out of `JumpAndOuter` at `hjump`, one enclosure per
transition met. `Invariant.flow` quantifies over every dwell time `τ` and
every admissible input `u`; `FlowOuterInputSolution` already discharges `u`
structurally from `hconv`/`hclosed`/`hbdd`/`h0` about `ℓ.U`, so nothing about
`u` survives into this criterion at all.

Two prices, and `InvariantOfEnclosureCut` is what pays neither. `h0` asks the
location's input set to hold the origin, which a constant drift — gravity —
already breaks. And `hflow` asks one `R` to absorb the enclosure at *every*
dwell time, the location's invariant nowhere in the statement; that enclosure
grows without bound in `τ` under a nonzero drift, and a nonempty compact `R`
cannot contain it. So this holds only where the drift vanishes.

Kept for those locations, and because it is the shape the cut is read against.
The fixpoint iteration that would find such an `R` is not implemented, exactly
as `NonlinearSysDT.confinement_of_subset` leaves the analogous search to CORA.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Mtimes (Mat 𝕋) S] [OfInterval S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The set `hflow`'s remainder-side hypotheses are asked of: `τ`'s remainder
bound against the location's own input set. -/
noncomputable def aux_remainder (ℓ : Location S L 𝕋 n) (τ : ℝ) (m : ℕ) : S n :=
  Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainder (toRealMat ℓ.dynamics.A) τ (m + 2)) ℓ.U


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Invariant.jump` is `JumpAndOuter` at `hjump`; `Invariant.flow` is
`FlowOuterInputSolution` at `hflow`, an order `m` chosen per dwell time `τ`
since `hε` cannot hold at one order for every one of them. -/
theorem HybridAutomaton.invariant_of_enclosure [∀ n, And (S n) (Vec ℝ n)]
    (HA : HybridAutomaton S L 𝕋 n) (R : L → S n)
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
      construct (e.jumpAnd (R ℓ)) ⊆ construct (R e.target)) :
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
  jump {ℓ e} hmem {z} hz hguard := hjump ℓ e hmem (e.jumpAnd_outer hz hguard)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
