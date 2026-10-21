module

public import CORALean.HybridDynamics.Definitions.Invariant
public import CORALean.HybridDynamics.Theorems.FlowOuterSplit
public import CORALean.HybridDynamics.Theorems.JumpOuter

@[expose] public section

/-!
# `Invariant` from the enclosures, cut down by the location's invariant

`InvariantOfEnclosure` without the two hypotheses no caller could meet. `FlowOuterSplit` stands in
for `FlowOuterInputSolution`, so `0 ∈ ℓ.inputSet` is gone; and `hflow`'s containment is asked only
of the part of the enclosure still inside `ℓ.inv`, so a dwell time long enough to leave the
location need not be absorbed by `R`. The cut is `∩ construct (HA.loc ℓ).inv` on sets rather than
`Location.timeIntervalInv`, which would need `Intersection` and shut out `Zonotope`; `hjump`
names `Rg` for the same reason. Both cuts being set inclusions lets the invariant and the guard sit
in their own representation `G`; `Examples.BouncingBall` runs it at a zonotope state (#39).

## Inputs
* `HA` – hybrid automaton
* `R` – reach set

## Hypotheses
* `hflow` – every dwell time is enclosed by the sets inside the invariant
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
variable [∀ n, ContSet (G n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Mtimes (Mat 𝕋) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Invariant.flow` is `FlowOuterSplit` at `hflow`, an order `m` per dwell
time and the enclosure cut to `ℓ.inv`; `Invariant.jump` is `JumpOuter` at
`hjump`, one enclosure per transition met. -/
theorem HybridAutomaton.invariant_of_enclosure_cut [∀ n, OfPoint (S n) (Vec ℝ n)]
    [∀ n, Recenter (S n) (Vec ℝ n)] [∀ n, ConvexSet (S n) (Vec ℝ n)]
    [∀ n, CompactSet (S n) (Vec ℝ n)]
    (HA : HybridAutomaton S G L 𝕋 n) (R : L → S n)
    (hflow : ∀ (ℓ : L) (τ : ℝ), 0 < τ → ∃ m : ℕ,
      ‖τ • toRealMat (HA.loc ℓ).dynamics.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 ∧
      construct ((HA.loc ℓ).timeIntervalSplit τ (m + 2) (R ℓ))
        ∩ construct (HA.loc ℓ).inv ⊆ construct (R ℓ))
    (hjump : ∀ (ℓ : L) (e : Transition G L 𝕋 n), e ∈ (HA.loc ℓ).trans → ∃ Rg : S n,
      construct (R ℓ) ∩ construct e.guard ⊆ construct Rg ∧
      construct (e.jump Rg) ⊆ construct (R e.target)) :
    HA.Invariant R where
  flow {ℓ τ x u w} h h₀ {t} ht := by
    rcases h.nonneg.lt_or_eq with hτ | hτ0
    · -- `τ > 0`: the stay's own state is in the enclosure and in `ℓ.inv`, and
      -- `hflow`'s containment is asked of exactly that intersection
      obtain ⟨m, hε, hsub⟩ := hflow ℓ τ hτ
      exact hsub ⟨h.timeInterval_outer_split h₀ hτ hε ht.1 ht.2, h.invariant t ht⟩
    · -- `τ = 0`: `Set.Icc 0 0` is `{0}`, and `h₀` already places `x 0`
      subst hτ0
      rwa [le_antisymm ht.2 ht.1]
  jump {ℓ e} hmem {z} hz hguard := by
    obtain ⟨Rg, hinter, hsub⟩ := hjump ℓ e hmem
    exact hsub (e.jump_outer hinter hz hguard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
