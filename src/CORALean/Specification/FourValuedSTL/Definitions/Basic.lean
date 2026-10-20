module

public import CORALean.Specification.FourValuedSTL.Definitions.Hat
public import CORALean.Specification.FourValuedSTL.FourValuedSTL
public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Definitions.IsValid

@[expose] public section

/-!
# `FourValuedSTL/Definitions`: small declarations

One section per declaration, at most five code lines each (CONTRIBUTING, "Small declarations").
`HoldsOn` is `H ⊨ φ` of [1, Sec. 2.5], `satBool` the signal `⟦φ⟧_ξ`, `reachSet` the reachable set
of [1, Sec. 2.4], `Covers` and `Extends` the relations `ξ ≺ R` and `R ≺ R̃` of [1, Sec. 4.2, 4.3
(satisfaction)]. `IsAtomSignal` says a signal is the satisfaction signal of an atom over `R`
(`IsPartialAtomSignal` over `R̃`); the operators need finite variability, which a valid signal has
([1, Sec. 2.3 (signals)]).

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open scoped NNReal


-- ==================================  `FourValuedSTL.Covers`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ξ ≺ R`, [1, Sec. 4.2 (satisfaction)]: the reachable set `R` covers the execution `ξ`. -/
def FourValuedSTL.Covers {X : Type} (R : ℝ≥0 → Set X) (ξ : ℝ≥0 → X) : Prop := ∀ t, ξ t ∈ R t


-- =================================  `FourValuedSTL.Extends`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `R ≺ R̃`, [1, Sec. 4.3 (satisfaction)]: `R` extends the partial reachable set `R̃` on `T`. -/
def FourValuedSTL.Extends {X : Type} (R Rp : ℝ≥0 → Set X) (T : Set ℝ≥0) : Prop :=
  ∀ t ∈ T, R t = Rp t


-- =============================  `FourValuedSTL.Formula.HoldsOn`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `H ⊨ φ`, [1, Sec. 2.5]: `φ` holds of every execution in `E`, `ξ ⊨ φ` being `⟦φ⟧_ξ(0) = ⊤`. -/
def FourValuedSTL.Formula.HoldsOn {X : Type} (φ : FourValuedSTL.Formula X)
    (E : Set (ℝ≥0 → X)) : Prop := ∀ ξ ∈ E, φ.Sat ξ 0


-- =============================  `FourValuedSTL.Formula.satBool`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

open Classical in
/-- `⟦φ⟧_ξ(t)` as a Boolean, [1, Sec. 2.5]: `⊤` where `φ.Sat ξ t`, `⊥` otherwise. -/
noncomputable def FourValuedSTL.Formula.satBool {X : Type} (φ : FourValuedSTL.Formula X)
    (ξ : ℝ≥0 → X) (t : ℝ≥0) : Bool := decide (φ.Sat ξ t)


-- ===============================  `FourValuedSTL.IsAtomSignal`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `s` is the `U₁`-signal `t ↦ â(R(t))` of the atom `a`, of finite variability (a valid signal). -/
def FourValuedSTL.IsAtomSignal {X : Type} (R : ℝ≥0 → Set X) (a : X → Prop) (s : KleeneSignal ℝ) :
    Prop := s.IsValid ∧ ∀ t : ℝ≥0, s.at t = FourValuedSTL.hat a (R t)


-- =================================  `FourValuedSTL.reachSet`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `R(t) := {ξ(t) ∣ ξ an execution of H}`, [1, Sec. 2.4], `E` the executions. -/
def FourValuedSTL.reachSet {X : Type} (E : Set (ℝ≥0 → X)) (t : ℝ≥0) : Set X :=
  {x | ∃ ξ ∈ E, ξ t = x}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
