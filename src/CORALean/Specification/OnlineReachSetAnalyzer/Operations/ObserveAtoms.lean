module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.ApValue
public import CORALean.Specification.FourValuedSignal.Operations.Basic

@[expose] public section

/-!
# The atom signals of a sequence of observations

The signal `⟦a⟧_R̃` of every atom `a` after the observations `obs`, each a set, a time interval and
a location, made on top of `sig`: on an observed interval the value of `a` on the set
(`OnlineAnalyzerNode.apValue`, CORA's `canBeTrue` and `canBeFalse`), elsewhere the value before.
From the inconclusive signal it is the partial reachable set of [1, Sec. 4.3 (satisfaction)] read
through the atoms; a later observation of a time overwrites an earlier one, as `signal.set` in CORA
does.

## Inputs
* `sig` – atom signals before the observations
* `obs` – observations: set, time interval, location

## Output
* the atom signals after the observations

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def OnlineReachSetAnalyzer.observeAtoms
    (sig : AtomicProposition S d → FourValuedSignal ℝ) (obs : List (S d × STLInterval ℝ × ℕ)) :
    AtomicProposition S d → FourValuedSignal ℝ :=
  obs.foldl (fun sig o a => match OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a o.1 o.2.2 with
    | some v => (sig a).set o.2.1 (FourValued.fromKleene v)
    | none => sig a) sig

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
