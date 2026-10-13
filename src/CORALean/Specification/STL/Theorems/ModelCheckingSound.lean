module

public import CORALean.Specification.STL.Theorems.ExistsNnf
public import CORALean.Specification.STL.Theorems.NnfExistsSampled
public import CORALean.Specification.STL.Theorems.SampToFormulaScale
public import CORALean.Specification.STL.Theorems.SatScale
public import CORALean.Specification.STL.Theorems.SampSatToCNF
public import CORALean.Specification.STL.Theorems.SampNodupToCNF
public import CORALean.Specification.STL.Theorems.CNFUpsilonSoundComplete
public import CORALean.Specification.STL.Theorems.TracesSubsetTraceSet

@[expose] public section

/-!
# STL model checking is sound

[1, Thm. 1]: a `c`-divisible STL formula `ϕ` is transformed to `ψ = Υ(⋀ᵢ ⋁ⱼ X_c^j (ϕᵢⱼ ∨ ϱᵢⱼ))`
such that, for every c-divisible finitely represented reach sequence `R` (with a state at every
time), `R ⊨ᵣ ψ` gives `C(R) ⊨ₜ ϕ` and `Traces(S) ⊨ₜ ϕ` for every set of traces `R` is a reach
sequence of. The pipeline: negation normal form and the scaling by `c` (`Lemma 4`), the rewriting
to sampled time ([1, Table 1]), the normal form (`Sec. 4.1`) and `Υ` (`Lemma 2`). `ψ` is `Υ`'s
output, which has the paper's shape up to distributing `X_a` over `∨`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.model_checking_sound {c : ℝ≥0} (hc : 0 < c) (φ : STL.Formula X) (hstl : φ.IsStl)
    (hdiv : φ.CDivisible c) : ∃ cnf : STL.CNF X,
      (∀ clause ∈ cnf, (clause.map STL.Branch.j).Nodup) ∧
        ∀ (T : Finset ℝ≥0) (R : ℝ≥0 → Set X), (∀ t, (R t).Nonempty) →
          ReachSequence.FinRep T R → ReachSequence.CDivisible c T →
            (cnf.upsilon c).Sat R → φ.HoldsOn (ReachSequence.traceSet R) ∧
              ∀ Traces : Set (ℝ≥0 → X), ReachSequence.Encloses R Traces →
                φ.HoldsOn Traces := by -- --- PROOF ---
  obtain ⟨n, -, hn, -⟩ := STL.Formula.exists_nnf c φ hstl hdiv
  obtain ⟨⟨s, hs⟩, -, -⟩ := STL.Nnf.hasSampledRewrite n
  refine ⟨s.toCNF true, s.nodup_toCNF true, fun T R hne hT hT' hSat => ?_⟩
  -- the sampled time formula at step `c` implies `ϕ`: scale the one at step `1` that implies `n`
  have hφ : ∀ ξ, (s.toFormula c).Sat ξ → φ.Sat ξ := fun ξ h => by
    have h₁ : (s.toFormula 1).Sat (fun t => ξ (t * c)) := by
      rw [← STL.Formula.sat_scale hc, STL.Samp.toFormula_scale]; exact h
    exact (hn ξ).1 ((STL.Formula.sat_scale hc _ ξ).2 (hs _ h₁))
  -- `Υ` is sound for the normal form, which is equivalent to `s`
  have hC := (STL.CNF.upsilon_sound_complete hc hne hT hT' (s.toCNF true)
    (s.nodup_toCNF true)).1 hSat
  have hholds : φ.HoldsOn (ReachSequence.traceSet R) := fun ξ hξ =>
    hφ ξ (by simpa using (STL.Samp.sat_toCNF c s true ξ).1 (hC ξ hξ))
  exact ⟨hholds, fun Traces hTr ξ hξ => hholds ξ (ReachSequence.traces_subset_traceSet hTr hξ)⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
