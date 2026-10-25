module

public import CORALean.Specification.STL.Definitions.IsDependencyPreservedBy

@[expose] public section

/-!
# Every enclosure is dependency preserving, read existentially

[1, Def. 4] asks that `μ` and `E` can be built from `R(t)`. Read as `∃ μ E`, the solution map itself
is `μ`, `E = {0}`: `ξ ∈ ξ ⊕ {0} ⊆ R` is `ξ ∈ R`, and `E = {0} = R` makes `R` a singleton, so the
nontriviality clause holds. The definition then excludes nothing: what [1] means is that `μ` is
read off the representation of `R`, as [1, Prop. 1] does for Alg. 1.

## Inputs
* `ξ` – solution map
* `X₀` – initial set
* `𝒰` – set of inputs
* `R` – reachable set enclosure
* `tEnd` – final time

## Hypotheses
* `h` – the enclosure contains every solution

## Conclusion
* the enclosure preserves the dependency

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X Y : Type} [AddCommGroup X]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.dependencyPreserved_of_encloses (ξ : ℝ → X → (ℝ → Y) → X) (X₀ : Set X)
    (𝒰 : Set (ℝ → Y)) (R : ℝ → Set X) (tEnd : ℝ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) tEnd, ∀ x₀ ∈ X₀, ∀ u ∈ 𝒰, ξ t x₀ u ∈ R t) : -- --- CONCL ---
    STL.IsDependencyPreservedBy ξ X₀ 𝒰 R tEnd ξ (fun _ => {0}) := by -- --- PROOF ---
  refine ⟨fun t _ _ hE => ⟨0, hE.symm⟩, fun t ht x₀ hx₀ u hu => ⟨?_, ?_⟩⟩
  · exact ⟨0, rfl, by simp⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [Set.mem_singleton_iff.mp he]
    simpa using h t ht x₀ hx₀ u hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
