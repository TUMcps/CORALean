module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The region of attraction of a set

[1, Sec. 3.1.2]: `D = {[x(0); y(0)] | ∀ u(·) ∈ U(·) : lim_{t→∞} γ(t, x(0), y(0), u(·)) ∈ S}`, the
initial states from which every admissible input leads into the invariant set `S`, read as
printed: the limit exists and lies in `S`. `γ` is the unique solution [1, Sec. 3.1] assumes,
an argument here as in the paper (`RobustInvariant`).

## References

* [1] M. Althoff. "Benchmarks for the Formal Verification of Power Systems". In Proc. of the
      9th International Workshop on Applied Verification of Continuous and Hybrid Systems
      (ARCH22), EPiC Series in Computing, vol. 90, pp. 26-43, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology

variable {X Inp : Type} [TopologicalSpace X]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.1.2]: the initial states whose solutions all converge into `S`. -/
def regionOfAttraction (γ : ℝ → X → (ℝ → Inp) → X) (U : Set (ℝ → Inp)) (S : Set X) : Set X :=
  {x₀ | ∀ u ∈ U, ∃ L ∈ S, Tendsto (fun t => γ t x₀ u) atTop (𝓝 L)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
