module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The factors that may reach a polytope: `K`

For a reachable set `⟨c, G⟩_Z` whose generators split into the tuple `H`, which carry the
initial state and the inputs, and the set `K` of the generators that only carry uncertainty, and a
polytope `⟨C, d⟩_P`, the polytope of [1, Prop. 2]

`K = ⟨[C G(·,H) 0], d - C c + Σ_{j∈K} |C G(·,j)|⟩_P`

in factor space. `[C G(·,H) 0] α̃` uses the first `|H|` entries of `α̃ ∈ ℝ^p` for the generators of
`H`, in order, as `[1, Prop. 1]`'s layout of `α̃` has it, hence `|H| ≤ p`. The reading of `K` as
a tuple is a `Finset`: only its members count.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (a zonotope
computation over `𝕋` with directed rounding) is not yet written.

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

variable {n s γ h p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 2]: the factors `α̃` with `C G(·,H) α̃ ≤ d - C c + Σ_{j∈K} |C G(·,j)|`. -/
def STL.unsafeFactors (C : Matrix (Fin s) (Fin n) ℝ) (d : Fin s → ℝ) (c : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin γ) ℝ) (H : Fin h → Fin γ) (K : Finset (Fin γ)) (hp : h ≤ p) :
    Set (Fin p → ℝ) :=
  {α | ∀ r, ∑ i, (C * G) r (H i) * α (Fin.castLE hp i) ≤
      d r - (C.mulVec c) r + ∑ k ∈ K, |(C * G) r k|}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
