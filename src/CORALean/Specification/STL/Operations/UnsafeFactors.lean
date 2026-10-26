module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The factors that may reach a polytope: `K`

For a reachable set `⟨c, G⟩_Z` whose generators split into the tuple `H` (initial state and
inputs) and the set `K` of those carrying only uncertainty, and a polytope `⟨C, d⟩_P`, the polytope
of [1, Prop. 2] `K = ⟨[C G(·,H) 0], d - C c + Σ_{j∈K} |C G(·,j)|⟩_P`. `[C G(·,H) 0] α̃`
uses the first `|H|` entries of `α̃ ∈ ℝ^p`, in order as [1, Prop. 1]'s layout has it, hence
`|H| ≤ p`; `K` is a `Finset`, only its members count.
Refinement pending: the set is unbounded in `α̃`, and the rounded matrix `C G(·,H)` of a float
polytope has an error `(C G - C̃ G̃) α̃` no offset absorbs without a bound on `α̃`; an outward
refinement would intersect with the box `[-1, 1]^p`, which the real set lacks and CORA never does.

## Inputs
* `C` – polytope matrix
* `d` – polytope offsets
* `c` – center of the reachable set
* `G` – generator matrix
* `H` – generator selection
* `K` – generators carrying only uncertainty

## Hypotheses
* `hp` – the selection fits the factor dimension

## Output
* the factors that may reach the polytope

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
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
