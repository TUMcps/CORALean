import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic

/-!
# [1, Alg. 3]: the automated verifier

The loop of [1, Alg. 3]: model check `φ` at step `Δt` and truncation order `κ`, return safe
if `L = []`, else model check `¬φ` and return unsafe if some `α̃ ∈ [-1, 1]^p` lies in no polytope
of its list (line 9, the program (26)), else halve `Δt`. `check Δt κ` and `checkNeg Δt κ` are
Alg. 2 on `φ` and `¬φ`, `tuneκ` is line 4's tuning of `κ` and `falsifiable` line 9; the loop is
`repeat`, which may not stop, so here it runs `fuel` times and gives `none` after that. The result
is `some true` for safe and `some false` for unsafe. `tEnd` of line 1 is the `Δt` it starts with.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X 𝕋 : Type} [Div 𝕋] [OfNat 𝕋 2]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the verdict after at most `fuel` halvings of `Δt`, `some true` for safe. -/
def STL.automatedVerification (tuneκ : 𝕋 → ℕ) (check checkNeg : 𝕋 → ℕ → List (Set X))
    (falsifiable : List (Set X) → Bool) : ℕ → 𝕋 → Option Bool
  | 0, _ => none
  | fuel + 1, Δt =>
    let κ := tuneκ Δt -- line 4
    let L := check Δt κ -- line 5
    if L.isEmpty then some true -- lines 6-7
    else
      let L' := checkNeg Δt κ -- line 8
      if falsifiable L' then some false -- lines 9-10
      else STL.automatedVerification tuneκ check checkNeg falsifiable fuel (Δt / 2) -- line 11

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
