module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# [1, Alg. 3]: the automated verifier

The loop of [1, Alg. 3]: model check `φ` at step `Δt` and truncation order `κ`, return safe
if `L = []`, else model check `¬φ` and return unsafe if some `α̃ ∈ [-1, 1]^p` lies in no polytope
of its list (line 9, the program (26)), else halve `Δt`. `check Δt κ` and `checkNeg Δt κ` are
Alg. 2 on `φ` and `¬φ`, `tuneκ` is line 4's tuning of `κ` and `falsifiable` line 9; the loop is
`repeat`, which may not stop, so here it runs `fuel` times and gives `none` after that. The result
is `some true` for safe and `some false` for unsafe. `tEnd` of line 1 is the `Δt` it starts with.

## Inputs
* `tuneκ` – choice of the Taylor order
* `check` – check of the specification
* `checkNeg` – check of the negated specification
* `falsifiable` – test for a falsifying reach set

## Output
* safe, unsafe or undecided after at most the given halvings

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X 𝕋 : Type} [Div 𝕋] [OfNat 𝕋 2]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the verdict after at most `fuel` halvings of `Δt`, `some true` for safe. -/
def STL.automatedVerification (tuneκ : 𝕋 → ℕ) (check checkNeg : 𝕋 → ℕ → List (Set X))
    (falsifiable : List (Set X) → Bool) : ℕ → 𝕋 → Option Bool
  | 0, _ => none
  | fuel + 1, Δt =>
    -- 4. `κ ← increase κ until 1 − ‖T(κ)‖_F / ‖T(κ+1)‖_F ≤ 10⁻¹⁰`, here `tuneκ`
    let κ := tuneκ Δt
    -- 5. `L ← model check φ with parameters Δt and κ using Alg. 2`
    let L := check Δt κ
    -- 6. `if L = ∅ then return safe`
    if L.isEmpty then some true
    else
      -- 8. `L ← model check ¬φ with parameters Δt and κ using Alg. 2`
      let L' := checkNeg Δt κ
      -- 9. `if ∃ α̃ ∈ [-1, 1]^p : α̃ ∉ K_j ∀ K_j ∈ L then return unsafe`
      if falsifiable L' then some false
      -- 11. `Δt ← Δt / 2`, and the `repeat` of line 3 goes round again
      else STL.automatedVerification tuneκ check checkNeg falsifiable fuel (Δt / 2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
