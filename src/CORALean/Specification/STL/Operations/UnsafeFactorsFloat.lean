module

public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# The factors that may reach a polytope, over a float scalar

The polytope `K = ⟨[C G(·,H) 0], d - C c + Σ_{j∈K} |C G(·,j)|⟩_P` of `unsafeFactors` from float
data, clipped to the factor box `[-1, 1]^p`: the rows `C G(·,H)` are stored rounded down, and the
offset is rounded up and pays what a stored row can miss on the box (the entrywise gap of
`C G` rounded both ways, `radius`). Read with the box, the float polytope encloses the real one
cut to the box (`unsafeFactorsFloat_outer`); off the box the rounded rows bound nothing. Every use
of the factors keeps them in the box, as [1, Prop. 2] does; the clipping is a departure from
CORA, which computes the rows in doubles and does not clip.

## Inputs
* `C` – polytope matrix
* `d` – polytope offsets
* `c` – center of the reachable set
* `G` – generator matrix
* `H` – generator selection
* `K` – generators carrying only uncertainty

## Output
* the rows and offsets of the polytope, to be read with the box `[-1, 1]^p`

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n s γ h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 2] over floats: the rows `C G(·,H)` rounded down and the offsets rounded up, with the
slack the rows cost on the box `[-1, 1]^p`. -/
def STL.unsafeFactorsFloat (C : Mat 𝕋 s n) (d : Vec 𝕋 s) (c : Vec 𝕋 n) (G : Mat 𝕋 n γ)
    (H : Fin h → Fin γ) (K : Finset (Fin γ)) : Mat 𝕋 s h × Vec 𝕋 s :=
  -- C G, rounded both ways
  let lo := matMulDown C G
  let hi := matMulUp C G
  -- [C G(·,H) 0], stored rounded down
  let A : Mat 𝕋 s h := fun r i => lo r (H i)
  -- what a stored row can miss on the box
  let err : Vec 𝕋 s := radius fun r i => subUp (hi r (H i)) (lo r (H i))
  -- Σ_{j∈K} |C G(·,j)|, rounded up
  let unc : Vec 𝕋 s := fun r => sumUp fun k =>
    if k ∈ K then maximum (absolute (lo r k)) (absolute (hi r k)) else zero
  -- d - C c + Σ_{j∈K} |C G(·,j)|, rounded up, and the slack
  let b : Vec 𝕋 s := fun r => addUp (addUp (subUp (d r) (dotDown (C r) c)) (unc r)) (err r)
  (A, b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
