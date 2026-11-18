module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LinearSys.verifyInputInnerFloat`, the support of one step's held input from below

CORA's `aux_underPU` holds the input over a step: its solution is `(∫₀^Δt e^{sA} ds) M β` for one
`β ∈ [-1, 1]^m`, and `β = sign(ℓ' PG)` reaches `Σ_c |ℓ' PG_c|`, `PG = (∫₀^Δt e^{sA} ds) M`. Here
`PG` is a member of the box `Vs` of the orders' sum plus a remainder within `ρ_l` in row `l`, and
the direction is within `E` of `ℓ̃`: `Σ_c mig(ℓ̃' [Vs]_c) − |ℓ̃|'ρ − E β`, rounded down, the
mignitude of each column's sums rounded down and up.

## Inputs
* `Vs` – float box of the sum of the orders
* `ρ` – float bound of the remainder per row
* `β` – float bound of the scaled row sums of `PG`
* `ℓ` – float direction
* `E` – float bound of the weighted error of the direction

## Output
* float lower bound of `Σ_c |ℓ' PG_c|` along the exact direction
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Σ_c mig(ℓ̃' Vs_c) − |ℓ̃|'ρ − E β`, rounded down. -/
def LinearSys.verifyInputInnerFloat (Vs : Interval (Mat 𝕋 n m)) (ρ : Vec 𝕋 n) (β : 𝕋)
    (ℓ : Vec 𝕋 n) (E : 𝕋) : 𝕋 :=
  let mig := fun c =>                                                        -- ≤ |ℓ̃' Vs_c|
    let up := sumUp fun l => maximum (mulUp (ℓ l) (Vs.inf l c)) (mulUp (ℓ l) (Vs.sup l c))
    let dn := sumDown fun l => minimum (mulDown (ℓ l) (Vs.inf l c)) (mulDown (ℓ l) (Vs.sup l c))
    maximum zero (maximum dn (neg up))
  subDown (subDown (sumDown mig) (sumUp fun l => mulUp (absolute (ℓ l)) (ρ l))) (mulUp E β)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
