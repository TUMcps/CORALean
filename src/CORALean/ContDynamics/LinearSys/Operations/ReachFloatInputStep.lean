module

public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# One pass of `reachFloatInput`'s loop

The body of CORA's `priv_reach_standard` loop, in `𝕋`, on the state
`(H(t_{k+1}), H(τ_k), P^R(t_{k+1}), [e^{AΔt}]^k P^R(Δt))`: the homogeneous and
constant-input sets each advance by `[e^{AΔt}] H ⊕ P̃(Δt)`, reduced to order
`ρ`; the time-varying input's propagated one-step set advances by `[e^{AΔt}]`
and is added to the accumulated `P^R`, which is reduced as CORA reduces it.
Nothing here depends on the system but the two sets it is handed.

## Inputs
* `eAΔt` – float exponential enclosure of the step
* `Pu` – float one-step set of the constant input
* `ρ` – zonotope order
* `s` – loop state of four zonotopes

## Output
* loop state one step on
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop state one step on, from `[e^{AΔt}]`, the constant input's
`P̃(Δt)` and the order `ρ`. -/
def LinearSys.reachFloatInputStep (eAΔt : Interval (Mat 𝕋 n n)) (Pu : Zonotope (Vec 𝕋 n)) (ρ : ℕ)
    (s : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) :=
  let Htp := s.1                                                    -- H(t_{k+1})
  let Hti := s.2.1                                                  -- H(τ_k)
  let PU := s.2.2.1                                                 -- P^R(t_{k+1})
  let PUnext := s.2.2.2                                             -- [e^{AΔt}]^k P^R(Δt)
  let eA := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{AΔt}] ·
    (S := 𝒵[𝕋]) eAΔt
  let PUnext' := eA PUnext                                          -- [e^{AΔt}]^{k+1} P^R(Δt)
  (Reduce.reduce (eA Htp ⊞ Pu) ρ,                                   -- H(t_{k+2})
    Reduce.reduce (eA Hti ⊞ Pu) ρ,                                  -- H(τ_{k+1})
    Reduce.reduce (PU ⊞ PUnext') ρ,                                 -- P^R(t_{k+2})
    PUnext')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
