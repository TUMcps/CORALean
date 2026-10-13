import CORALean.ContDynamics.LinearSys.Definitions.ManualStateFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinearSys.Operations.SquaringsFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

/-!
# `Alg. 1` lines 5-11 in floats: one iteration of the main loop

`manualStep` computed in `𝕋`, at a fixed step `Δt`, order `η` and zonotope order `ρ`. `V` is
split `ũ ⊕ Ũ` at its stored centre (line 1). `[e^{At_k}]` and `[e^{At_{k+1}}]` are taken by
scaling and squaring at their float brackets, so `H(t_{k+1})` is reached from `X₀` directly,
as line 7 reaches it. `P^u(t_{k+1})`, a point in [1], is kept as a box, so its rounding
does not accumulate generators.

One departure, the float layer's: lines 8-9's `comb(H(t_k), H(t_{k+1})) ⊕ F H(t_k) ⊕ G ũ`
is taken as `comb(H(t_k), [e^{AΔt}] H(t_k)) ⊕ [F] H(t_k)` (`timeIntervalStepFloat`) plus
the input solution of the segment `[0, ũ]`, which holds `P^u(τ)` for every `τ ∈ [0, Δt]`:
the float layer has no `G`, and encloses a constant input's share this way throughout.
`η` must be admissible for the float enclosures; `manualReachFloat` raises it until it is.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 5-11: one iteration of [1, Alg. 1] from `X₀` under inputs in `V`, the next state
and `R̂(τ_k)`, or `none` where no squaring count fits `[e^{At_k}]` or `[e^{At_{k+1}}]`. -/
def LinearSys.manualStepFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (Δt : 𝕋)
    (η ρ : ℕ) (s : LinearSys.ManualStateFloat 𝕋 n) :
    Option (LinearSys.ManualStateFloat 𝕋 n × Zonotope (Vec 𝕋 n)) := do
  let ũ := (Interval.point V.c).zonotope                            -- 1. {ũ}, V's stored centre
  let Ũ := Recentre.recentre V                                      -- 1. U₀ = V - ũ, holding 0
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  let PuΔt := sys.inputSolutionFloat Δt η ũ                         -- 3. P^u(Δt), eq. (19)
  let PUΔt := sys.inputSolutionFloat Δt η Ũ                         -- 3. P̂^U(Δt), eq. (20)
  let PuτΔt := sys.inputSolutionFloat Δt η seg                      -- P^u(τ), every τ ≤ Δt
  let tk1 := s.t + ToRat.toRat Δt                                   -- 5. t_{k+1}
  let tLo1 := addDown s.tLo Δt                                      -- 5. a float below t_{k+1}
  let tHi1 := addUp s.tHi Δt                                        -- 5. a float above t_{k+1}
  let sq ← sys.squaringsFloat Δt s.tLo s.tHi η                      -- t_k / 2^sq within Δt
  let Φtk := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- 6. [e^{A t_k}] ·
    (S := fun k => Zonotope (Vec 𝕋 k))
    (sys.expSquaringFloat s.tLo s.tHi η sq)
  let Puk1 := (s.Pu.zonotope ⊞ Φtk PuΔt).interval                   -- 6. P^u(t_{k+1}), a box
  let sq1 ← sys.squaringsFloat Δt tLo1 tHi1 η                       -- t_{k+1} / 2^sq1 within Δt
  let Φtk1 := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- 7. [e^{A t_{k+1}}] ·
    (S := fun k => Zonotope (Vec 𝕋 k))
    (sys.expSquaringFloat tLo1 tHi1 η sq1)
  let Hk1 := Φtk1 X₀ ⊞ Puk1.zonotope                                -- 7. H(t_{k+1})
  let Hτk := sys.timeIntervalStepFloat Δt η s.H ⊞ PuτΔt             -- 8.-9. Ĥ(τ_k)
  let PUk1 := Reduce.reduce (s.PU ⊞ Φtk PUΔt) ρ                     -- 10. P̂^U(t_{k+1})
  let Rτk := Hτk ⊞ PUk1                                             -- 11. R̂(τ_k)
  pure ({ t := tk1, tLo := tLo1, tHi := tHi1, H := Hk1, Pu := Puk1, PU := PUk1 }, Rτk)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
