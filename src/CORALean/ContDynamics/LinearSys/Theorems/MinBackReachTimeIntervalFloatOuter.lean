module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetForallExistsExact
public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetOfInputExact
public import CORALean.ContDynamics.LinearSys.Operations.MinBackReachPFloat
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# `Thm. 1` in floats: what `Alg. 2` returns encloses the AE set over `τ`

[1, Thm. 1] at the float layer's run, [1, Alg. 2]'s: `R^{∀∃}(-τ)` sits inside the union of the `ω`
steps' float sets, each cut by `⟨N,p⟩_H`, `p` the float `minBackReachPFloat`. Same direction as
over `ℝ`, `⊆`: an outer approximation, here also outer in the rounding, since every float set is
an enclosure. Three of the theorem's four moves are proved outright, exactly as there; the fourth,
that the propagated sets and support values really do enclose, is `hcov` and `hp`, stated against
the float run's own outputs. `hp` is stated at the real number `p_(j)` denotes, and
`minBackReachSupportFloat_ge` is what makes that number an upper bound of the support values.

## Inputs
* `sys` – linear system
* `T` – time domain
* `τ` – target time set
* `U` – input set
* `W` – disturbance set
* `Xend` – target set
* `CZ` – target constrained zonotope
* `W₀` – initial disturbance float zonotope
* `U₀` – initial input float zonotope
* `Zw` – center trajectory contribution
* `N` – direction matrix
* `t₀` – float start time
* `Δt` – float step length
* `η` – Taylor order
* `ν` – number of squarings
* `ω` – number of iterations
* `u₀` – central input signal
* `û` – per-direction input signals

## Hypotheses
* `hu₀` – central input lies in the input set
* `hmu₀` – central input measurable
* `hû` – direction inputs lie in the input set
* `hmû` – direction inputs measurable
* `hcov` – steps' sets cover the set of the central input
* `hp` – each direction is bounded by a cut direction

## Conclusion
* the union of the cut float steps encloses the AE backward reachable set

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet MeasureTheory

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `Û = {u₀} ∪ {û j}` inside `U`, `Alg. 2`'s union of cut float steps encloses the
time-interval AE backward reachable set. -/
theorem LinearSys.minBackReachTimeIntervalFloat_outer (sys : LinearSys 𝕋 n) {T τ : Set ℝ}
    {U W Xend : S n}
    {CZ : ConZonotope 𝕋 (Vec 𝕋 n)} {W₀ U₀ : Zonotope (Vec 𝕋 n)} {Zw : 𝕋 → Zonotope (Vec 𝕋 n)}
    {N : Mat 𝕋 q n} {t₀ Δt : 𝕋} {η ν ω : ℕ}
    -- `Û ⊂ U`: the center trajectory `u₀(·)` and the `q` others, all admissible
    {u₀ : ℝ → Vec ℝ n} {û : Fin q → ℝ → Vec ℝ n}
    (hu₀ : ∀ s ∈ T, u₀ s ∈ construct U)
    (hmu₀ : AEStronglyMeasurable u₀ (volume.restrict T))
    (hû : ∀ i s, s ∈ T → û i s ∈ construct U)
    (hmû : ∀ i, AEStronglyMeasurable (û i) (volume.restrict T))
    -- (44), (45): the `ω` steps enclose the center trajectory's own set
    (hcov : sys.timeIntervalBackReachSetOfInputExact T U W Xend τ u₀ ⊆
      ⋃ k < ω, (sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).R.construct)
    -- (46), (49): each `p_(j)` is a support value of some trajectory's own set
    (hp : ∀ j : Fin q, ∃ i : Fin q,
      ∀ x ∈ sys.timeIntervalBackReachSetOfInputExact T U W Xend τ (û i),
        (toRealMat N *ᵥ x) j ≤ toReal (sys.minBackReachPFloat CZ W₀ U₀ Zw N t₀ Δt η ν (ω - 1) j)) :
    sys.timeIntervalBackReachSetForallExistsExact T U W Xend τ ⊆
      ⋃ k < ω, ((sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k).R.construct ∩
        (HPolytope.ineqs N
        (sys.minBackReachPFloat CZ W₀ U₀ Zw N t₀ Δt η ν (ω - 1))).construct) := by -- --- PROOF ---
  intro x₀ hx₀
  -- (42), (55): `x₀` is in `R^∃(-τ;u*(·))` for every admissible `u*(·)`, so for `Û`'s
  have key : ∀ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) →
      AEStronglyMeasurable u (volume.restrict T) →
      x₀ ∈ sys.timeIntervalBackReachSetOfInputExact T U W Xend τ u :=
    fun u hu hmu => hx₀ u hu hmu
  -- (57): every row of `⟨N,p⟩_H` bounds one of those sets, hence `x₀`
  have hP : x₀ ∈ (HPolytope.ineqs N
      (sys.minBackReachPFloat CZ W₀ U₀ Zw N t₀ Δt η ν (ω - 1))).construct := by
    refine HPolytope.mem_ineqs_iff.mpr fun j => ?_
    obtain ⟨i, hi⟩ := hp j
    exact hi x₀ (key (û i) (hû i) (hmû i))
  -- (44): the center trajectory's own set is covered by the `ω` steps
  obtain ⟨k, hk, hkx⟩ := Set.mem_iUnion₂.mp (hcov (key u₀ hu₀ hmu₀))
  -- (48): distributing the intersection over the union
  exact Set.mem_iUnion₂.mpr ⟨k, hk, hkx, hP⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
