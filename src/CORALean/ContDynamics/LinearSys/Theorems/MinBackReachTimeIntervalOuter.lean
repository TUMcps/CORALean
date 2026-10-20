module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetForallExistsExact
public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalBackReachSetOfInputExact
public import CORALean.ContDynamics.LinearSys.Operations.MinBackReachTimeInterval
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# `Thm. 1`: what `Alg. 2` returns encloses the AE set over `τ`

[1, Thm. 1] holds [1, Alg. 2] to its claim: `R^{∀∃}(-τ)` sits inside the union of the `ω` steps'
sets, each cut by `⟨N,p⟩_H`. Three of the theorem's four moves are proved outright: restricting
`∀u(·)∈U` to the finite `Û`, enclosing each trajectory's own set by the halfspaces, and distributing
the intersection over the union. The fourth, that the propagated sets and support values really do
enclose, is what the paper imports from the standard propagation for (44), (45) and (46); it is
`hcov` and `hp` here. `⊆`, not `=`: [1, (48)] claims an outer approximation and nothing more. The
sets are over Carathéodory runs: under derivative-everywhere runs a non-measurable input admits
none, the left-hand side would be empty whenever `U` holds two points.

## Inputs
* `sys` – linear system
* `T` – time domain
* `τ` – target time set
* `U` – input set
* `W` – disturbance set
* `Xend` – target set
* `ρ` – support oracle for constrained zonotopes
* `CZ` – target constrained zonotope
* `W₀` – initial disturbance zonotope
* `U₀` – initial input zonotope
* `Zw` – center trajectory contribution
* `N` – direction matrix
* `t₀` – start time
* `tend` – end time
* `Δt` – step length
* `η` – Taylor order
* `ω` – number of iterations
* `u₀` – central input signal
* `û` – per-direction input signals

## Hypotheses
* `hΔt` – step is the horizon over the iteration count
* `hu₀` – central input lies in the input set
* `hmu₀` – central input measurable
* `hû` – direction inputs lie in the input set
* `hmû` – direction inputs measurable
* `hcov` – steps' sets cover the set of the central input
* `hp` – each direction is bounded by a cut direction

## Conclusion
* the union of the cut steps encloses the AE backward reachable set
## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar MeasureTheory

variable {n q : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `Û = {u₀} ∪ {û j}` inside `U`, `Alg. 2`'s union of cut steps encloses
the time-interval AE backward reachable set. -/
theorem LinearSys.minBackReachTimeInterval_outer (sys : LinearSys 𝕋 n) {T τ : Set ℝ}
    {U W Xend : S n}
    {ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c}
    {CZ : ConZonotope (Vec ℝ n)} {W₀ U₀ : Zonotope (Vec ℝ n)} {Zw : ℝ → Zonotope (Vec ℝ n)}
    {N : Mat ℝ q n} {t₀ tend Δt : ℝ} {η ω : ℕ} (hΔt : Δt = (tend - t₀) / ω)
    -- `Û ⊂ U`: the center trajectory `u₀(·)` and the `q` others, all admissible
    {u₀ : ℝ → Vec ℝ n} {û : Fin q → ℝ → Vec ℝ n}
    (hu₀ : ∀ s ∈ T, u₀ s ∈ construct U)
    (hmu₀ : AEStronglyMeasurable u₀ (volume.restrict T))
    (hû : ∀ i s, s ∈ T → û i s ∈ construct U)
    (hmû : ∀ i, AEStronglyMeasurable (û i) (volume.restrict T))
    -- (44), (45): the `ω` steps enclose the center trajectory's own set
    (hcov : sys.timeIntervalBackReachSetOfInputExact T U W Xend τ u₀ ⊆
      ⋃ k < ω, (sys.aux_minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k).R.construct)
    -- (46), (49): each `p_(j)` is a support value of some trajectory's own set
    (hp : ∀ j : Fin q, ∃ i : Fin q,
      ∀ x ∈ sys.timeIntervalBackReachSetOfInputExact T U W Xend τ (û i),
        HPolytope.rowLin N j x ≤ sys.aux_minBackReachP ρ CZ W₀ U₀ Zw N t₀ Δt η (ω - 1) j) :
    sys.timeIntervalBackReachSetForallExistsExact T U W Xend τ ⊆
      sys.minBackReachTimeInterval ρ CZ W₀ U₀ Zw N t₀ tend η ω := by -- --- PROOF ---
  subst hΔt
  intro x₀ hx₀
  -- (42), (55): `x₀` is in `R^∃(-τ;u*(·))` for every admissible `u*(·)`, so for `Û`'s
  have key : ∀ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) →
      AEStronglyMeasurable u (volume.restrict T) →
      x₀ ∈ sys.timeIntervalBackReachSetOfInputExact T U W Xend τ u :=
    fun u hu hmu => hx₀ u hu hmu
  -- (57): every row of `⟨N,p⟩_H` bounds one of those sets, hence `x₀`
  have hP : x₀ ∈ (HPolytope.ineqs N
      (sys.aux_minBackReachP ρ CZ W₀ U₀ Zw N t₀ ((tend - t₀) / ω) η (ω - 1))).construct := by
    refine HPolytope.mem_ineqs_iff.mpr fun j => ?_
    obtain ⟨i, hi⟩ := hp j
    exact hi x₀ (key (û i) (hû i) (hmû i))
  -- (44): the center trajectory's own set is covered by the `ω` steps
  obtain ⟨k, hk, hkx⟩ := Set.mem_iUnion₂.mp (hcov (key u₀ hu₀ hmu₀))
  -- (48): distributing the intersection over the union
  exact Set.mem_iUnion₂.mpr ⟨k, hk, hkx, hP⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
