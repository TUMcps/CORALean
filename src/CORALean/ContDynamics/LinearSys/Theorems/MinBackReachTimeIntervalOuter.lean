import CORALean.ContDynamics.LinearSys.Definitions.IntegralTimeIntervalBackReachSetForallExists
import CORALean.ContDynamics.LinearSys.Definitions.IntegralTimeIntervalBackReachSetOfInput
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachTimeInterval
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff

/-!
# `Thm. 1`: what `Alg. 1` returns encloses the minimal set over `τ`

[1, Thm. 1] holds [1, Alg. 1] to its claim: `R^{∀∃}(-τ)` sits inside the union of
the `ω` steps' sets, each cut by `⟨N,p⟩_H`. Three of the theorem's four moves are
proved outright — restricting `∀u(·)∈U` to the finite `Û`, enclosing each
trajectory's own set by the halfspaces, and distributing the intersection over
the union. The fourth, that the propagated sets and support values really do
enclose, is what the paper imports from the standard propagation for (42), (43)
and (44); it is `hcov` and `hp` here, stated against `Alg. 1`'s own outputs.

`⊆`, not `=`: [1, (45)] claims an outer approximation and nothing more.

The sets are the Carathéodory ones. Under `PerturbedTrajectory` the left-hand
side is empty whenever `U` holds two points, so the statement would be true and
empty — see `integralTimeIntervalBackReachSetForallExists`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar MeasureTheory

variable {n q : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `Û = {u₀} ∪ {û j}` inside `U`, `Alg. 1`'s union of cut steps encloses
the time-interval minimal backward reachable set. -/
theorem LinearSys.minBackReachTimeInterval_outer (sys : LinearSys 𝕋 n) {T τ : Set ℝ}
    {U W Xend : S n}
    {ρ : ∀ (cZ : ConZonotope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound cZ.construct c}
    {CZ : ConZonotope (Vec ℝ n)} {W₀ U₀ : Zonotope (Vec ℝ n)} {Zw : ℝ → Zonotope (Vec ℝ n)}
    {N : Mat ℝ q n} {t₀ tend Δt : ℝ} {η ω : ℕ} (hΔt : Δt = (tend - t₀) / ω)
    -- `Û ⊂ U`: the centre trajectory `u₀(·)` and the `q` others, all admissible
    {u₀ : ℝ → Vec ℝ n} {û : Fin q → ℝ → Vec ℝ n}
    (hu₀ : ∀ s ∈ T, u₀ s ∈ construct U)
    (hmu₀ : AEStronglyMeasurable u₀ (volume.restrict T))
    (hû : ∀ i s, s ∈ T → û i s ∈ construct U)
    (hmû : ∀ i, AEStronglyMeasurable (û i) (volume.restrict T))
    -- (42), (43): the `ω` steps enclose the centre trajectory's own set
    (hcov : sys.integralTimeIntervalBackReachSetOfInput T U W Xend τ u₀ ⊆
      ⋃ k < ω, (sys.minBackReachRun CZ W₀ U₀ Zw t₀ Δt η k).R.construct)
    -- (44), (46): each `p_(j)` is a support value of some trajectory's own set
    (hp : ∀ j : Fin q, ∃ i : Fin q,
      ∀ x ∈ sys.integralTimeIntervalBackReachSetOfInput T U W Xend τ (û i),
        HPolytope.rowLin N j x ≤ sys.minBackReachP ρ CZ W₀ U₀ Zw N t₀ Δt η (ω - 1) j) :
    sys.integralTimeIntervalBackReachSetForallExists T U W Xend τ ⊆
      sys.minBackReachTimeInterval ρ CZ W₀ U₀ Zw N t₀ tend η ω := by -- --- PROOF ---
  subst hΔt
  intro x₀ hx₀
  -- (40), (52): `x₀` is in `R^∃(-τ;u*(·))` for every admissible `u*(·)`, so for `Û`'s
  have key : ∀ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) →
      AEStronglyMeasurable u (volume.restrict T) →
      x₀ ∈ sys.integralTimeIntervalBackReachSetOfInput T U W Xend τ u :=
    fun u hu hmu => hx₀ u hu hmu
  -- (54): every row of `⟨N,p⟩_H` bounds one of those sets, hence `x₀`
  have hP : x₀ ∈ (HPolytope.ineqs N
      (sys.minBackReachP ρ CZ W₀ U₀ Zw N t₀ ((tend - t₀) / ω) η (ω - 1))).construct := by
    refine HPolytope.mem_ineqs_iff.mpr fun j => ?_
    obtain ⟨i, hi⟩ := hp j
    exact hi x₀ (key (û i) (hû i) (hmû i))
  -- (42): the centre trajectory's own set is covered by the `ω` steps
  obtain ⟨k, hk, hkx⟩ := Set.mem_iUnion₂.mp (hcov (key u₀ hu₀ hmu₀))
  -- (45): distributing the intersection over the union
  exact Set.mem_iUnion₂.mpr ⟨k, hk, hkx, hP⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
