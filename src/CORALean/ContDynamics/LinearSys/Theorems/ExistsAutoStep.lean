import CORALean.ContDynamics.LinearSys.AutoTuneReach
import CORALean.ContDynamics.LinearSys.Theorems.ExistsAutoTuneDeltaT
import CORALean.ContSet.Zonotope.Real.Theorems.ExistsAutoTuneSetOrder

/-!
# `Thm. 1`: one iteration of `Alg. 2` always completes, for every `ε_max > 0`

[1, Thm. 1]'s proof is three sentences and this is all three: `Lemma 2` against eq. (37)
and `Lemma 3`/`Lemma 4` against eq. (38) give lines 5-15 a step size and a truncation
order (`exists_autoTuneDeltaT`), and "the reduction error can be set to `0` by simply
omitting the reduction" gives lines 19-22 an order (`exists_autoTuneSetOrder`). Lines
16-18 and 23-30 compute, so `autoStep` reports.

Carried, not proved, are the two budget invariants [1] maintains across the loop rather
than establishes: `ε^a_k` and `ε^r_k` are inside eq. (36)'s and eq. (35)'s shares at
`t_k`. They hold at `k = 0` (`autoInit` sets both to `0`) and are what eq. (33)/(28)'s
accumulations would have to preserve — accumulations [1] states and does not prove, and
which stay open here (see the `Prop. 2`/`Prop. 4` rows).

Not formalizable here is [1]'s word "terminates". Two reasons, one ours and one [1]'s.
Ours: the searches take `fuel` and return `Option`, so they terminate by construction.
[1]'s: even granting every iteration succeeds, nothing in [1]'s proof bounds the *number*
of iterations — see the `Thm. 1` finding on the reference page.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], the half that transfers: one iteration of `Alg. 2` is never stuck. For
every `ε_max > 0` some fuel lets lines 5-15 and lines 19-22 both report, so `autoStep`
returns the step it computes rather than `none`. -/
theorem LinearSys.exists_autoStep (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, a ≤ b → le a b = true) (X₀ U : Zonotope (Vec ℝ n))
    (s : LinearSys.AutoState n) {tend εmax ζ : ℝ} {ηmax : ℕ} (hn : 0 < n)
    (htend : s.t < tend) (htpos : 0 < tend) (hεmax : 0 < εmax) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1)
    (hεa : s.εa ≤ s.t / tend * (1 - ζ) * εmax) (hεr : s.εr ≤ s.t / tend * ζ * εmax)
    (hΔt : 0 < s.Δt) (hηmax : 1 ≤ ηmax) :
    ∃ (fuel : ℕ) (r : LinearSys.AutoState n × Zonotope (Vec ℝ n)),
      sys.autoStep le X₀ U tend εmax ζ ηmax fuel s = some r := by -- --- PROOF ---
  obtain ⟨fuel, Δt, η, hdt, hΔtpos⟩ := sys.exists_autoTuneDeltaT hle s.H U.c
    ({ h := U.h, c := 0, G := U.G } : Zonotope (Vec ℝ n)) htend htpos hεmax hζ1 hεa hΔt hηmax
  -- line 19's share is non-negative because the step it is read at is
  have hεrτ : 0 ≤ (s.t + Δt) / tend * ζ * εmax - s.εr := by
    have hdiff : (s.t + Δt) / tend * ζ * εmax - s.t / tend * ζ * εmax
        = Δt / tend * (ζ * εmax) := by field_simp; ring
    have hgain : 0 ≤ Δt / tend * (ζ * εmax) :=
      mul_nonneg (div_nonneg hΔtpos.le htpos.le) (mul_nonneg hζ0 hεmax.le)
    linarith
  obtain ⟨ρ, hρ⟩ := Zonotope.exists_autoTuneSetOrder hle
    (Zonotope.plus s.PU0 (Zonotope.mtimes (exp (s.t • toRealMat sys.A))
      (Zonotope.mtimes (MatExp.particularCoeff (toRealMat sys.A) Δt 0)
        ({ h := U.h, c := 0, G := U.G } : Zonotope (Vec ℝ n))))) hn hεrτ
  refine ⟨fuel, ?_⟩
  simp only [LinearSys.autoStep, hdt, hρ]
  exact ⟨_, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
