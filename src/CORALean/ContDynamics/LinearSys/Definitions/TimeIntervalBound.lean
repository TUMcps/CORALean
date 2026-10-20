module

public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalReachSetExactSubsetSetLinCombSum
public import CORALean.ContSet.ContSet.Operations.SupportBoundSetLinComb
public import CORALean.Global.SupportFunction.Composition

@[expose] public section

/-!
# A support bound over a whole step, not a time point

[1, Alg. 1 (upper bounds)]'s line 13: `ρ(R̂(τ_k), ℓ) ← max{ρ(H(t_k), ℓ), ρ(H(t_{k+1}), ℓ)} +
ρ(C, d_k) + ρ(P̂_U(t_{k+1}), ℓ)`, term for term: `SupportBound.setLinComb` for the `max`,
`SupportBound.image` for the direction pulled back through `e^{Ar}`, `SupportBound.add` for
the `+`s, `SupportBound.mono` to cross `timeIntervalReachSetExact_subset_setLinComb_sum`.
The three bounds are hypotheses: any representation that answers `SupportBound` on `R₀`, on the
correction term and on the particular solution may be handed in.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `r` – step length
* `m` – Taylor order offset
* `b₀` – support bound on the initial set
* `bC` – support bound on the correction term
* `bP` – support bound on the particular solution
* `c` – direction

## Hypotheses
* `hr` – step length positive
* `hT` – step lies in the time domain
* `hε` – scaled norm small enough for the Taylor order
* `hconv` – input set convex
* `hclosed` – input set closed
* `hbdd` – input set bounded
* `hRconv` – remainder image convex
* `hRclosed` – remainder image closed
* `hRbdd` – remainder image bounded
* `h0` – origin in the input set

## Output
* support bound on the time-interval reachable set along the direction
## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Bounds on `R₀`, on the correction term and on the particular solution, in
every direction, give a bound on the time-interval reachable set over one step
— no set built, and `timeIntervalReachSetExact` named only in the conclusion. -/
noncomputable def LinearSys.timeIntervalBound (sys : LinearSys 𝕋 n) {T : Set ℝ} (R₀ U : S n)
    {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U)
    (b₀ : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct R₀) d)
    (bC : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, SupportBound (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.correctionMatrix (toRealMat sys.A) r (m + 2)) R₀)) d)
    (bP : ∀ d : Vec ℝ n →ₗ[ℝ] ℝ,
      SupportBound (construct (sys.inputSolution r (m + 2) U)) d)
    (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound (sys.timeIntervalReachSetExact T R₀ U r) c :=
  (((b₀ c).setLinComb (SupportBound.image (mulVecLin (exp (r • toRealMat sys.A)))
      (b₀ (c.comp (mulVecLin (exp (r • toRealMat sys.A))))))).add (bC c)).add (bP c) |>.mono
    (sys.timeIntervalReachSetExact_subset_setLinComb_sum R₀ U hr hT hε hconv hclosed hbdd hRconv
      hRclosed hRbdd h0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
