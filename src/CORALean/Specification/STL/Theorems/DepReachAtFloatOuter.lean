module

public import CORALean.Specification.STL.Operations.DepReachAtFloat
public import CORALean.Specification.STL.Theorems.DepReachInitFloatOuter
public import CORALean.Specification.STL.Theorems.DepReachStepFloatOuter

@[expose] public section

/-!
# The float state after `i` steps encloses the real one

By induction on `i` over [1, Alg. 1]: `depReachInitFloat_outer` at zero and
`depReachStepFloat_outer` for each pass. The set standing for `C_i` is the exact products of the
first state, mapped `i` times by `e^{AΔt}`.
## Inputs
* `A` – float dynamics matrix
* `Δt` – float time step
* `η` – Taylor order of the matrix exponential
* `csR` – real constants
* `csF` – float constants
* `X₀r` – real initial set
* `X₀f` – float initial set
* `i` – step index

## Hypotheses
* `hε` – the float norm bound is small enough for the Taylor order
* `hX` – the real initial set lies inside the float one
* `hcs` – the float constants enclose the real ones

## Conclusion
* the float state after `i` steps encloses the real one, with the mapped exact products
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Float Float.FloatOps Float.SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float state at `t_i` encloses the real one, with `C_i` as the mapped exact products. -/
theorem STL.depReachAtFloat_outer (A : Mat 𝕋 n n) (Δt : 𝕋) {η : ℕ}
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((η : ℝ) + 2) ≤ 1 / 2) {csR : STL.DepReachConsts n} {csF : STL.DepReachConstsFloat 𝕋 n}
    {X₀r : Real.Zonotope (Vec ℝ n)} {X₀f : Float.Zonotope (Vec 𝕋 n)}
    (hX : X₀r.construct ⊆ X₀f.construct) (hcs : csF.Encloses csR) (i : ℕ) : -- --- CONCL ---
    (STL.depReachAtFloat A Δt η csF X₀f i).Encloses
      (STL.depReachAt (toRealMat A) (toReal Δt) csR X₀r i)
      ((exp (toReal Δt • toRealMat A) *ᵥ ·)^[i] ''
        {y | ∃ M ∈ csR.F.construct, ∃ x ∈ X₀r.construct, ∃ M' ∈ csR.G.construct,
          y = M *ᵥ x + M' *ᵥ csR.ũ}) := by -- --- PROOF ---
  induction i with
  | zero =>
    rw [Function.iterate_zero, Set.image_id]
    exact STL.depReachInitFloat_outer hX hcs
  | succ i ih =>
    have := STL.depReachStepFloat_outer A Δt hε hcs ih
    rwa [Function.iterate_succ', Set.image_comp]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
