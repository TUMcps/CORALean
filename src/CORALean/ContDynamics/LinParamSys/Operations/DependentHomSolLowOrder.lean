import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `LinParamSys.dependentHomSolLowOrder`, as CORA computes it

The part `R_lowOrder` of CORA's `linParamSys/private/priv_dependentHomSol`, the solution
after one step `r` of `ẋ = A x + u` with `A = A_c + Σᵢ pᵢ A_g⁽ⁱ⁾` and the constant input
`u = U_c + Σᵢ pᵢ U_G⁽ⁱ⁾` sharing the parameters `pᵢ ∈ [-1, 1]`, expanded to second order in
the `pᵢ`: `R_c` (order zero, and the centre of the `pᵢ²` terms), `R_g` the first-order
generators, the halved `pᵢ²` generators and the mixed `pᵢpⱼ` ones, line by line as printed.
The time orders above `A² r²` (state) and `A² r³` (input) are left to the high-order mapping
matrices, which CORA adds afterwards and which are not modelled here.

It is defined to be refuted: the second-order input terms are incomplete
(`dependentHomSolLowOrder_counterexample`, FINDINGS.md). The mixed generators are indexed
by all pairs `(i, j)`, zero unless `i < j`, where CORA lists the pairs `i < j`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `R_lowOrder = zonotope(R_c, R_g)` of `priv_dependentHomSol`, at the centre `c` of
`Rinit`, the system matrix `A_c + Σ pᵢ A_g⁽ⁱ⁾`, the input `U_c + Σ pᵢ U_G⁽ⁱ⁾` and step `r`. -/
noncomputable def LinParamSys.dependentHomSolLowOrder (Ac : Mat ℝ n n) (Ag : Fin k → Mat ℝ n n)
    (c Uc : Vec ℝ n) (UG : Fin k → Vec ℝ n) (r : ℝ) : Zonotope (Vec ℝ n) :=
  -- zero parametric order: `c + Uc r + Σ_{i=1,2} Acⁱ rⁱ/i! (c + Uc r/(i+1))`
  let R_c0 : Vec ℝ n := c + r • Uc + (r • Ac) *ᵥ (c + (r / 2) • Uc)
    + ((r ^ 2 / 2) • (Ac * Ac)) *ᵥ (c + (r / 3) • Uc)
  -- first parametric order
  let M : Mat ℝ n n := r • 1 + (r ^ 2 / 2) • Ac + (r ^ 3 / 6) • (Ac * Ac)
  let R_g1 : Fin k → Vec ℝ n := fun i =>
    (r • Ag i + (r ^ 2 / 2) • (Ac * Ag i) + (r ^ 2 / 2) • (Ag i * Ac)) *ᵥ c
      + ((r ^ 2 / 2) • Ag i + (r ^ 3 / 6) • (Ac * Ag i) + (r ^ 3 / 6) • (Ag i * Ac)) *ᵥ Uc
      + M *ᵥ UG i
  -- second parametric order, same index: `Rtmp`, half a generator and half to the centre
  let Rtmp : Fin k → Vec ℝ n := fun i =>
    ((r ^ 2 / 2) • (Ag i * Ag i)) *ᵥ c + ((r ^ 3 / 6) • Ag i) *ᵥ Uc
      + ((r ^ 3 / 6) • (Ac * Ag i + Ag i * Ac)) *ᵥ UG i
  let R_g2 : Fin k → Vec ℝ n := fun i => (1 / 2 : ℝ) • Rtmp i
  let R_c : Vec ℝ n := R_c0 + ∑ i, (1 / 2 : ℝ) • Rtmp i
  -- second parametric order, different index `i < j`
  let R_g3 : Fin k × Fin k → Vec ℝ n := fun ij =>
    if ij.1 < ij.2 then
      ((r ^ 2 / 2) • (Ag ij.1 * Ag ij.2 + Ag ij.2 * Ag ij.1)) *ᵥ c
        + ((r ^ 3 / 6) • (Ag ij.1 * Ag ij.2 + Ag ij.2 * Ag ij.1)) *ᵥ Uc
        + ((r ^ 3 / 6) • (Ac * Ag ij.1 + Ag ij.1 * Ac)) *ᵥ UG ij.2
    else 0
  ⟨k + k + k * k, R_c, Fin.append (Fin.append R_g1 R_g2) (fun l => R_g3 (finProdFinEquiv.symm l))⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
