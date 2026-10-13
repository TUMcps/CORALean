module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `LinParamSys.dependentLowOrder`, CORA's `R_lowOrder` corrected

CORA's `R_lowOrder` of `linParamSys/private/priv_dependentHomSol` is meant to hold the time
orders up to `A²` of one step `r` of `ẋ = A x + u` from the centre `c` of `Rinit`,
`(I + A r + A² r²/2) c + (I r + A r²/2 + A² r³/6) u`, with `A = A_c + Σ pᵢ A_g⁽ⁱ⁾` and
`u = U_c + Σ pᵢ U_G⁽ⁱ⁾` sharing `p ∈ [-1, 1]ᵏ`: a cubic in `p`, one generator per monomial.
CORA's code (`dependentHomSolLowOrder`, refuted) drops terms; here order zero and one are as
CORA prints them, and the lines marked in the code are corrected or added: the `pᵢ²` block
(`A_g⁽ⁱ⁾² r³/6 U_c` for CORA's `A_g⁽ⁱ⁾ r³/6 U_c`, `A_g⁽ⁱ⁾ U_G⁽ⁱ⁾ r²/2` added), the `pᵢpⱼ`, `i < j`,
block (`A_g U_G r²/2` both ways and the second mixed half added), and the `pᵢpⱼpₗ` block
`A_g⁽ⁱ⁾ A_g⁽ʲ⁾ U_G⁽ˡ⁾ r³/6`, which CORA has none of.

Each monomial is its own generator, the dependency between monomials dropped, as in CORA's;
the squares keep CORA's half-centre, half-generator split. Mixed generators are indexed by all
pairs, zero unless `i < j`, triples by all ordered triples.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `R_lowOrder = zonotope(R_c, R_g)` of `priv_dependentHomSol`, corrected: every
monomial of the time orders up to `A²` in the parameters, at the centre `c` of `Rinit`, the
system matrix `A_c + Σ pᵢ A_g⁽ⁱ⁾`, the input `U_c + Σ pᵢ U_G⁽ⁱ⁾` and step `r`. -/
noncomputable def LinParamSys.dependentLowOrder (Ac : Mat ℝ n n) (Ag : Fin k → Mat ℝ n n)
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
    ((r ^ 2 / 2) • (Ag i * Ag i)) *ᵥ c
      + ((r ^ 3 / 6) • (Ag i * Ag i)) *ᵥ Uc                        -- corrected: `Ag⁽ⁱ⁾²`
      + ((r ^ 2 / 2) • Ag i) *ᵥ UG i                               -- added
      + ((r ^ 3 / 6) • (Ac * Ag i + Ag i * Ac)) *ᵥ UG i
  let R_g2 : Fin k → Vec ℝ n := fun i => (1 / 2 : ℝ) • Rtmp i
  let R_c : Vec ℝ n := R_c0 + ∑ i, (1 / 2 : ℝ) • Rtmp i
  -- second parametric order, different index `i < j`
  let R_g3 : Fin k × Fin k → Vec ℝ n := fun ij =>
    if ij.1 < ij.2 then
      ((r ^ 2 / 2) • (Ag ij.1 * Ag ij.2 + Ag ij.2 * Ag ij.1)) *ᵥ c
        + ((r ^ 3 / 6) • (Ag ij.1 * Ag ij.2 + Ag ij.2 * Ag ij.1)) *ᵥ Uc
        + ((r ^ 2 / 2) • Ag ij.1) *ᵥ UG ij.2 + ((r ^ 2 / 2) • Ag ij.2) *ᵥ UG ij.1   -- added
        + ((r ^ 3 / 6) • (Ac * Ag ij.1 + Ag ij.1 * Ac)) *ᵥ UG ij.2
        + ((r ^ 3 / 6) • (Ac * Ag ij.2 + Ag ij.2 * Ac)) *ᵥ UG ij.1               -- added
    else 0
  -- third parametric order, every ordered triple: added
  let R_g4 : Fin k × Fin k × Fin k → Vec ℝ n := fun ijl =>
    ((r ^ 3 / 6) • (Ag ijl.1 * Ag ijl.2.1)) *ᵥ UG ijl.2.2
  let e3 : Fin (k * (k * k)) ≃ Fin k × Fin k × Fin k :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)
  ⟨k + k + k * k + k * (k * k), R_c,
    Fin.append (Fin.append (Fin.append R_g1 R_g2) (fun l => R_g3 (finProdFinEquiv.symm l)))
      (fun l => R_g4 (e3 l))⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
