module

public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# A row of `G' = [G, c - d]`

`[1, Eq. 12]`: the functional `(α, t) ↦ λⱼᵀ(G α + t (c - d))`, the `j`-th row of `Λ G'`,
on `E × ℝ` with the `ℓ_p` combination of the two norms, which on `E = ℓ_p^m` is `ℓ_p^{m+1}`.
Its operator norm is `‖G'ᵀ λⱼ‖_{p*}`.

## Inputs
* `p` – `ℝ≥0∞`
* `G` – linear map
* `c` – center of length `n`
* `d` – direction of length `n`
* `Λ` – `s × n` matrix
* `j` – index below `s`

## Output
* the row `j` of `Λ` applied to `G' = [G, c - d]`, a functional on `E × ℝ`

## References

* [1] [A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope
      and Ellipsotope Containment Problems". 2024 European Control Conference (ECC),
      2024.](../../../../../../references/2024/kulmburg-ecc-zonotope-ellipsotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ENNReal

variable {n s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The row `j` of `Λ` applied to `G' = [G, c - d]`, a functional on `E × ℝ`. -/
noncomputable def HPolytope.extendedRow (p : ℝ≥0∞) [Fact (1 ≤ p)] (G : E →ₗ[ℝ] Vec ℝ n)
    (c d : Vec ℝ n) (Λ : Mat ℝ s n) (j : Fin s) : WithLp p (E × ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (Λ *ᵥ (G x.fst + x.snd • (c - d))) j
      map_add' := fun x y => by
        simp [mulVec_add, add_smul, add_add_add_comm]
      map_smul' := fun a x => by
        simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, mulVec_add, mulVec_smul,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
