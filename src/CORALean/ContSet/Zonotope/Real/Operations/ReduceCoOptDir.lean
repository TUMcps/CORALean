module

public import CORALean.ContSet.Zonotope.Real.Operations.PCABasis
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis

@[expose] public section

/-!
# `Zonotope.reduceCoOptDir`: CoOpt_dir of [1, Alg. 4]

Direct constrained optimization (Sec. III-D of [1]), the variant [1, Alg. 4] refines: a
parallelotope `(c | C)` minimizing `|det C|` (eq. 8) subject to `Σⱼ |(C⁻¹G)ᵢⱼ| ≤ 1` (eq. 10),
started from PCA's `C₀ = U₀ diag(S₀)` ([1, Alg. 2] over every generator). The minimization is
MATLAB's `fmincon` in [1] and an argument `opt` here; its candidate is kept when it is
invertible — which eq. 10's `C⁻¹` presumes — and satisfies eq. 10, and PCA's parallelotope is
returned otherwise.

## References

* [1] [A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of Zonotopes". 2017
      IEEE 56th Annual Conference on Decision and Control (CDC),
      2017.](../../../../../../references/2017/kopetzki-cdc-order-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- CoOpt_dir of [1, Alg. 4] without its SVD: PCA's `C₀`, the solver's `C`, and `(c | C)` when
`C` is invertible and meets eq. 10, PCA's parallelotope when not. -/
noncomputable def Zonotope.reduceCoOptDir (Z : Zonotope (Vec ℝ n))
    (opt : Mat ℝ n n → Mat ℝ n n) : Zonotope (Vec ℝ n) :=
  -- 1. initialize `C` using Algorithm 2: the principal axes `U₀` and the box radii `S₀`
  let part := (Partition.split 0 Z.h).reindex (finCongr (zero_add Z.h)).symm
  let U₀ := Z.pcaBasis part
  let S₀ : Vec ℝ n := fun k => ∑ l, |(U₀⁻¹ *ᵥ Z.G l) k|
  let C₀ := U₀ * Matrix.diagonal S₀
  -- 4. minimize `|det C|` (eq. 8) subject to (10); no SVD, so lines 2 and 6 fall away
  let C := opt C₀
  -- 7. `Z_red = (c | C)`, when the solver's candidate meets (10); else the initialisation
  if IsUnit C.det ∧ ∀ i, ∑ j, |(C⁻¹ *ᵥ Z.G j) i| ≤ 1 then ⟨n, Z.c, fun k i => C i k⟩
  else Z.reduceByBasis part U₀

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
