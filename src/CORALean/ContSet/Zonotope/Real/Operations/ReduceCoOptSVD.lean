module

public import CORALean.ContSet.Zonotope.Real.Operations.PCABasis
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis

@[expose] public section

/-!
# `Zonotope.reduceCoOptSVD`: [1, Alg. 4]

CoOptSVD, reduction to a parallelotope `(c | C)` of least volume subject to `Z ⊆ (c | C)`, with
`C = U S Vᵀ`. One `let` per line of the listing: `C₀` by PCA, [1, Alg. 2] over every generator
(`C₀ = U₀ diag(S₀)`, whose decomposition PCA's output already is: no SVD routine is needed);
lines 3-5, the constrained minimization of eq. 11 subject to eq. 13, handed to MATLAB's `fmincon`,
are `opt`, an argument, from the initial triple to a candidate `(U, S, V)`; `C = U diag(S) Vᵀ`;
and `(c | C)` only when the candidate satisfies eq. 13 — `U`, `V` orthogonal, every `sᵢᵢ ≠ 0`,
`Σⱼ |(V diag(1/s) Uᵀ G)ᵢⱼ| ≤ 1` — which a solver's return need not; otherwise the PCA
initialisation, which encloses `Z` regardless.

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
/-- [1, Alg. 4]: PCA's `C₀ = U₀ diag(S₀)`, the solver's `(U, S, V)`, and `(c | U diag(S) Vᵀ)` when
that satisfies eq. 13, PCA's parallelotope when not. -/
noncomputable def Zonotope.reduceCoOptSVD (Z : Zonotope (Vec ℝ n))
    (opt : Mat ℝ n n × Vec ℝ n × Mat ℝ n n → Mat ℝ n n × Vec ℝ n × Mat ℝ n n) :
    Zonotope (Vec ℝ n) :=
  -- 1. initialize `C` using Algorithm 2: the principal axes `U₀` and the box radii `S₀`
  let part := (Partition.split 0 Z.h).reindex (finCongr (zero_add Z.h)).symm
  let U₀ := Z.pcaBasis part
  let S₀ : Vec ℝ n := fun k => ∑ l, |(U₀⁻¹ *ᵥ Z.G l) k|
  -- 2. decomposition `C = U S Vᵀ`, here `U₀ diag(S₀) Iᵀ`; 3-5. minimize (11) subject to (13)
  let USV := opt (U₀, S₀, 1)
  -- 6. compute `U S Vᵀ = C`
  let C := USV.1 * Matrix.diagonal USV.2.1 * USV.2.2ᵀ
  -- 7. `Z_red = (c | C)`, when the solver's candidate meets (13); else the initialisation
  if USV.1ᵀ * USV.1 = 1 ∧ USV.2.2ᵀ * USV.2.2 = 1 ∧ (∀ i, USV.2.1 i ≠ 0)
      ∧ ∀ i, ∑ j, |((USV.2.2 * Matrix.diagonal USV.2.1⁻¹ * USV.1ᵀ) *ᵥ Z.G j) i| ≤ 1 then
    ⟨n, Z.c, fun k i => C i k⟩
  else Z.reduceByBasis part U₀

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
