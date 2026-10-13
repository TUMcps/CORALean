module

public import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
public import CORALean.ContSet.Zonotope.Real.Operations.LineClKeep
public import CORALean.ContSet.Zonotope.Real.Operations.LineClVolume
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

/-!
# `Zonotope.lineClBasis`

The transformation matrix of line clustering [1, Alg. 3], on the generators a partition
drops, as CORA reduces them [2]. One named step per printed line. Where the listing is
open:

* Line 2 is random; run `t` instead starts at the `n` dropped generators from index `t`,
  cyclically. Eq. 5 is squared (same ranking); a generator joins the first nearest line.
* Eq. 6's dominant left singular vector is the eigenvector of `G_k G_kᵀ` of largest
  eigenvalue, found by sorting. The loop stops at `‖L − L_old‖_F ≤ ξ` or after `fuel` steps.
* Line 12 is not carried out: `P · IH(P⁻¹ Z)` ignores positive column scalings.
* `L⁻¹` needs an invertible `L`: singular candidates are skipped (`lineClKeep`), and with
  no invertible run the answer is `1`, which boxes along the axes.

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
* [2] `contSet/@zonotope/private/priv_reduceCluster.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped Classical

variable {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Eq. 5 squared, for the line through `l` and the generator `g`. -/
noncomputable def Zonotope.aux_lineClDist (l g : Vec ℝ n) : ℝ :=
  ∑ i, (g i - (∑ j, l j * g j) / (∑ j, l j ^ 2) * l i) ^ 2

/-- `G_k G_kᵀ`, for the generators of cluster `k` of `L`: those whose first
nearest line is the `k`-th (lines 5-7). -/
noncomputable def Zonotope.aux_lineClScatter (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (L : Mat ℝ n n) (k : Fin n) : Mat ℝ n n :=
  Matrix.of fun i j => ∑ l, if (∀ m, Zonotope.aux_lineClDist (fun a => L a k) (Z.G (part.right l))
        ≤ Zonotope.aux_lineClDist (fun a => L a m) (Z.G (part.right l))) ∧
      (∀ m < k, Zonotope.aux_lineClDist (fun a => L a k) (Z.G (part.right l))
        < Zonotope.aux_lineClDist (fun a => L a m) (Z.G (part.right l)))
    then Z.G (part.right l) i * Z.G (part.right l) j else 0

/-- Eq. 6: the eigenvector of largest eigenvalue of a symmetric matrix, the first
column of `U_k`. (The axis `k` stands in where the matrix is not symmetric, which
`aux_lineClScatter` never is.) -/
noncomputable def Zonotope.aux_lineClAxis (A : Mat ℝ n n) (k : Fin n) : Vec ℝ n :=
  if hA : A.IsHermitian then
    fun i => (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) i
      (Tuple.sort (fun j => -hA.eigenvalues j) ⟨0, k.pos⟩)
  else Pi.single k 1

/-- Lines 8-10: every representative `l_k` replaced by its cluster's axis. -/
noncomputable def Zonotope.aux_lineClStep (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (L : Mat ℝ n n) : Mat ℝ n n :=
  Matrix.of fun i k => Zonotope.aux_lineClAxis (Z.aux_lineClScatter part L k) k i

/-- Lines 3-11: assign and update until `‖L − L_old‖ ≤ ξ`, at most `fuel` times. -/
noncomputable def Zonotope.aux_lineClConverge (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (ξ : ℝ) : ℕ → Mat ℝ n n → Mat ℝ n n
  | 0, Lold => Lold
  | fuel + 1, Lold =>
    let L := Z.aux_lineClStep part Lold                            -- lines 4-9
    if ∑ i, ∑ k, (L i k - Lold i k) ^ 2 ≤ ξ ^ 2 then L
    else Zonotope.aux_lineClConverge Z part ξ fuel L

/-- Line 2 of run `t`: `n` of the dropped generators, from index `t` on. -/
noncomputable def Zonotope.aux_lineClInit (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (t : ℕ) : Mat ℝ n n :=
  Matrix.of fun i k =>
    if h : 0 < r then Z.G (part.right ⟨(t + k) % r, Nat.mod_lt _ h⟩) i else 0

/-- One pass of the `for` loop's body (lines 2-13): the converged `L` of run `t`. -/
noncomputable def Zonotope.aux_lineClRun (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (ξ : ℝ) (fuel t : ℕ) : Mat ℝ n n :=
  let L₀ := Z.aux_lineClInit part t                                 -- line 2
  Z.aux_lineClConverge part ξ fuel L₀                               -- lines 3-11


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the `L_min` of the best of `runs` runs, by the volume of eq. 7; `1`
if no run gave an invertible matrix. -/
noncomputable def Zonotope.lineClBasis (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (ξ : ℝ) (fuel runs : ℕ) : Mat ℝ n n :=
  let Lmin := (List.range runs).foldl                               -- lines 1, 14-18
    (fun best t => Zonotope.lineClKeep (Z.lineClVolume part) best (Z.aux_lineClRun part ξ fuel t))
    none
  Lmin.getD 1                                                       -- line 19


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
