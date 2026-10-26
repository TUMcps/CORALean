module

public import CORALean.ContDynamics.OutputEq.Operations.Eval
public import CORALean.ContSet.ContSet.Theorems.HausdorffDistImageLe
public import CORALean.ContSet.ContSet.Theorems.HausdorffDistAddLe
public import CORALean.Global.EuclideanHausdorffDist

@[expose] public section

/-!
# The output-set error a state-space error induces, at the Euclidean norm

[1, Prop. 5]: given `d_H(R(τ_k), R̂(τ_k)) ≤ ε` for the reachable set, the output set has error
`d_H(Y(τ_k), Ŷ(τ_k)) ≤ ε · ‖C‖₂`, `‖C‖₂` the largest singular value. [1]'s eq. (43) is
`Set.image2 out.eval` here: `out.eval x u = C *ᵥ x + D *ᵥ u + k`. Stated for arbitrary compact
nonempty `X1 X2` and one common `V`: nothing about how `X2` over-approximates `X1` is used.
`‖C‖₂` is not `‖mulVecLin (toRealMat out.C)‖`: `Vec ℝ n` carries the supremum norm, so that
operator norm is the largest absolute row sum. Reading `C` in the paper's norm needs it
conjugated through `toEuclidean`, `aux_toEuclideanCLM`.

## Inputs
* `out` – output equation
* `X1` – first state set
* `X2` – second state set
* `V` – input set

## Hypotheses
* `hX1` – first set compact
* `hX1ne` – first set nonempty
* `hX2` – second set compact
* `hX2ne` – second set nonempty

## Conclusion
* the output sets are as close as the state sets scaled by the matrix norm

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Pointwise

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same matrix action, conjugated to act between the `EuclideanSpace` copies of `Vec ℝ n` and
`Vec ℝ r`, so its own operator norm is `Def. 5`'s `‖·‖₂` rather than `Vec`'s supremum one. -/
noncomputable def aux_toEuclideanCLM (M : Mat ℝ r n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
  toEuclidean.toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap (mulVecLin M)).comp toEuclidean.symm.toContinuousLinearMap)

@[simp] private theorem aux_toEuclideanCLM_apply (M : Mat ℝ r n) (x : Vec ℝ n) :
    aux_toEuclideanCLM M (toEuclidean x) = toEuclidean (mulVecLin M x) := by
  simp [aux_toEuclideanCLM]

/-- `toEuclidean`'s image of a matrix's image is the conjugated map's image of `toEuclidean`'s. -/
private theorem aux_toEuclidean_image_mulVecLin (M : Mat ℝ r n) (X : Set (Vec ℝ n)) :
    toEuclidean '' (mulVecLin M '' X) = aux_toEuclideanCLM M '' (toEuclidean '' X) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun x _ => (aux_toEuclideanCLM_apply M x).symm

/-- `hausdorffDist_image_le`, read at `‖·‖₂` on both the state and the output side. -/
private theorem aux_hausdorffDist₂_mulVecLin_le (M : Mat ℝ r n) {X1 X2 : Set (Vec ℝ n)}
    (hX1 : IsCompact X1) (hX1ne : X1.Nonempty) (hX2 : IsCompact X2) (hX2ne : X2.Nonempty) :
    hausdorffDist₂ (mulVecLin M '' X1) (mulVecLin M '' X2)
      ≤ ‖aux_toEuclideanCLM M‖ * hausdorffDist₂ X1 X2 := by
  rw [hausdorffDist₂, aux_toEuclidean_image_mulVecLin, aux_toEuclidean_image_mulVecLin]
  exact hausdorffDist_image_le (aux_toEuclideanCLM M)
    (hX1.image toEuclidean.continuous) (hX1ne.image _)
    (hX2.image toEuclidean.continuous) (hX2ne.image _)

/-- `hausdorffDist_add_le`, read at `‖·‖₂`: a fixed set added to both sides cannot move them
apart, whichever set that is. -/
private theorem aux_hausdorffDist₂_add_le {S : Set (Vec ℝ r)} {V W : Set (Vec ℝ r)}
    (hV : IsCompact V) (hVne : V.Nonempty) (hW : IsCompact W) (hWne : W.Nonempty) :
    hausdorffDist₂ (S + V) (S + W) ≤ hausdorffDist₂ V W := by
  rw [hausdorffDist₂, hausdorffDist₂, Set.image_add, Set.image_add]
  exact hausdorffDist_add_le (hV.image toEuclidean.continuous) (hVne.image _)
    (hW.image toEuclidean.continuous) (hWne.image _)

/-- [1]'s eq. (43): the output map splits into `C`'s part and the part `D` and `k` make, added. -/
private theorem aux_image2_eval_eq_add (out : OutputEq 𝕋 n m r) (X : Set (Vec ℝ n))
    (V : Set (Vec ℝ m)) : -- --- CONCL ---
    Set.image2 out.eval X V = mulVecLin (toRealMat out.C) '' X
      + (fun u => toRealMat out.D *ᵥ u + toRealVec out.k) '' V := by -- --- PROOF ---
  ext y
  simp only [Set.mem_image2, Set.mem_add, Set.mem_image, OutputEq.eval]
  constructor
  · rintro ⟨x, hx, u, hu, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨u, hu, rfl⟩, (add_assoc _ _ _).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨x, hx, u, hu, add_assoc _ _ _⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 5]: an error in the reachable set carries over to the output set, scaled by `‖C‖₂`
(`aux_toEuclideanCLM`'s operator norm). `V` is the same input/disturbance set on both sides,
matching how `WV + q` is read off `Y` and `Ŷ` alike in [1]'s proof. -/
theorem OutputEq.hausdorffDist₂_eval_le (out : OutputEq 𝕋 n m r) {X1 X2 : Set (Vec ℝ n)}
    (hX1 : IsCompact X1) (hX1ne : X1.Nonempty) (hX2 : IsCompact X2) (hX2ne : X2.Nonempty)
    (V : Set (Vec ℝ m)) : -- --- CONCL ---
    hausdorffDist₂ (Set.image2 out.eval X1 V) (Set.image2 out.eval X2 V)
      ≤ ‖aux_toEuclideanCLM (toRealMat out.C)‖ * hausdorffDist₂ X1 X2 := by -- --- PROOF ---
  have hC1 : IsCompact (mulVecLin (toRealMat out.C) '' X1) :=
    hX1.image (mulVecLin (toRealMat out.C)).continuous_of_finiteDimensional
  have hC2 : IsCompact (mulVecLin (toRealMat out.C) '' X2) :=
    hX2.image (mulVecLin (toRealMat out.C)).continuous_of_finiteDimensional
  calc hausdorffDist₂ (Set.image2 out.eval X1 V) (Set.image2 out.eval X2 V)
      = hausdorffDist₂
          ((fun u => toRealMat out.D *ᵥ u + toRealVec out.k) '' V
            + mulVecLin (toRealMat out.C) '' X1)
          ((fun u => toRealMat out.D *ᵥ u + toRealVec out.k) '' V
            + mulVecLin (toRealMat out.C) '' X2) := by
        rw [aux_image2_eval_eq_add, aux_image2_eval_eq_add,
          add_comm (mulVecLin (toRealMat out.C) '' X1),
          add_comm (mulVecLin (toRealMat out.C) '' X2)]
    _ ≤ hausdorffDist₂ (mulVecLin (toRealMat out.C) '' X1) (mulVecLin (toRealMat out.C) '' X2) :=
        aux_hausdorffDist₂_add_le hC1 (hX1ne.image _) hC2 (hX2ne.image _)
    _ ≤ ‖aux_toEuclideanCLM (toRealMat out.C)‖ * hausdorffDist₂ X1 X2 :=
        aux_hausdorffDist₂_mulVecLin_le _ hX1 hX1ne hX2 hX2ne

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
