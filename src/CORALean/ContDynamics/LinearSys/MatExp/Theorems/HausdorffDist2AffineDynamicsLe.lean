import CORALean.ContDynamics.LinearSys.MatExp.AffineTimeIntervalSolution
import CORALean.ContSet.ContSet.Theorems.IsCompactSegments
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2LinCombLe
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# [1, Prop. 1]: the affine dynamics error of eq. (22)'s time-interval enclosure

`d_H(H(τ_k), Ĥ(τ_k)) ≤ Δε^h_k(Δt,η) = 2err(C) + √γ_h‖G^{(-)}_h‖₂`, eq. (23), for the exact
tube `affineTimeIntervalSolution` and eq. (22)'s `affineTimeIntervalOuter`.

Two inclusions are hypotheses, and each is one [1] states without proving. `houter` is eq. (22)'s
soundness, which [1] cites rather than proves. `hinner` is [1]'s own inner-approximation
`comb(H(t_k),H(t_{k+1})) ⊖ B_µ ⊖ C ⊆ H(τ_k)`, stated in the Minkowski-*sum* form
`comb(H(t_k),H(t_{k+1})) ⊆ H(τ_k) ⊕ C` its bound actually uses: every point of the straight
combination is within the curvature set of the true tube.

The witness is then one triangle inequality — `err(C)` for the added curvature, `Prop. 9`'s `µ`
for `linComb`'s own enclosure error, `err(C)` again for `hinner`'s curvature — reaching eq. (23)'s
constant exactly, without [1]'s erosion step, which does not compose additively.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A zonotope's centre is one of its points, which is all the nonemptiness a Hausdorff
distance asks of it. -/
theorem aux_center_mem_construct {α : Type} [AddCommGroup α] [Module ℝ α] (Z : Zonotope α) :
    Z.c ∈ Z.construct :=
  ⟨0, fun _ => by simp, by simp⟩

/-- And the segments between two zonotopes are nonempty for the same reason. -/
theorem aux_segments_nonempty {α : Type} [AddCommGroup α] [Module ℝ α] (Z₁ Z₂ : Zonotope α) :
    (segments Z₁.construct Z₂.construct).Nonempty :=
  ⟨Z₁.c, Z₁.c, aux_center_mem_construct Z₁, Z₂.c, aux_center_mem_construct Z₂, 1,
    ⟨zero_le_one, le_refl 1⟩, by simp⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: eq. (23) bounds the distance between the exact time-interval solution of the
affine dynamics and eq. (22)'s enclosure, given [1]'s own two inclusions. -/
theorem MatExp.hausdorffDist₂_affineDynamics_le (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (Δt : ℝ) (η : ℕ)
    (hinner : segments H.construct (MatExp.affineTimePointNext A H ũ Δt).construct
      ⊆ MatExp.affineTimeIntervalSolution A H ũ Δt
        + (MatExp.curvatureEnclosure A H ũ Δt η).construct)
    (houter : MatExp.affineTimeIntervalSolution A H ũ Δt
      ⊆ (MatExp.affineTimeIntervalOuter A H ũ Δt η).construct) :
    hausdorffDist₂ (MatExp.affineTimeIntervalSolution A H ũ Δt)
        (MatExp.affineTimeIntervalOuter A H ũ Δt η).construct
      ≤ MatExp.affineDynamicsError A H ũ Δt η := by -- --- PROOF ---
  have hε := MatExp.affineDynamicsError_nonneg A H ũ Δt η
  have hCb : Bornology.IsBounded (MatExp.curvatureEnclosure A H ũ Δt η).construct :=
    Zonotope.isBounded_construct _
  have hOut : (MatExp.affineTimeIntervalOuter A H ũ Δt η).construct
      = (H.linComb (MatExp.affineTimePointNext A H ũ Δt)).construct
        + (MatExp.curvatureEnclosure A H ũ Δt η).construct := (Zonotope.plus_exact _ _).symm
  -- [1, Prop. 9] at `cp = P^u(Δt)`: `linComb`'s own enclosure error is `µ`
  have hP9 : hausdorffDist₂
      (segments H.construct (MatExp.affineTimePointNext A H ũ Δt).construct)
      ((H.linComb (MatExp.affineTimePointNext A H ũ Δt)).construct)
        ≤ Real.sqrt H.h * genOpNorm₂ (MatExp.genMinus A H Δt) :=
    Zonotope.hausdorffDist₂_linComb_le A Δt H ((MatExp.expIntegral A Δt).mulVec ũ)
  refine hausdorffDist₂_le_of_mem_dist hε ?_ ?_
  -- one side is free: the exact tube already sits inside its own enclosure
  · intro x hx
    exact ⟨x, houter hx, by rw [sub_self, norm₂_zero]; exact hε⟩
  intro y hy
  rw [hOut, Set.mem_add] at hy
  obtain ⟨ŝ, hŝ, c, hc, rfl⟩ := hy
  -- `Prop. 9`'s bound read back as a point of the exact combination
  obtain ⟨s, hs, hsd⟩ := hausdorffDist₂_exists_mem_dist_le
    (isCompact_segments H.isCompact_construct
      (MatExp.affineTimePointNext A H ũ Δt).isCompact_construct)
    (aux_segments_nonempty H (MatExp.affineTimePointNext A H ũ Δt))
    (Zonotope.isBounded_construct _)
    ⟨_, aux_center_mem_construct (H.linComb (MatExp.affineTimePointNext A H ũ Δt))⟩ hP9 hŝ
  -- and `hinner` turns that point into one of the tube, one curvature apart
  obtain ⟨x, hx, c', hc', hxeq⟩ := Set.mem_add.mp (hinner hs)
  refine ⟨x, hx, ?_⟩
  have hsplit : ŝ + c - x = (ŝ - s) + (c + c') := by rw [← hxeq]; abel
  have hcn := norm₂_le_err_of_mem hCb hc
  have hcn' := norm₂_le_err_of_mem hCb hc'
  have hsum := norm₂_add_le c c'
  rw [MatExp.affineDynamicsError]
  calc ‖ŝ + c - x‖₂ = ‖(ŝ - s) + (c + c')‖₂ := by rw [hsplit]
    _ ≤ ‖ŝ - s‖₂ + ‖c + c'‖₂ := norm₂_add_le _ _
    _ ≤ Real.sqrt H.h * genOpNorm₂ (MatExp.genMinus A H Δt)
          + 2 * err (MatExp.curvatureEnclosure A H ũ Δt η).construct := by linarith
    _ = 2 * err (MatExp.curvatureEnclosure A H ũ Δt η).construct
          + Real.sqrt H.h * genOpNorm₂ (MatExp.genMinus A H Δt) := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
