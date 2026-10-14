module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulLe
public import CORALean.ContSet.ContSet.Theorems.ConvexHullUnionEqSetLinComb
public import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2LinCombLe
public import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.Global.EuclideanNorm
public import CORALean.Specification.STL.Operations.DepReachConstsOf
public import CORALean.Specification.STL.Theorems.DepReachAtHh

@[expose] public section

/-!
# [1, Prop. 5]: the convex hull enclosure converges

The difference between the exact convex hull `conv(H(t_i), H(t_{i+1}))` of Eq. (5) and its
enclosure by Eq. (8), `Zonotope.linComb`, tends to `0` as `Δt → 0`. "The difference" is the
Hausdorff distance in the Euclidean norm (`hausdorffDist₂`); `‖·‖₂` is not the sup norm that `Vec`
carries. It is bounded by `√γ_x ‖(e^{AΔt} - I) G_i‖₂` (`Zonotope.hausdorffDist₂_linComb_le`), where
the generators of `H(t_i)` are those of `X₀` mapped by `e^{iAΔt}`, so that the bound is at most
`√γ_x γ_x √n ‖e^{AΔt} - I‖ e^{T‖A‖} Σ_k ‖G_{x,k}‖` for all steps `iΔt ≤ T`, and `e^{AΔt} → I`.
The statement is uniform over the steps `i` up to a fixed final time `T`, with `H(t_i)` the
homogeneous solution of the algorithm itself, not a set fixed while `Δt` varies.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Adding the point `w` is shifting the centre by `w`. -/
theorem aux_plus_ofPoint_eq_shift (Z : Zonotope (Vec ℝ n)) (w : Vec ℝ n) :
    Z.plus (Zonotope.ofPoint w) = Z.shift (-w) := by -- --- PROOF ---
  obtain ⟨h, c, G⟩ := Z
  simp only [Zonotope.plus, Zonotope.shift, Zonotope.ofPoint, sub_neg_eq_add]
  congr 1
  funext j
  exact Fin.append_left G Fin.elim0 j

/-- The generators of `H(t_i)` are those of `X₀` mapped by `e^{iAΔt}`. -/
theorem aux_depReachAt_H_G (A : Mat ℝ n n) (Δt : ℝ) (cs : STL.DepReachConsts n)
    (X₀ : Zonotope (Vec ℝ n)) (i : ℕ) (j : Fin (STL.depReachAt A Δt cs X₀ i).H.h) :
    ∃ k : Fin X₀.h,
      (STL.depReachAt A Δt cs X₀ i).H.G j = (exp (Δt • A) ^ i) *ᵥ X₀.G k := by -- --- PROOF ---
  induction i with
  | zero => exact ⟨j, by simp [STL.depReachAt, STL.depReachInit]⟩
  | succ i ih =>
    obtain ⟨k, hk⟩ := ih j
    refine ⟨k, ?_⟩
    have : (STL.depReachAt A Δt cs X₀ (i + 1)).H.G j
        = exp (Δt • A) *ᵥ (STL.depReachAt A Δt cs X₀ i).H.G j :=
      Fin.append_left (fun j => exp (Δt • A) *ᵥ (STL.depReachAt A Δt cs X₀ i).H.G j) Fin.elim0 j
    rw [this, hk, Matrix.mulVec_mulVec, ← pow_succ']


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.tendsto_depReach_linComb_hausdorff_zero (A : Mat ℝ n n) (B : Mat ℝ n m)
    (X₀ : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (κ : ℕ) (T : ℝ) :
    ∀ ε > 0, ∀ᶠ Δt in 𝓝[>] (0 : ℝ), ∀ i : ℕ, (i : ℝ) * Δt ≤ T →
      hausdorffDist₂
        (convexHull ℝ ((STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i).H.construct
          ∪ (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ (i + 1)).H.construct))
        ((STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i).H.linComb
          (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ (i + 1)).H).construct
        ≤ ε := by -- --- PROOF ---
  intro ε hε
  set M : ℝ := ∑ k, ‖X₀.G k‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set c : ℝ := Real.sqrt X₀.h * X₀.h * (Real.sqrt n * Real.exp (T * ‖A‖) * M) with hc
  have hc0 : 0 ≤ c := by positivity
  -- `e^{AΔt} → I`
  have hcont : Tendsto (fun Δt : ℝ => ‖exp (Δt • A) - 1‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun Δt : ℝ => exp (Δt • A) - 1 :=
      (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)).sub continuous_const
    have h0 := ((hc.tendsto 0).norm).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h0
  filter_upwards [(hcont.const_mul c).eventually (gt_mem_nhds (by simpa using hε)),
    self_mem_nhdsWithin] with Δt hΔt hpos i hi
  have hΔ0 : 0 ≤ Δt := le_of_lt hpos
  set cs := STL.depReachConsts A B U Δt κ with hcs
  set Hi := (STL.depReachAt A Δt cs X₀ i).H with hHi
  -- `H(t_{i+1})` is the `H(t_k)` of Prop. 9 of Wetzlinger et al.
  have hnext : (STL.depReachAt A Δt cs X₀ (i + 1)).H
      = (Zonotope.mtimes (exp (Δt • A)) Hi).shift (-(MatExp.expIntegral A Δt).mulVec (B *ᵥ U.c)) :=
    aux_plus_ofPoint_eq_shift _ _
  rw [hnext, convexHull_union_eq_setLinComb ⟨Hi.c, Zonotope.centre_mem_construct Hi⟩
    ⟨_, Zonotope.centre_mem_construct _⟩ Hi.convex_construct (Zonotope.convex_construct _)]
  refine (Zonotope.hausdorffDist₂_linComb_le A Δt Hi _).trans ?_
  -- the generators of `H(t_i)`
  have hcol : ∀ j : Fin Hi.h, ‖(exp (Δt • A) - 1) *ᵥ Hi.G j‖₂
      ≤ Real.sqrt n * Real.exp (T * ‖A‖) * M * ‖exp (Δt • A) - 1‖ := by
    intro j
    obtain ⟨k, hk⟩ := aux_depReachAt_H_G A Δt cs X₀ i j
    rw [hk, Matrix.mulVec_mulVec]
    -- from `‖·‖₂` to the sup norm, then the operator norm of the matrix
    have h1 := norm₂_le_sqrt_mul_norm (((exp (Δt • A) - 1) * exp (Δt • A) ^ i) *ᵥ X₀.G k)
    have h2 := Matrix.linfty_opNorm_mulVec ((exp (Δt • A) - 1) * exp (Δt • A) ^ i) (X₀.G k)
    have hT : 0 ≤ T := le_trans (by positivity) hi
    have h3 : ‖(exp (Δt • A) - 1) * exp (Δt • A) ^ i‖
        ≤ ‖exp (Δt • A) - 1‖ * Real.exp (T * ‖A‖) := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [pow_zero, mul_one]
        exact le_mul_of_one_le_right (norm_nonneg _)
          (Real.one_le_exp (mul_nonneg hT (norm_nonneg _)))
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      calc ‖exp (Δt • A) ^ i‖ ≤ ‖exp (Δt • A)‖ ^ i := norm_pow_le' _ hi0
        _ ≤ Real.exp (Δt * ‖A‖) ^ i :=
            pow_le_pow_left₀ (norm_nonneg _) (MatExp.norm_exp_smul_le A hΔ0) i
        _ = Real.exp (i * (Δt * ‖A‖)) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (T * ‖A‖) := by
            refine Real.exp_le_exp.mpr ?_
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    -- the generator is one of the summands of `M`
    have h4 : ‖X₀.G k‖ ≤ M := Finset.single_le_sum (f := fun k => ‖X₀.G k‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have h5 : ‖(((exp (Δt • A) - 1) * exp (Δt • A) ^ i) *ᵥ X₀.G k)‖
        ≤ ‖exp (Δt • A) - 1‖ * Real.exp (T * ‖A‖) * M :=
      h2.trans (mul_le_mul h3 h4 (norm_nonneg _) (by positivity))
    -- collect the factors
    calc _ ≤ Real.sqrt n * ‖(((exp (Δt • A) - 1) * exp (Δt • A) ^ i) *ᵥ X₀.G k)‖ := h1
      _ ≤ Real.sqrt n * (‖exp (Δt • A) - 1‖ * Real.exp (T * ‖A‖) * M) :=
          mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hgen := (genOpNorm₂_le_sum_norm₂ (fun j : Fin Hi.h => (exp (Δt • A) - 1) *ᵥ Hi.G j)).trans
    (Finset.sum_le_sum fun j _ => hcol j)
  -- `H(t_i)` has the `γ_x` generators of `X₀`
  have hhh : (Hi.h : ℝ) = X₀.h := by rw [hHi, STL.depReachAt_H_h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hhh] at hgen
  calc Real.sqrt Hi.h * genOpNorm₂ (fun j : Fin Hi.h => (exp (Δt • A) - 1) *ᵥ Hi.G j)
      ≤ Real.sqrt X₀.h * (X₀.h * (Real.sqrt n * Real.exp (T * ‖A‖) * M * ‖exp (Δt • A) - 1‖)) := by
        rw [hhh]; exact mul_le_mul_of_nonneg_left hgen (Real.sqrt_nonneg _)
    _ = c * ‖exp (Δt • A) - 1‖ := by rw [hc]; ring
    _ ≤ ε := hΔt.le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
