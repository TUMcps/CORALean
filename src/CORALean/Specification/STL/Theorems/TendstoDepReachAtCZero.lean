module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderMatZero
public import CORALean.Specification.STL.Operations.DepReachConstsOf
public import CORALean.Specification.STL.Theorems.DepBoxSubsetClosedBall
public import CORALean.Specification.STL.Theorems.DepReachAtCSubsetClosedBall
public import CORALean.Specification.STL.Theorems.MtimesIntervalMatSubsetClosedBallInfSup
public import CORALean.Specification.STL.Theorems.TendstoSSupNormOfEventuallySubsetClosedBall
public import CORALean.Specification.STL.Operations.DepReachInit
public import CORALean.Specification.STL.Operations.DepReachAt
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusSubsetClosedBall

@[expose] public section

/-!
# [1, Prop. 4]: the curvature set vanishes with the step

`lim_{Δt→0} C_i = 0` for the curvature set of Eq. (17), as `C_i` is computed by Alg. 1, uniformly
over the steps up to a fixed final time `T`: the union of the `C_i`, `i Δt ≤ T`, has sup norm
radius tending to `0` as `Δt → 0⁺`, at the order `κ` fixed. `C₀ = interval(F X₀ ⊕ G ũ)` lies in the
ball of radius `2 s_F Σ_j absBound_j(X₀) + 2 s_G Σ_j absBound_j(ũ)` with `s_F`, `s_G` the sums
of the bounds in magnitude (`STL.mtimesIntervalMat_subset_closedBall_infSup`), each of which tends
to `0` since the terms `[c_j Δt^j, 0] A^j/j!` are continuous and `0` at `Δt = 0` and
`E → 0`; then `C_i = e^{AΔt} C_{i-1}` multiplies the radius by at most `e^{T‖A‖}`
(`STL.depReachAt_C_subset_closedBall`).

## Inputs
* `A` – dynamics matrix
* `B` – input matrix
* `X₀` – initial set
* `U` – input set
* `κ` – Taylor order
* `T` – final time

## Hypotheses
* none

## Conclusion
* the radius of the curvature sets tends to zero with the step

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.tendsto_depReachAt_C_zero (A : Mat ℝ n n) (B : Mat ℝ n m) (X₀ : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) (κ : ℕ) (T : ℝ) : -- --- CONCL ---
    Tendsto (fun Δt : ℝ => sSup ((fun v => ‖v‖) ''
      ⋃ i ∈ {i : ℕ | (i : ℝ) * Δt ≤ T},
        (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i).C.construct))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by -- --- PROOF ---
  have hcz : ∀ g : ℝ → ℝ, Continuous g → g 0 = 0 →
      Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0) := fun g hc h0 => by
    simpa [h0] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hE : ∀ j k : Fin n, Tendsto (fun Δt : ℝ => MatExp.expRemainderMat A Δt κ j k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := fun j k =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (MatExp.tendsto_expRemainderMat_zero A κ) j) k
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hΔE : ∀ j k : Fin n, Tendsto (fun Δt : ℝ => Δt * MatExp.expRemainderMat A Δt κ j k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := fun j k => by simpa using hid.mul (hE j k)
  -- the order-`j` terms of `F` and `G`
  have hcorr : ∀ (o : ℕ) (j k : Fin n), 2 ≤ o →
      Tendsto (fun Δt : ℝ => MatExp.corrTerm A Δt o j k) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro o j k ho
    refine hcz _ ?_ ?_
    · unfold MatExp.corrTerm; fun_prop
    · simp [MatExp.corrTerm, zero_pow (by omega : o ≠ 0)]
  -- the constant terms `Δt^o/o!`-type of `G`
  have hconst : ∀ (o : ℕ) (j k : Fin n),
      Tendsto (fun Δt : ℝ => MatExp.constCorrTerm A Δt o j k) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro o j k
    refine hcz _ ?_ ?_
    · unfold MatExp.constCorrTerm; fun_prop
    · simp [MatExp.constCorrTerm]
  -- the lower and upper bounds of the interval matrices `F` and `G` vanish
  have hFmin : ∀ j k : Fin n, Tendsto (fun Δt : ℝ =>
      ∑ i ∈ Finset.range (κ - 1), min (MatExp.corrTerm A Δt (i + 2) j k) 0) (𝓝[>] (0 : ℝ))
      (𝓝 0) := fun j k => by
    simpa using tendsto_finsetSum (Finset.range (κ - 1)) fun i _ =>
      (hcorr (i + 2) j k (by omega)).min (tendsto_const_nhds (x := (0 : ℝ)))
  have hFmax : ∀ j k : Fin n, Tendsto (fun Δt : ℝ =>
      ∑ i ∈ Finset.range (κ - 1), max (MatExp.corrTerm A Δt (i + 2) j k) 0) (𝓝[>] (0 : ℝ))
      (𝓝 0) := fun j k => by
    simpa using tendsto_finsetSum (Finset.range (κ - 1)) fun i _ =>
      (hcorr (i + 2) j k (by omega)).max (tendsto_const_nhds (x := (0 : ℝ)))
  have hGmin : ∀ j k : Fin n, Tendsto (fun Δt : ℝ =>
      ∑ i ∈ Finset.range κ, min (MatExp.constCorrTerm A Δt i j k) 0) (𝓝[>] (0 : ℝ))
      (𝓝 0) := fun j k => by
    simpa using tendsto_finsetSum (Finset.range κ) fun i _ =>
      (hconst i j k).min (tendsto_const_nhds (x := (0 : ℝ)))
  have hGmax : ∀ j k : Fin n, Tendsto (fun Δt : ℝ =>
      ∑ i ∈ Finset.range κ, max (MatExp.constCorrTerm A Δt i j k) 0) (𝓝[>] (0 : ℝ))
      (𝓝 0) := fun j k => by
    simpa using tendsto_finsetSum (Finset.range κ) fun i _ =>
      (hconst i j k).max (tendsto_const_nhds (x := (0 : ℝ)))
  -- the sums of the bounds in magnitude vanish
  have hsF : Tendsto (fun Δt : ℝ => ∑ j : Fin n, ∑ k : Fin n,
      (|(STL.depCurvatureF A Δt κ).inf j k| + |(STL.depCurvatureF A Δt κ).sup j k|))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [STL.depCurvatureF] using tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_finsetSum Finset.univ fun k _ =>
      (((hFmin j k).sub (hE j k)).abs).add (((hFmax j k).add (hE j k)).abs)
  have hsG : Tendsto (fun Δt : ℝ => ∑ j : Fin n, ∑ k : Fin n,
      (|(STL.depCurvatureG A Δt κ).inf j k| + |(STL.depCurvatureG A Δt κ).sup j k|))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [STL.depCurvatureG] using tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_finsetSum Finset.univ fun k _ =>
      (((hGmin j k).sub (hΔE j k)).abs).add (((hGmax j k).add (hΔE j k)).abs)
  -- the radius of the ball around `C₀`
  set ũ : Zonotope (Vec ℝ n) := Zonotope.ofPoint (B *ᵥ U.c) with hũ
  set ρ0 : ℝ → ℝ := fun Δt =>
    2 * (∑ j : Fin n, ∑ k : Fin n,
      (|(STL.depCurvatureF A Δt κ).inf j k| + |(STL.depCurvatureF A Δt κ).sup j k|))
        * ∑ j, X₀.absBound j
    + 2 * (∑ j : Fin n, ∑ k : Fin n,
      (|(STL.depCurvatureG A Δt κ).inf j k| + |(STL.depCurvatureG A Δt κ).sup j k|))
        * ∑ j, ũ.absBound j with hρ0
  have hρ0t : Tendsto ρ0 (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (((hsF.const_mul 2).mul_const (∑ j, X₀.absBound j)).add
      ((hsG.const_mul 2).mul_const (∑ j, ũ.absBound j)))
  -- the radius is nonnegative
  have hnn : ∀ Z : Zonotope (Vec ℝ n), ∀ j, 0 ≤ Z.absBound j := fun Z j =>
    add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hρ0nn : ∀ Δt, 0 ≤ ρ0 Δt := fun Δt => by
    have h1 : ∀ (IM : Interval (Mat ℝ n n)), 0 ≤ ∑ j : Fin n, ∑ k : Fin n,
        (|IM.inf j k| + |IM.sup j k|) := fun IM =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        add_nonneg (abs_nonneg _) (abs_nonneg _)
    have h2 : ∀ Z : Zonotope (Vec ℝ n), 0 ≤ ∑ j, Z.absBound j :=
      fun Z => Finset.sum_nonneg fun j _ => hnn Z j
    exact add_nonneg (mul_nonneg (mul_nonneg two_pos.le (h1 _)) (h2 X₀))
      (mul_nonneg (mul_nonneg two_pos.le (h1 _)) (h2 ũ))
  -- `C₀` lies in the ball of radius `ρ0`
  have hC0 : ∀ Δt : ℝ, (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ 0).C.construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (ρ0 Δt) := fun Δt =>
    STL.depBox_subset_closedBall (hρ0nn Δt)
      (Zonotope.plus_subset_closedBall
        (STL.mtimesIntervalMat_subset_closedBall_infSup (STL.depCurvatureF A Δt κ) X₀)
        (STL.mtimesIntervalMat_subset_closedBall_infSup (STL.depCurvatureG A Δt κ) ũ))
  refine STL.tendsto_sSup_norm_of_eventually_subset_closedBall fun ε hε => ?_
  -- for small `Δt` the ball of `C_i` has radius below `ε`
  have hev : ∀ᶠ Δt in 𝓝[>] (0 : ℝ), Real.exp (T * ‖A‖) * ρ0 Δt < ε :=
    (hρ0t.const_mul (Real.exp (T * ‖A‖))).eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [hev, self_mem_nhdsWithin] with Δt hΔt hpos
  intro v hv
  obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.mp hv
  exact Metric.closedBall_subset_closedBall hΔt.le
    (STL.depReachAt_C_subset_closedBall A (le_of_lt hpos) _ X₀ (hρ0nn Δt) (hC0 Δt) i hi hvi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
