module

public import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
public import CORALean.ContDynamics.LinearSys.Definitions.HeldInput
public import CORALean.Specification.STL.Operations.DepReach
public import CORALean.Specification.STL.Theorems.DepBloatingC
public import CORALean.Specification.STL.Theorems.SumGenMtimes
public import CORALean.Specification.STL.Theorems.SumGenOfPoint
public import CORALean.Specification.STL.Theorems.SumGenPlus
public import CORALean.ContSet.Zonotope.Real.Operations.LinComb
public import CORALean.Specification.STL.Theorems.ExpIntegralZeroOne

@[expose] public section

/-!
# The generators of `R(τ₀)` for `ẋ = u`: only the input's one is non-zero

For `ẋ = u` (`A = 0`, `B = 1`), `X₀ = {0}`, `U = [-1,1]`, `Δt = 1`, `κ = 1`, `i = 0`, every weighted
sum of the generators of `R(τ₀)` of [1, Alg. 1] is `f(1)` times `1`: the hull's `½(c₁-c₂)`, `D₁` and
`C₀` have the generator `0`, and `T B G_u = 1` is the second. Used for the example of the
failure of [1, Prop. 1] and [1, Prop. 2] between the time points.

## Inputs
* `f` – factor values

## Hypotheses
* none

## Conclusion
* only the input generator of the first interval set is nonzero

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem STL.aux_remZero {n : ℕ} (Δt : ℝ) (κ : ℕ) : -- --- CONCL ---
    MatExp.expRemainderMat (0 : Mat ℝ n n) Δt κ = 0 := by -- --- PROOF ---
  -- `|0| = 0`, so `E = e^0 - Σ 0^j/j! = 1 - 1`
  have h : MatExp.absMat (0 : Mat ℝ n n) = 0 := by
    funext i j; simp [MatExp.absMat]
  simp only [MatExp.expRemainderMat, h, smul_zero, exp_zero, MatExp.expTaylor]
  rw [Finset.sum_range_succ']
  simp [zero_pow, Finset.sum_eq_zero]

/-- The sum of two sets without generators has none. -/
private theorem STL.aux_plus_zero {n : ℕ} (Z₁ Z₂ : Zonotope (Vec ℝ n)) (h₁ : ∀ k, Z₁.G k = 0)
    (h₂ : ∀ k, Z₂.G k = 0) : -- --- CONCL ---
    ∀ k, (Z₁.plus Z₂).G k = 0 := by -- --- PROOF ---
  intro k
  -- the layout is `Fin.append`: an index is in the first block or in the second
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · simp [Zonotope.plus, Fin.append_left, h₁]
  · simp [Zonotope.plus, Fin.append_right, h₂]

private theorem STL.aux_mtimes_zero {n m : ℕ} (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) (h : M = 0) :
    ∀ k, (Zonotope.mtimes M Z).G k = 0 := by
  intro k; simp [Zonotope.mtimes, h]

private theorem STL.aux_depBox_zero {n : ℕ} (Z : Zonotope (Vec ℝ n)) (h : ∀ k, Z.G k = 0) :
    ∀ k, (STL.depBox Z).G k = 0 := by
  -- the radius `Σ |0|` is `0`
  intro k; simp [STL.depBox, h]; rfl

private theorem STL.aux_mtimesIntervalMat_zero {m n : ℕ} (IM : Interval (Mat ℝ m n))
    (Z : Zonotope (Vec ℝ n)) (hc : IM.center = 0) (hr : ∀ i, Zonotope.radiusReach IM Z i = 0) :
    ∀ k, (Zonotope.mtimesIntervalMat IM Z).G k = 0 := by
  intro k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · simp [Zonotope.mtimesIntervalMat, Fin.append_left, hc]
  · simp [Zonotope.mtimesIntervalMat, Fin.append_right, hr]; rfl

private theorem STL.aux_partZero {n : ℕ} (Δt : ℝ) (j : ℕ) :
    MatExp.particularCoeff (0 : Mat ℝ n n) Δt (j + 1) = 0 := by
  simp [MatExp.particularCoeff, zero_pow]

private theorem STL.aux_foldl_zero {n : ℕ} (A : Mat ℝ n n) (Δt : ℝ) (hA : A = 0)
    (U₀ : Zonotope (Vec ℝ n)) (l : List ℕ) (Z : Zonotope (Vec ℝ n))
    (hZ : ∀ k, Z.G k = 0) : -- --- CONCL ---
    ∀ k, (l.foldl (fun Z j => Z.plus
      (Zonotope.mtimes (MatExp.particularCoeff A Δt (j + 1)) U₀)) Z).G k = 0 := by -- --- PROOF ---
  induction l generalizing Z with
  | nil => exact hZ
  | cons j l ih =>
    exact ih _ (STL.aux_plus_zero _ _ hZ
      (STL.aux_mtimes_zero _ _ (by subst hA; exact STL.aux_partZero Δt j)))

private theorem STL.aux_bloat_zero {n : ℕ} (Δt : ℝ) (κ : ℕ)
    (U₀ : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    ∀ k, (STL.depBloating (0 : Mat ℝ n n) U₀ Δt κ).G k = 0 := by -- --- PROOF ---
  unfold STL.depBloating
  simp only []
  refine STL.aux_plus_zero _ _ (STL.aux_plus_zero _ _ ?_ ?_) ?_
  · refine STL.aux_mtimes_zero _ _ (Finset.sum_eq_zero fun j hj => ?_)
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; omega⟩
    exact STL.aux_partZero Δt j'
  · refine STL.aux_foldl_zero _ _ rfl _ _ _ ?_
    intro k; exact k.elim0
  · refine STL.aux_mtimesIntervalMat_zero _ _ ?_ ?_
    · simp [Interval.center, STL.aux_remZero]
    · intro i; simp [Zonotope.radiusReach, Interval.radius, STL.aux_remZero]

private theorem STL.aux_mtimes_zero_gens {n m : ℕ} (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n))
    (h : ∀ k, Z.G k = 0) :
    ∀ k, (Zonotope.mtimes M Z).G k = 0 := by
  intro k; simp [Zonotope.mtimes, h]

private theorem STL.aux_mtimesIntervalMat_zero_gens {m n : ℕ} (IM : Interval (Mat ℝ m n))
    (Z : Zonotope (Vec ℝ n)) (hg : ∀ k, Z.G k = 0) (hc : Z.c = 0) : -- --- CONCL ---
    ∀ k, (Zonotope.mtimesIntervalMat IM Z).G k = 0 := by -- --- PROOF ---
  intro k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · simp [Zonotope.mtimesIntervalMat, Fin.append_left, hg]
  · simp [Zonotope.mtimesIntervalMat, Fin.append_right, Zonotope.radiusReach,
      Zonotope.absBound, hg, hc]
    rfl

private theorem STL.aux_linComb_zero {n : ℕ} (Z₁ Z₂ : Zonotope (Vec ℝ n)) (h₁ : ∀ k, Z₁.G k = 0)
    (h₂ : ∀ k, Z₂.G k = 0) (hc : Z₁.c = Z₂.c) : -- --- CONCL ---
    ∀ k, (Z₁.linComb Z₂).G k = 0 := by -- --- PROOF ---
  intro k
  unfold Zonotope.linComb
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · simp only [Fin.append_left]
    refine Fin.addCases (fun a' => ?_) (fun b' => ?_) a
    · simp [Fin.append_left, Zonotope.pairSum, h₁, h₂]
    · simp [Fin.append_right, Zonotope.pairDiff, h₁, h₂]
  · simp [Fin.append_right, hc]

private theorem STL.aux_S_general {n : ℕ} (hull Pc D C : Zonotope (Vec ℝ n))
    (hh : ∀ k, hull.G k = 0)
    (hD : ∀ k, D.G k = 0) (hC : ∀ k, C.G k = 0) (f : ℕ → ℝ) : -- --- CONCL ---
    ∑ k : Fin ((hull.plus (Pc.plus D)).plus C).h, f k • ((hull.plus (Pc.plus D)).plus C).G k
      = ∑ k : Fin Pc.h, f (hull.h + k) • Pc.G k := by -- --- PROOF ---
  rw [STL.sumGen_plus (hull.plus (Pc.plus D)) C f, STL.sumGen_plus hull (Pc.plus D) f,
    STL.sumGen_plus Pc D (fun k => f (hull.h + k))]
  have h1 : ∑ k : Fin hull.h, f k • hull.G k = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hh k, smul_zero]
  have h2 : ∑ k : Fin D.h, f (hull.h + (Pc.h + k)) • D.G k = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hD k, smul_zero]
  have h3 : ∑ k : Fin C.h, f ((hull.plus (Pc.plus D)).h + k) • C.G k = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hC k, smul_zero]
  rw [h1, h2, h3]
  simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depReachInterval_sum_eval (f : ℕ → ℝ) : -- --- CONCL ---
    let X₀ : Zonotope (Vec ℝ 1) := ⟨0, 0, Fin.elim0⟩
    let U : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ => fun _ => 1⟩
    ∑ k : Fin (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) X₀ U 1 1 0).2.h,
        f k • (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) X₀ U 1 1 0).2.G k
      = f 1 • (fun _ => (1 : ℝ) : Vec ℝ 1) := by -- --- PROOF ---
  -- `ẋ = u`, `X₀ = {0}`, `U = [-1,1]`: all but one generator of `R(τ₀)` are `0`
  intro X₀ U
  set cs := STL.depReachConsts (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) U 1 1 with hcs
  have hXc : X₀.c = 0 := rfl
  have hUc : U.c = 0 := rfl
  have hu : cs.ũ = 0 := by
    show (1 : Mat ℝ 1 1) *ᵥ U.c = 0
    simp [hUc]
  -- the generators of `H(t₀)`, `H(t₁)`, `D₁` and `C₀` are all `0`
  have hH0 : ∀ k, (STL.depReachAt 0 1 cs X₀ 0).H.G k = 0 :=
    fun k => Fin.elim0 k
  have hHc0 : (STL.depReachAt 0 1 cs X₀ 0).H.c = 0 := rfl
  have hH1 : ∀ k, (STL.depReachAt 0 1 cs X₀ 1).H.G k = 0 :=
    STL.aux_plus_zero _ _ (STL.aux_mtimes_zero_gens _ _ hH0) (fun k => Fin.elim0 k)
  have hHc1 : (STL.depReachAt 0 1 cs X₀ 1).H.c = 0 := by
    simp [STL.depReachAt, STL.depReachStep, STL.depReachInit, Zonotope.plus,
      Zonotope.mtimes, Zonotope.ofPoint, hXc, hu]
  have hD1 : ∀ k, (STL.depReachAt 0 1 cs X₀ 1).D.G k = 0 :=
    STL.aux_depBox_zero _ (STL.aux_plus_zero _ _
      (STL.aux_mtimes_zero_gens _ _ (fun k => Fin.elim0 k)) (STL.aux_bloat_zero _ _ _))
  have hC0 : ∀ k, (STL.depReachAt 0 1 cs X₀ 0).C.G k = 0 :=
    STL.aux_depBox_zero _ (STL.aux_plus_zero _ _
      (STL.aux_mtimesIntervalMat_zero_gens _ _ (fun k => Fin.elim0 k) hXc)
      (STL.aux_mtimesIntervalMat_zero_gens _ _ (fun k => Fin.elim0 k)
        (by simpa [Zonotope.ofPoint] using hu)))
  -- so only the generator of `P_c(t₁)` is left, `T B G_u = 1`, after the hull's one
  have hhull := STL.aux_linComb_zero _ _ hH0 hH1 (hHc0.trans hHc1.symm)
  refine (STL.aux_S_general _ _ _ _ hhull hD1 hC0 f).trans ?_
  refine (STL.sumGen_plus _ _ (fun k => f (1 + k))).trans ?_
  have hPc0 : (STL.depReachAt 0 1 cs X₀ 0).Pc
      = Zonotope.ofPoint 0 := rfl
  rw [hPc0, STL.sumGen_mtimes _ _ (fun k => f (1 + k)), STL.sumGen_ofPoint, Matrix.mulVec_zero,
    zero_add]
  have hU0 : cs.U₀
      = Zonotope.mtimes 1 (U.plus (Zonotope.ofPoint (-U.c))) := rfl
  have hT : cs.T = 1 := STL.expIntegral_zero_one
  -- the weights of the generators of `T U₀`, shifted by the blocks before it
  set g : ℕ → ℝ := fun k => f (1 + ((Zonotope.mtimes (exp ((1:ℝ) • (0 : Mat ℝ 1 1)))
    (Zonotope.ofPoint (0 : Vec ℝ 1))).h + k)) with hg
  rw [STL.sumGen_mtimes _ _ g, hU0, hT, Matrix.one_mulVec, STL.sumGen_mtimes 1 _ g,
    Matrix.one_mulVec, STL.sumGen_plus _ _ g]
  rw [STL.sumGen_ofPoint, add_zero]
  show ∑ k : Fin 1, g k • (fun _ : Fin 1 => (1 : ℝ)) = _
  rw [Fin.sum_univ_one]
  simp [hg, Zonotope.mtimes, Zonotope.ofPoint]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
