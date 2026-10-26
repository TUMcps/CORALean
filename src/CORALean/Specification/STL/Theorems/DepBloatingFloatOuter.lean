module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatEntryLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsLeAbsBoundError
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.Specification.STL.Operations.DepBloatingFloat
public import CORALean.Specification.STL.Theorems.ZonotopeExtremes

@[expose] public section

/-!
# The bloating `D` over floats encloses the real one

The first term of `STL.depBloating` [1, Alg. 1] maps a real zonotope by a real matrix, the sum
of the coefficients, which the interval matrix `particularCoeffSum` holds, so the float
`mtimesIntervalMat` holds it (`mtimesIntervalMat_outer`). The second is the sum of the images by the
single coefficients, each inside its `intervalInputTerm`, one `plus` at a time. The third is a box:
the interval matrix is symmetric, so the real product is the box whose radius weights the reach of
the real zonotope by `2Δt E`, and the reach is under `absBoundError` of the float zonotope that
holds it (`aux_absBound_le_absBoundError`), as `2Δt E` is under the float bound
(`expRemainderMat_entry_le_bound`).

## Inputs
* `A` – float dynamics matrix
* `Δt` – float time step
* `κ` – Taylor order
* `U₀r` – real input zonotope
* `U₀f` – float input zonotope

## Hypotheses
* `hr` – the time step is nonnegative
* `hε` – the float norm bound is small enough for the Taylor order
* `hU` – the real zonotope lies inside the float one

## Conclusion
* the real bloating lies inside the float one

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise Matrix Float Float.FloatOps Float.SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sum of the real coefficients lies in the float sum over the point box. -/
private theorem STL.aux_depBloating_sum (A : Mat 𝕋 n n) {r : 𝕋} (hr : 0 ≤ toReal r)
    (η : ℕ) : -- --- CONCL ---
    ∑ j ∈ Finset.Icc 1 η, Real.MatExp.particularCoeff (toRealMat A) (toReal r) j
      ∈ (MatExp.particularCoeffSum (Interval.point A) r 1 η).construct := by -- --- PROOF ---
  have hM : toRealMat A ∈ (Interval.point A).construct := Float.Interval.mem_point A
  -- the point `0` holds the empty sum
  have hzero : (0 : Mat ℝ n n)
      ∈ (Interval.point fun _ _ => (zero : 𝕋) : Interval (Mat 𝕋 n n)).construct :=
    Interval.mem_mat_iff.mpr fun _ _ => by simp [Interval.point, toReal_zero]
  have hterm : ∀ i, Real.MatExp.particularCoeff (toRealMat A) (toReal r) i
      ∈ (MatExp.intervalInputTerm (Interval.point A) r i).construct :=
    fun i => MatExp.smul_pow_mem_intervalInputTerm _ hr hM i
  have hIcc : Finset.Icc 1 η = Finset.Ico 1 (η + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [hIcc]
  clear hIcc
  induction η with
  | zero =>
    unfold MatExp.particularCoeffSum
    rw [if_neg (by omega), Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
    exact hzero
  | succ η ih =>
    unfold MatExp.particularCoeffSum
    rw [if_pos (by omega), Finset.sum_Ico_succ_top (by omega), Interval.materialiseMat_eq]
    exact Interval.matPlus_outer _ _ ih (hterm (η + 1))

/-- The reach of a real zonotope is under the float `absBoundError` of one holding it. -/
private theorem STL.aux_absBound_le_absBoundError {Zr : Real.Zonotope (Vec ℝ n)}
    {Zf : Float.Zonotope (Vec 𝕋 n)} (h : Zr.construct ⊆ Zf.construct) (i : Fin n) : -- --- CONCL ---
    Zr.absBound i ≤ toReal (Zf.absBoundError i) := by -- --- PROOF ---
  obtain ⟨⟨x₁, hx₁, e₁⟩, ⟨x₂, hx₂, e₂⟩⟩ := STL.zonotope_extremes Zr i
  have b₁ := Float.Zonotope.abs_le_absBoundError (h hx₁) i
  have b₂ := Float.Zonotope.abs_le_absBoundError (h hx₂) i
  have hr0 : 0 ≤ ∑ l, |Zr.G l i| := Finset.sum_nonneg fun l _ => abs_nonneg _
  rw [e₁] at b₁
  rw [e₂] at b₂
  show |Zr.c i| + ∑ l, |Zr.G l i| ≤ _
  rcases le_total 0 (Zr.c i) with hc | hc
  · rw [abs_of_nonneg hc]
    exact (le_abs_self _).trans b₁
  · rw [abs_of_nonpos hc]
    refine le_trans ?_ b₂
    rw [abs_of_nonpos (by linarith [hr0] : Zr.c i - ∑ l, |Zr.G l i| ≤ 0)]
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float bloating holds the real one of every real zonotope inside the float `U₀`. -/
theorem STL.depBloatingFloat_outer (A : Mat 𝕋 n n) {Δt : 𝕋} (hr : 0 ≤ toReal Δt) (κ : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((κ : ℝ) + 2) ≤ 1 / 2) {U₀r : Real.Zonotope (Vec ℝ n)} {U₀f : Float.Zonotope (Vec 𝕋 n)}
    (hU : U₀r.construct ⊆ U₀f.construct) : -- --- CONCL ---
    (STL.depBloating (toRealMat A) U₀r (toReal Δt) κ).construct ⊆
      (STL.depBloatingFloat A U₀f Δt κ).construct := by -- --- PROOF ---
  have hM : toRealMat A ∈ (Interval.point A).construct := Float.Interval.mem_point A
  unfold STL.depBloating STL.depBloatingFloat
  dsimp only
  rw [← Real.Zonotope.plus_exact, ← Real.Zonotope.plus_exact]
  refine (Set.add_subset_add (Set.add_subset_add ?_ ?_) ?_).trans
    ((Set.add_subset_add (Float.Zonotope.plus_outer _ _) (Set.Subset.refl _)).trans
      (Float.Zonotope.plus_outer _ _))
  · -- the first term: one real matrix of the interval matrix maps `U₀`
    rw [← Real.Zonotope.mtimes_exact]
    rintro _ ⟨u, hu, rfl⟩
    exact Float.Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_iUnion₂.2
      ⟨_, STL.aux_depBloating_sum A hr κ, ⟨u, hU hu, rfl⟩⟩)
  · -- the second term: the images of the `κ` coefficient matrices, summed one at a time
    -- by induction on the number of coefficients folded in
    have hfold : ∀ m, ((List.range m).foldl
        (fun Z j => Z.plus (Real.Zonotope.mtimes
          (Real.MatExp.particularCoeff (toRealMat A) (toReal Δt) (j + 1)) U₀r))
        (Real.Zonotope.ofPoint (0 : Vec ℝ n))).construct ⊆
        ((List.range m).foldl
        (fun Z j => Z.plus (Float.Zonotope.mtimesIntervalMat
          (MatExp.intervalInputTerm (Interval.point A) Δt (j + 1)) U₀f))
        (Float.Zonotope.point (fun _ => (zero : 𝕋)))).construct := by
      intro m
      -- the empty fold is the point zero on both sides
      induction m with
      | zero =>
        intro x hx
        simp only [List.range_zero, List.foldl_nil] at hx ⊢
        rw [Real.Zonotope.mem_ofPoint_iff] at hx
        rw [Float.Zonotope.construct_point]
        show x = toRealVec (fun _ => (zero : 𝕋))
        rw [hx]
        funext i
        simp [toRealVec, toReal_zero]
      | succ m ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons,
          List.foldl_cons, List.foldl_nil, List.foldl_nil, ← Real.Zonotope.plus_exact,
          ← Real.Zonotope.mtimes_exact]
        refine (Set.add_subset_add ih ?_).trans (Float.Zonotope.plus_outer _ _)
        rintro _ ⟨u, hu, rfl⟩
        exact Float.Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_iUnion₂.2
          ⟨_, MatExp.smul_pow_mem_intervalInputTerm _ hr hM (m + 1), ⟨u, hU hu, rfl⟩⟩)
    exact hfold κ
  · -- the third term: a symmetric interval matrix gives a box, held by the zonotope of the box
    intro y hy
    refine Float.Interval.zonotope_contains _ ?_
    -- the radius matrix `X = 2Δt E` of the symmetric interval matrix, and its center `0`
    set X : Mat ℝ n n := (2 * toReal Δt) • Real.MatExp.expRemainderMat (toRealMat A) (toReal Δt) κ
      with hX
    obtain ⟨β, hβ, hyβ⟩ := Real.Zonotope.mem_construct_iff.1 hy
    refine Float.Interval.mem_vec_iff.2 fun i => ?_
    have hctr : Real.Interval.center (⟨-X, X⟩ : Real.Interval (Mat ℝ n n)) = 0 := by
      simp [Real.Interval.center]
    have hrad : ∀ a b, Real.Interval.radius (⟨-X, X⟩ : Real.Interval (Mat ℝ n n)) a b = X a b := by
      intro a b
      simp [Real.Interval.radius]
      ring
    -- the point is the last generator of coordinate `i` scaled by a coefficient
    have hyi : |y i| ≤ ∑ k, |X i k| * U₀r.absBound k := by
      have hy' : y i = (Real.Interval.center (⟨-X, X⟩ : Real.Interval (Mat ℝ n n)) *ᵥ U₀r.c) i +
          ∑ j : Fin (U₀r.h + n), (Fin.append
            (fun l => Real.Interval.center (⟨-X, X⟩ : Real.Interval (Mat ℝ n n)) *ᵥ U₀r.G l)
            (Matrix.diagonal fun q => Real.Zonotope.radiusReach
              (⟨-X, X⟩ : Real.Interval (Mat ℝ n n)) U₀r q)) j i * β j := hyβ i
      rw [hy']
      simp only [hctr, Matrix.zero_mulVec, Pi.zero_apply, zero_add, Fin.sum_univ_add,
        Fin.append_left, Fin.append_right, Matrix.diagonal_apply]
      simp only [Real.Zonotope.radiusReach, hrad, zero_mul, Finset.sum_const_zero, zero_add,
        ite_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      calc |(∑ k, X i k * U₀r.absBound k) * β (Fin.natAdd U₀r.h i)|
          ≤ |∑ k, X i k * U₀r.absBound k| * 1 := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hβ _) (abs_nonneg _)
        _ ≤ ∑ k, |X i k * U₀r.absBound k| := by rw [mul_one]; exact Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, |X i k| * U₀r.absBound k := Finset.sum_congr rfl fun k _ => by
            rw [abs_mul, abs_of_nonneg (a := U₀r.absBound k) (add_nonneg (abs_nonneg _)
              (Finset.sum_nonneg fun l _ => abs_nonneg _))]
    -- the float bound on the entries of `X`, and the reach of the float zonotope
    have hM := Float.Interval.mem_point A
    have hnorm := MatExp.norm_smul_le_normUpperBound (Interval.point A) Δt hM
    -- the norm bound is below one, so the remainder entries are bounded
    have hlt : ‖toReal Δt • toRealMat A‖ / ((κ : ℝ) + 2) < 1 :=
      lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnorm (by positivity)) hε)
        (by norm_num)
    have hE := MatExp.expRemainderBound_le κ hnorm (le_trans (norm_nonneg _) hnorm) hε
    -- the rounded bound on `2Δt E`, entry by entry
    set Eb := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul Δt Δt
      (Interval.point A))) κ with hEb
    set w := mulUp Δt Eb with hw
    -- each term of the row sum is under its rounded-up float term
    have hterm : ∀ k, |X i k| * U₀r.absBound k ≤
        toReal (mulUp (addUp w w) (U₀f.absBoundError k)) := fun k => by
      have hab : 0 ≤ U₀r.absBound k := add_nonneg (abs_nonneg _)
        (Finset.sum_nonneg fun l _ => abs_nonneg _)
      have hXk : |X i k| ≤ toReal (addUp w w) := by
        have h1 := (Real.MatExp.expRemainderMat_entry_le_bound (toRealMat A) κ hlt i k).trans hE
        have h2 : |X i k| =
            2 * toReal Δt * |Real.MatExp.expRemainderMat (toRealMat A) (toReal Δt) κ i k| := by
          simp only [hX, Matrix.smul_apply, smul_eq_mul, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * toReal Δt)]
        have h3 := mul_le_mulUp Δt Eb
        have h4 := add_le_addUp w w
        rw [h2]
        nlinarith [mul_le_mul_of_nonneg_left h1 hr]
      have hX0 : 0 ≤ toReal (addUp w w) := (abs_nonneg _).trans hXk
      -- the entry bound, then the real reach against the float reach, then the rounding
      calc |X i k| * U₀r.absBound k ≤ toReal (addUp w w) * U₀r.absBound k :=
            mul_le_mul_of_nonneg_right hXk hab
        _ ≤ toReal (addUp w w) * toReal (U₀f.absBoundError k) :=
            mul_le_mul_of_nonneg_left (STL.aux_absBound_le_absBoundError hU k) hX0
        _ ≤ _ := mul_le_mulUp _ _
    -- summing the entries gives the float radius
    have hρ : |y i| ≤ toReal (sumUp fun k => mulUp (addUp w w) (U₀f.absBoundError k)) :=
      hyi.trans ((Finset.sum_le_sum fun k _ => hterm k).trans (sum_le_sumUp _))
    have hρ' := abs_le.1 hρ
    refine ⟨?_, hρ'.2⟩
    change toReal (neg _) ≤ y i
    rw [toReal_neg]
    exact hρ'.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
