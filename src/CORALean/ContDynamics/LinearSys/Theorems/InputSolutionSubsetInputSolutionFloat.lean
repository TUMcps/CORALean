module

public import CORALean.ContDynamics.LinearSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundNonneg
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# The float input solution holds the exact one

[1, Thm. 1]'s `⊕ᵢ Aⁱrⁱ⁺¹/(i+1)! U ⊕ E(r)·r·U` over `Real.Zonotope` is inside
`inputSolutionFloat` at a float zonotope holding `U`: order by order the exact matrix is in the
float interval matrix and `mtimes_outer` carries its image, the exact sums in `plus_outer`, and
the remainder is the exact zonotope map at the exact interval `[-E r, E r]`, inside the float
one by `Zonotope.aux_real_mtimesIntervalMat_subset` since both ends of the exact interval are
matrices of the float one. The float zonotope has error box `{0}`, so its points are its nominal
part.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `Wr` – exact input zonotope
* `V` – input float zonotope

## Hypotheses
* `hr` – step length nonnegative
* `hη` – order admissible
* `hE` – float zonotope has a point error box
* `hW` – exact zonotope lies in the float zonotope

## Conclusion
* the exact input solution lies in the float one

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet Matrix
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Real
section
variable {n : ℕ}

/-- A real number times its own sign is its absolute value. -/
theorem aux_absLe_mul_sign (x : ℝ) : x * (if 0 ≤ x then (1 : ℝ) else -1) = |x| := by
  split
  · rw [mul_one, abs_of_nonneg]; assumption
  · rw [mul_neg_one, abs_of_neg (not_le.mp (by assumption))]


/-- A coordinate's `absBound` is the largest `|x j|` a zonotope reaches. -/
theorem Zonotope.aux_absBound_le_of_abs_le {Z : Zonotope (Vec ℝ n)} {r : ℝ} {j : Fin n}
    (h : ∀ x ∈ Z.construct, |x j| ≤ r) : -- --- CONCL ---
    Z.absBound j ≤ r := by -- --- PROOF ---
  -- the center's sign on every generator at coordinate `j`
  set t : ℝ := if 0 ≤ Z.c j then (1 : ℝ) else -1 with ht
  set β : Fin Z.h → ℝ := fun l => t * (if 0 ≤ Z.G l j then (1 : ℝ) else -1) with hβdef
  have hβ : ∀ l, |β l| ≤ 1 := fun l => by
    rw [hβdef, ht]
    by_cases h1 : 0 ≤ Z.c j <;> by_cases h2 : 0 ≤ Z.G l j <;> simp [h1, h2]
  set x : Vec ℝ n := fun i => Z.c i + ∑ l, Z.G l i * β l with hxdef
  -- it is a point of the zonotope, and its `j`-th coordinate is the reach up to the sign
  have hx : x ∈ Z.construct := Zonotope.mem_construct_iff.mpr ⟨β, hβ, fun i => rfl⟩
  have htt : t * t = 1 := by rw [ht]; split <;> norm_num
  have htc : t * Z.c j = |Z.c j| := by rw [mul_comm, ht, aux_absLe_mul_sign]
  -- each generator's sign makes its term `|Gₗ j|`, so the sum is the sum of magnitudes
  have hsum : t * ∑ l, Z.G l j * β l = ∑ l, |Z.G l j| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hβdef]
    calc t * (Z.G l j * (t * (if 0 ≤ Z.G l j then (1:ℝ) else -1)))
        = (t * t) * (Z.G l j * (if 0 ≤ Z.G l j then (1:ℝ) else -1)) := by ring
      _ = |Z.G l j| := by rw [htt, one_mul, aux_absLe_mul_sign]
  -- scaling the point by `t` gives the `absBound`
  have hxj : t * x j = Z.absBound j := by
    show t * (Z.c j + ∑ l, Z.G l j * β l) = _
    rw [mul_add, htc, hsum, Zonotope.absBound]
  have habs : |t| = 1 := by rw [ht]; split <;> norm_num
  have heq : |Z.absBound j| = |x j| := by rw [← hxj, abs_mul, habs, one_mul]
  have hnonneg : 0 ≤ Z.absBound j := by rw [Zonotope.absBound]; positivity
  rw [abs_of_nonneg hnonneg] at heq
  rw [heq]
  exact h x hx

end
end Real


namespace Float
section
open InflatedContSet
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}

/-- A zonotope whose error box is the point `0` is its nominal part. -/
theorem aux_construct_nominal_point {V : Zonotope (Vec 𝕋 n)}
    (hE : V.I_error = Interval.point fun _ => FloatOps.zero)
    {y : Vec ℝ n} (hy : y ∈ V.construct) : -- --- CONCL ---
    y ∈ nominalSet V := by -- --- PROOF ---
  obtain ⟨z, hz, e, he, rfl⟩ := hy
  have he0 : e = 0 := funext fun i => by
    have h : toReal (V.I_error.inf i) ≤ e i ∧ e i ≤ toReal (V.I_error.sup i) := he i
    rw [hE] at h
    change toReal (zero : 𝕋) ≤ e i ∧ e i ≤ toReal (zero : 𝕋) at h
    rw [toReal_zero] at h
    exact le_antisymm h.2 h.1
  subst he0
  show z + 0 ∈ nominalSet V
  rw [add_zero]
  exact hz


/-- A point of the nominal part reaches no further than `|c| + Σ|G|`, rounded up. -/
theorem aux_abs_nominal_le (V : Zonotope (Vec 𝕋 n)) {z : Vec ℝ n}
    (hz : z ∈ nominalSet V) (j : Fin n) : -- --- CONCL ---
    |z j| ≤ toReal (addUp (absolute (V.c j)) (radius (fun i j => V.G j i) j)) := by -- --- PROOF ---
  obtain ⟨β, hβ, hval⟩ := Zonotope.mem_nominalSet_iff.mp hz
  have hgen := abs_sum_le_radius (d := fun i j => V.G j i) (Δ := fun i j => toReal (V.G j i))
    (fun _ _ => le_refl _) hβ j
  have hup := add_le_addUp (absolute (V.c j)) (radius (fun i j => V.G j i) j)
  rw [toReal_absolute] at hup
  rw [hval j]
  exact le_trans (abs_add_le _ _) (by linarith)


/-- The two ends of the exact interval at a residual `Rs` of the float one: the center's distance
from the stored center plus the radius is at most the residual's larger end. -/
theorem aux_mid_add_rad_le {lo hi C M : ℝ} (hlo : |lo - C| ≤ M) (hhi : |hi - C| ≤ M) :
    |(lo + hi) / 2 - C| + (hi - lo) / 2 ≤ M := by
  obtain ⟨h1, h2⟩ := abs_le.mp hlo
  obtain ⟨h3, h4⟩ := abs_le.mp hhi
  rcases abs_cases ((lo + hi) / 2 - C) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith


/-- The exact `mtimesIntervalMat` is inside the float one. -/
theorem Zonotope.aux_real_mtimesIntervalMat_subset {IMr : CORALean.Real.Interval (Mat ℝ m n)}
    {IMf : Interval (Mat 𝕋 m n)} (hlo : IMr.inf ∈ IMf.construct) (hhi : IMr.sup ∈ IMf.construct)
    (hle : ∀ i j, IMr.inf i j ≤ IMr.sup i j) {Zr : CORALean.Real.Zonotope (Vec ℝ n)}
    {V : Zonotope (Vec 𝕋 n)} (hE : V.I_error = Interval.point fun _ => FloatOps.zero)
    (hZ : Zr.construct ⊆ V.construct) : -- --- CONCL ---
    (CORALean.Real.Zonotope.mtimesIntervalMat IMr Zr).construct ⊆
      (Zonotope.mtimesIntervalMat IMf V).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hxi⟩ : ∃ β : Fin (Zr.h + m) → ℝ, (∀ j, |β j| ≤ 1) ∧ ∀ i, x i
      = (IMr.center *ᵥ Zr.c) i + ∑ l : Fin (Zr.h + m),
        Fin.append (fun l => IMr.center *ᵥ Zr.G l)
          (fun l : Fin m => (Matrix.diagonal (fun i => CORALean.Real.Zonotope.radiusReach IMr Zr i)
            l : Vec ℝ m)) l i * β l :=
    CORALean.Real.Zonotope.mem_construct_iff.mp hx
  -- the point of `Zr` the first generators name, and the box coefficients
  set β1 : Fin Zr.h → ℝ := fun l => β (Fin.castAdd m l) with hβ1
  set β2 : Fin m → ℝ := fun i => β (Fin.natAdd Zr.h i) with hβ2
  set w : Vec ℝ n := fun i => Zr.c i + ∑ l, Zr.G l i * β1 l with hw
  have hwZ : w ∈ Zr.construct :=
    CORALean.Real.Zonotope.mem_construct_iff.mpr ⟨β1, fun l => hβ _, fun _ => rfl⟩
  have hwV : w ∈ V.construct := hZ hwZ
  -- the exact point is `mid w` plus the box part
  set rr : Vec ℝ m := fun i => CORALean.Real.Zonotope.radiusReach IMr Zr i with hrr
  -- written out coordinate by coordinate, the first generators giving `mid w`
  have hxw : ∀ i, x i = (IMr.center *ᵥ w) i + rr i * β2 i := fun i => by
    have h := hxi i
    rw [Fin.sum_univ_add] at h
    have h' : x i = (IMr.center *ᵥ Zr.c) i + (∑ l : Fin Zr.h, (IMr.center *ᵥ Zr.G l) i * β1 l
        + ∑ l : Fin m, Matrix.diagonal rr l i * β2 l) := by
      rw [h]
      congr 2
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [congrFun (Fin.append_left (fun l => IMr.center *ᵥ Zr.G l)
          (fun l : Fin m => (Matrix.diagonal rr l : Vec ℝ m)) l) i]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [congrFun (Fin.append_right (fun l => IMr.center *ᵥ Zr.G l)
          (fun l : Fin m => (Matrix.diagonal rr l : Vec ℝ m)) l) i]
    clear h
    have h := h'
    rw [CORALean.Real.Zonotope.sum_diagonal_mul'] at h
    -- `w` as a vector, so `mid` can be pulled through the sum
    have hwvec : w = Zr.c + ∑ l, β1 l • Zr.G l := funext fun k => by
      simp only [hw, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have hmv : (IMr.center *ᵥ w) i
        = (IMr.center *ᵥ Zr.c) i + ∑ l, (IMr.center *ᵥ Zr.G l) i * β1 l := by
      rw [hwvec, Matrix.mulVec_add, Matrix.mulVec_sum, Pi.add_apply, Finset.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [h, hmv, hrr]
    ring
  -- the stored center, the float residual, and what a point of `V` can be
  set C := Interval.centerMat IMf with hC
  set Rs := Interval.matResidual IMf.inf IMf.sup C with hRs
  have hV0 : (0 : Vec ℝ n) ∈ V.I_error.construct := fun i => by
    show toReal (V.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (V.I_error.sup i)
    rw [hE]
    change toReal (FloatOps.zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (FloatOps.zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩
  obtain ⟨t₀, ht₀, e₀, he₀, hsum⟩ := Zonotope.mtimes_outer C V ⟨w, hwV, rfl⟩
  have hsum' : t₀ + e₀ = toRealMat C *ᵥ w := hsum
  have hRl : (fun i j => IMr.inf i j - toReal (C i j)) ∈ Rs.construct :=
    Interval.sub_mem_matResidual fun i j => Interval.mem_mat_iff.mp hlo i j
  have hRh : (fun i j => IMr.sup i j - toReal (C i j)) ∈ Rs.construct :=
    Interval.sub_mem_matResidual fun i j => Interval.mem_mat_iff.mp hhi i j
  -- the larger end of the float residual bounds both ends of the exact interval
  set mag : Mat 𝕋 m n := fun i j => maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j))
    with hmag
  have hbl : ∀ i j, |IMr.inf i j - toReal (C i j)| ≤ toReal (mag i j) := fun i j => by
    have h := Interval.mem_mat_iff.mp hRl i j
    rw [hmag]
    show _ ≤ toReal (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j)))
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs h.1 h.2
  have hbh : ∀ i j, |IMr.sup i j - toReal (C i j)| ≤ toReal (mag i j) := fun i j => by
    have h := Interval.mem_mat_iff.mp hRh i j
    rw [hmag]
    show _ ≤ toReal (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j)))
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs h.1 h.2
  -- the exact center's distance from the stored one plus the radius is under the magnitude
  have hterm : ∀ i j, |IMr.center i j - toReal (C i j)| + IMr.radius i j ≤ toReal (mag i j) :=
    fun i j => by
      have h := aux_mid_add_rad_le (hbl i j) (hbh i j)
      have hc : IMr.center i j = (IMr.inf i j + IMr.sup i j) / 2 := by
        simp only [CORALean.Real.Interval.center, Matrix.smul_apply, Matrix.add_apply,
          smul_eq_mul]
        ring
      have hr : IMr.radius i j = (IMr.sup i j - IMr.inf i j) / 2 := by
        simp only [CORALean.Real.Interval.radius, Matrix.smul_apply, Matrix.sub_apply,
          smul_eq_mul]
        ring
      rw [hc, hr]
      exact h
  have hrad : ∀ i j, 0 ≤ IMr.radius i j := fun i j => by
    simp only [CORALean.Real.Interval.radius, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    linarith [hle i j]
  -- the reach of `Zr` is under the float reach of `V`
  set ν : Vec 𝕋 n := fun j => addUp (absolute (V.c j)) (radius (fun i j => V.G j i) j) with hν
  have habs : ∀ j, Zr.absBound j ≤ toReal (ν j) := fun j =>
    CORALean.Real.Zonotope.aux_absBound_le_of_abs_le fun y hy =>
      aux_abs_nominal_le V (aux_construct_nominal_point hE (hZ hy)) j
  have hwabs : ∀ j, |w j| ≤ Zr.absBound j := fun j =>
    CORALean.Real.Zonotope.abs_le_absBound (fun l => hβ _) (fun _ => rfl) j
  set v : Vec ℝ m := fun i => ((IMr.center - toRealMat C) *ᵥ w) i + rr i * β2 i with hv
  set b : Vec 𝕋 m := fun i => sumUp fun j => mulUp (mag i j) (ν j) with hb
  have hvb : ∀ i, |v i| ≤ toReal (b i) := fun i => by
    -- the two parts, each a sum over `j` of an entry bound times a reach
    have h1 : |((IMr.center - toRealMat C) *ᵥ w) i|
        ≤ ∑ j, |IMr.center i j - toReal (C i j)| * Zr.absBound j := by
      show |∑ j, (IMr.center i j - toReal (C i j)) * w j| ≤ _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwabs j) (abs_nonneg _)
    -- the box part is nonnegative and at most its radius
    have hrr0 : 0 ≤ rr i := Finset.sum_nonneg fun j _ =>
      mul_nonneg (hrad i j) (by rw [CORALean.Real.Zonotope.absBound]; positivity)
    have h2 : |rr i * β2 i| ≤ ∑ j, IMr.radius i j * Zr.absBound j := by
      rw [abs_mul, abs_of_nonneg hrr0]
      exact mul_le_of_le_one_right hrr0 (hβ _)
    have h3 : ∑ j, |IMr.center i j - toReal (C i j)| * Zr.absBound j
        + ∑ j, IMr.radius i j * Zr.absBound j ≤ ∑ j, toReal (mag i j) * toReal (ν j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have hab : 0 ≤ Zr.absBound j := by rw [CORALean.Real.Zonotope.absBound]; positivity
      calc _ = (|IMr.center i j - toReal (C i j)| + IMr.radius i j) * Zr.absBound j := by ring
        _ ≤ toReal (mag i j) * Zr.absBound j := mul_le_mul_of_nonneg_right (hterm i j) hab
        _ ≤ _ := mul_le_mul_of_nonneg_left (habs j)
          (le_trans (add_nonneg (abs_nonneg _) (hrad i j)) (hterm i j))
    have h4 : ∑ j, toReal (mag i j) * toReal (ν j) ≤ toReal (b i) :=
      le_trans (Finset.sum_le_sum fun j _ => mul_le_mulUp _ _) (sum_le_sumUp _)
    exact le_trans (abs_add_le _ _) (by linarith)
  have hb0 : ∀ i, 0 ≤ toReal (b i) := fun i => le_trans (abs_nonneg _) (hvb i)
  -- the zero error of the residual on `V`'s error box
  have h0 : (0 : Vec ℝ m) ∈ (Interval.mtimesIntervalMat Rs V.I_error).construct := by
    have := Interval.mtimesIntervalMat_outer Rs V.I_error (Set.mem_biUnion hRl ⟨0, hV0, rfl⟩)
    simpa using this
  -- the stored center's image, then one coefficient per coordinate for what is left
  obtain ⟨γ, hγ, ht₀γ⟩ := Zonotope.mem_nominalSet_iff.mp ht₀
  refine ⟨t₀ + v, ?_, e₀ + 0, Interval.plus_outer _ _ (Set.add_mem_add he₀ h0), ?_⟩
  · -- the witness: `mid(M) V`'s coefficients, then one per coordinate scaled to the radius
    refine Zonotope.mem_nominalSet_iff.mpr
      ⟨Fin.append γ (fun i => CORALean.Real.Zonotope.coefficient (toReal (b i)) (v i)), ?_,
        fun i => ?_⟩
    · refine Fin.addCases (fun l => ?_) (fun i => ?_)
      · simpa using hγ l
      · simp only [Fin.append_right]
        exact CORALean.Real.Zonotope.abs_coefficient_le_one (hb0 i) (hvb i)
    · show t₀ i + v i = toReal (mulVecDown C V.c i)
        + ∑ j : Fin (V.h + m), toReal (Fin.append (fun l => mulVecDown C (V.G l))
          (diagonalBlock b) j i) * Fin.append (m := V.h) γ
            (fun i => CORALean.Real.Zonotope.coefficient (toReal (b i)) (v i)) j
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, toReal_diagonalBlock]
      rw [CORALean.Real.Zonotope.sum_diagonal_mul', toRealVec,
        CORALean.Real.Zonotope.mul_coefficient (hvb i), ht₀γ i, add_assoc]
      rfl
  · -- the exact point is the stored center's image plus `v`
    funext i
    show (t₀ + v + (e₀ + 0)) i = x i
    have hx' := hxw i
    have hs := congrFun hsum' i
    simp only [Pi.add_apply] at hs
    rw [hx', hv]
    simp only [Pi.add_apply, Pi.zero_apply, Matrix.sub_mulVec, Pi.sub_apply]
    linarith

end
end Float


/-- The exact orders, over `Real.Zonotope`, inside the float sum. -/
theorem LinearSys.aux_inputTaylorSumZ_subset (sys : LinearSys 𝕋 n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {Wr : CORALean.Real.Zonotope (Vec ℝ n)} {V : Zonotope (Vec 𝕋 n)}
    (hW : Wr.construct ⊆ V.construct) : -- --- CONCL ---
    ∀ i, construct (sys.inputTaylorSum (S := 𝒵)
        (toReal r) Wr i) ⊆ (sys.inputTaylorSumFloat r V i).construct := by -- --- PROOF ---
  -- order `i`'s matrix is in its float box, so the image of `Wr` is in the float product
  have hterm : ∀ i, construct (CORALean.Real.Zonotope.mtimes (sys.inputTerm (toReal r) i) Wr)
      ⊆ (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) V).construct := by
    intro i y hy
    have hy' : y ∈ CORALean.Real.Zonotope.construct
        (CORALean.Real.Zonotope.mtimes (sys.inputTerm (toReal r) i) Wr) := hy
    rw [← CORALean.Real.Zonotope.mtimes_exact] at hy'
    obtain ⟨u, hu, rfl⟩ := hy'
    exact Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋])
      (MatExp.intervalInputTerm (Interval.point sys.A) r i) V
      (Set.mem_biUnion (MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) i)
        (Set.mem_image_of_mem _ (hW hu)))
  intro i
  -- the sum is the previous sum and one more order, each inside its float counterpart
  induction i with
  | zero => exact hterm 0
  | succ i ih =>
    intro y hy
    have hy' : y ∈ CORALean.Real.Zonotope.construct (CORALean.Real.Zonotope.plus
        (sys.inputTaylorSum (S := 𝒵) (toReal r) Wr i)
        (CORALean.Real.Zonotope.mtimes (sys.inputTerm (toReal r) (i + 1)) Wr)) := hy
    rw [← CORALean.Real.Zonotope.plus_exact] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    exact Plus.plus_outer (sys.inputTaylorSumFloat r V i) _
      (Set.add_mem_add (ih ha) (hterm (i + 1) hb))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputSolution_subset_inputSolutionFloat (sys : LinearSys 𝕋 n) {r : 𝕋} {η : ℕ}
    (hr : 0 ≤ toReal r) (hη : sys.IsOrderAdmissibleFloat r r η)
    {Wr : CORALean.Real.Zonotope (Vec ℝ n)} {V : Zonotope (Vec 𝕋 n)}
    (hE : V.I_error = Interval.point fun _ => FloatOps.zero)
    (hW : Wr.construct ⊆ V.construct) : -- --- CONCL ---
    construct (sys.inputSolution (S := 𝒵) (toReal r) η Wr)
      ⊆ (sys.inputSolutionFloat r η V).construct := by -- --- PROOF ---
  set IMr := CORALean.Real.MatExp.inputRemainder (Scalar.toRealMat sys.A) (toReal r) η with hIMr
  set IMf := MatExp.intervalInputRemainder (Interval.point sys.A) r η with hIMf
  intro y hy
  have hy' : y ∈ CORALean.Real.Zonotope.construct (CORALean.Real.Zonotope.plus
      (sys.inputTaylorSum (S := 𝒵) (toReal r) Wr η)
      (CORALean.Real.Zonotope.mtimesIntervalMat IMr Wr)) := hy
  rw [← CORALean.Real.Zonotope.plus_exact] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  -- the remainder's ends are matrices of the exact interval, so of the float one
  have hA : Scalar.toRealMat sys.A ∈ (Interval.point sys.A).construct :=
    Interval.mem_point sys.A
  -- the remainder's bound is nonnegative, so its interval has `inf ≤ sup`
  have hε : ‖toReal r • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2) ≤ 1 / 2 :=
    le_trans (by gcongr; exact MatExp.norm_smul_le_normUpperBound _ r hA) hη.2
  have hE0 := CORALean.Real.MatExp.expRemainderBound_nonneg η hε
  have hmem : ∀ M : Mat ℝ n n, (∀ i j, IMr.inf i j ≤ M i j ∧ M i j ≤ IMr.sup i j) →
      M ∈ IMf.construct := fun M hM =>
    MatExp.inputRemainder_subset_intervalInputRemainder _ hr η hη.2 hA
      (CORALean.Real.Interval.mem_mat_iff.mpr hM)
  have hle : ∀ i j, IMr.inf i j ≤ IMr.sup i j := fun _ _ => by
    show -(toReal r * CORALean.Real.MatExp.expRemainderBound (toReal r • Scalar.toRealMat sys.A) η)
      ≤ toReal r * CORALean.Real.MatExp.expRemainderBound (toReal r • Scalar.toRealMat sys.A) η
    nlinarith [mul_nonneg hr hE0]
  -- the remainder term, through the float interval-matrix product
  have hrem := Zonotope.aux_real_mtimesIntervalMat_subset (IMf := IMf)
    (hmem _ fun i j => ⟨le_rfl, hle i j⟩) (hmem _ fun i j => ⟨hle i j, le_rfl⟩) hle hE hW hb
  have hrem' : b ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) IMf V).construct := by
    show b ∈ ((Zonotope.mtimesIntervalMat IMf V).materialise).construct
    rw [Zonotope.materialise_eq]
    exact hrem
  exact Plus.plus_outer (sys.inputTaylorSumFloat r V η) _
    (Set.add_mem_add (sys.aux_inputTaylorSumZ_subset hr hW η ha) hrem')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
