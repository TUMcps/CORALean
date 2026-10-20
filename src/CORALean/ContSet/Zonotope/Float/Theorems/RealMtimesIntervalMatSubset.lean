module

public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsBoundLeOfAbsLe
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# The exact `mtimesIntervalMat` is inside the float one

The exact layer's `Real.Zonotope.mtimesIntervalMat IMr Zr` is `mid(IMr) w` plus a box of reach
`Σ_j rad(IMr)_{ij} absBound_j(Zr)` in each coordinate, `w` a point of `Zr`. The float
`mtimesIntervalMat IMf V` holds `mid(IMf) w` (`mtimes_outer`) plus any vector `v` with
`|v_i| ≤ Σ_j mag(IMf - mid(IMf))_{ij} (|c_j| + Σ|G_j|)`, by the witness of
`mtimesIntervalMat_outer`. The distance `mid(IMr) w - mid(IMf) w` and the box together stay
under that, because both ends of `IMr` are matrices of `IMf` and so lie in the float residual:
`|mid - C| + rad = max(|inf - C|, |sup - C|)`. The float `V` is asked to have error box `{0}`, so
that its points are its nominal part and the exact `absBound` is at most the float reach.

## Inputs
* `IMr` – real interval matrix
* `IMf` – float interval matrix
* `Zr` – real zonotope
* `V` – float zonotope

## Hypotheses
* `hlo` – lower end lies in the float interval matrix
* `hhi` – upper end lies in the float interval matrix
* `hle` – real interval matrix ordered
* `hE` – float error box is zero
* `hZ` – real zonotope lies in the float one

## Conclusion
* exact interval matrix product is contained in the float one
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.real_mtimesIntervalMat_subset {IMr : CORALean.Real.Interval (Mat ℝ m n)}
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
    CORALean.Real.Zonotope.absBound_le_of_abs_le fun y hy =>
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


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
