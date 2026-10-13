import CORALean.HybridDynamics.Operations.GuardIntersectHyperplaneMapFloat
import CORALean.HybridDynamics.Theorems.AbstractionErrorFloatOuter
import CORALean.HybridDynamics.Theorems.HitFactorMemIcc
import CORALean.HybridDynamics.Theorems.HitHessianMatZonoFloatMem
import CORALean.HybridDynamics.Theorems.HitJacobianMemHitJacobianFloat
import CORALean.HybridDynamics.Theorems.HitPointAddEq
import CORALean.HybridDynamics.Theorems.HitPointMemHitPointFloat
import CORALean.HybridDynamics.Theorems.LinearEmbedding
import CORALean.HybridDynamics.Theorems.SdcInputMemSdcInputFloat
import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInputReflected
import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneIntervalFloatOuter
import CORALean.ContSet.Interval.Float.Theorems.RecipOuter
import CORALean.ContSet.Zonotope.Float.Theorems.HalfspaceRangeMem
import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapMatZonoOuter
import CORALean.ContSet.Zonotope.Float.Theorems.RecentreZeroMem
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter

/-!
# The float hyperplane map holds every guard hit of a run from `R₀`

`Location.guardIntersectHyperplaneMapFloat_outer`: a run of the location from `x(0) ∈ R₀` that
is on the hyperplane `nᵀx = d` at a time `t ≤ tmax` is, at `t`, in the set the float guard
mapping returns, whenever it returns one, for `η ≥ 1` Taylor terms; the exact layer's
`Location.guardIntersectHyperplaneMap_outer`, at floats, with the floats read as reals.

The chain is the exact layer's, each real quantity in the float set or interval that encloses
it: `x(t) = x₀ + (Ax₀ + b)t + e` with `b` the float lower end of the box of the exact `b` and
`e` in the float abstraction error plus `t(b_exact − b)` (`GuardMap.abstractionErrorFloat_outer`,
`GuardMap.sdcInput_mem_sdcInputFloat`); the hit is `y_h(x₀) + (−nᵀe/Λ(x₀))(Ax₀ + b) + e`;
`y_h(x₀)` is in `res1` by the exact expansion around the stored centre `ξ` of the reduced `R₀`,
`k`, `L` and the matrix zonotopes at `ξ` enclosed (`GuardMap.hitPoint_mem_hitPointFloat`,
`GuardMap.hitJacobian_mem_hitJacobianFloat`, `GuardMap.hitHessianMatZonoFloat_mem`) and the
remainder a point of the float `quadMapMatZono`; the rest is in `res2`; and a point of the
hyperplane is fixed by the projection onto the hyperplane `(n/‖n‖)ᵀx = d/‖n‖`, one of those the
boxes of the normalized normal allow (`ContSet.projectOnHyperplaneIntervalFloat_outer`).

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic
open Matrix hiding zero one
open NormedSpace MeasureTheory ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}
  [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `s v ∈ [a, b] Z` for `s ∈ [a, b]` and `v ∈ Z`, `[a, b]` the interval matrix `[a, b] I`. -/
theorem aux_hpMapF_smul_mem {a b : 𝕋} {s : ℝ} (h₁ : toReal a ≤ s) (h₂ : s ≤ toReal b)
    {Z : Zonotope (Vec 𝕋 n)} {v : Vec ℝ n} (hv : v ∈ Z.construct) :
    s • v ∈ (Zonotope.mtimesIntervalMat (Interval.smul a b
      (Interval.point (diagonalBlock fun _ => (one : 𝕋)))) Z).construct := by -- --- PROOF ---
  have hone : (1 : Mat ℝ n n) ∈
      (Interval.point (diagonalBlock fun _ : Fin n => (one : 𝕋))).construct := by
    have h := Interval.mem_point (diagonalBlock fun _ : Fin n => (one : 𝕋))
    convert h using 1
    funext i j
    rw [realImage_mat, toRealMat, toReal_diagonalBlock]
    simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply]
  have h := Zonotope.mtimesIntervalMat_outer _ Z
    (Set.mem_biUnion (Interval.smul_outer h₁ h₂ _ hone) ⟨v, hv, rfl⟩)
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h
  exact h

/-- A float certificate that `[lo, hi]` excludes `0`, read as reals. -/
theorem aux_hpMapF_sign {lo hi : 𝕋} (h : (ltStrict zero lo || ltStrict hi zero) = true) :
    0 < toReal lo ∨ toReal hi < 0 := by -- --- PROOF ---
  rcases Bool.or_eq_true_iff.mp h with h | h
  · left
    have := toReal_lt_of_ltStrict h
    rwa [toReal_zero] at this
  · right
    have := toReal_lt_of_ltStrict h
    rwa [toReal_zero] at this

/-- `1/y` of a point of a certified interval lies in `Interval.recip`'s box. -/
theorem aux_hpMapF_recip {lo hi : 𝕋} (h : (ltStrict zero lo || ltStrict hi zero) = true) {y : ℝ}
    (h1 : toReal lo ≤ y) (h2 : y ≤ toReal hi) :
    toReal ((Interval.recip (⟨fun _ => lo, fun _ => hi⟩ : Interval (Vec 𝕋 1))).inf 0) ≤ y⁻¹ ∧
      y⁻¹ ≤ toReal ((Interval.recip (⟨fun _ => lo, fun _ => hi⟩ : Interval (Vec 𝕋 1))).sup 0) :=
  Interval.recip_outer (⟨fun _ => lo, fun _ => hi⟩ : Interval (Vec 𝕋 1))
    (fun _ => Bool.or_eq_true_iff.mp h) ⟨fun _ : Fin 1 => y, fun _ => ⟨h1, h2⟩, rfl⟩ 0

/-- `1/y²` of a point of a certified interval lies in `[φ̲, φ̄]`, `1/max(|lo|, |hi|)²` rounded
down and `1/min(|lo|, |hi|)²` rounded up, the latter's denominator certified positive. -/
theorem aux_hpMapF_sq {lo hi : 𝕋} (h : (ltStrict zero lo || ltStrict hi zero) = true)
    (hm : ltStrict zero (mulDown (minimum (absolute lo) (absolute hi))
      (minimum (absolute lo) (absolute hi))) = true) {y : ℝ} (h1 : toReal lo ≤ y)
    (h2 : y ≤ toReal hi) :
    toReal (divDown one (mulUp (maximum (absolute lo) (absolute hi))
        (maximum (absolute lo) (absolute hi)))) ≤ 1 / y ^ 2 ∧
      1 / y ^ 2 ≤ toReal (divUp one (mulDown (minimum (absolute lo) (absolute hi))
        (minimum (absolute lo) (absolute hi)))) := by -- --- PROOF ---
  set m := minimum (absolute lo) (absolute hi)
  set M := maximum (absolute lo) (absolute hi)
  have hmr : toReal m = min |toReal lo| |toReal hi| := by
    rw [toReal_minimum, toReal_absolute, toReal_absolute]
  have hMr : toReal M = max |toReal lo| |toReal hi| := by
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
  -- `min(|lo|, |hi|) ≤ |y| ≤ max(|lo|, |hi|)`, `y` on one side of `0`
  have hy : toReal m ≤ |y| ∧ |y| ≤ toReal M := by
    rw [hmr, hMr]
    rcases aux_hpMapF_sign h with hl | hh
    · rw [abs_of_pos hl, abs_of_pos (hl.trans_le (h1.trans h2)), abs_of_pos (hl.trans_le h1)]
      exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩
    · have hy0 : y < 0 := h2.trans_lt hh
      rw [abs_of_neg hh, abs_of_neg (h1.trans_lt hy0), abs_of_neg hy0]
      exact ⟨(min_le_right _ _).trans (by linarith), (by linarith : -y ≤ -toReal lo).trans
        (le_max_left _ _)⟩
  have hm0 : 0 ≤ toReal m := by rw [hmr]; exact le_min (abs_nonneg _) (abs_nonneg _)
  have hq : 0 < toReal (mulDown m m) := by
    have := toReal_lt_of_ltStrict hm
    rwa [toReal_zero] at this
  -- `q ≤ y² ≤ P`, `q` and `P` the rounded squares
  have hqy : toReal (mulDown m m) ≤ y ^ 2 := by
    rw [← sq_abs]
    exact (mulDown_le_mul m m).trans (by nlinarith [hy.1])
  have hyP : y ^ 2 ≤ toReal (mulUp M M) := by
    rw [← sq_abs]
    exact (by nlinarith [hy.1, hy.2] : |y| ^ 2 ≤ toReal M * toReal M).trans (mul_le_mulUp M M)
  have hy2 : 0 < y ^ 2 := hq.trans_le hqy
  constructor
  · have := divDown_le_div (one : 𝕋) (mulUp M M) (hy2.trans_le hyP)
    rw [toReal_one] at this
    exact this.trans (one_div_le_one_div_of_le hy2 hyP)
  · have := div_le_divUp (one : 𝕋) (mulDown m m) hq
    rw [toReal_one] at this
    exact (one_div_le_one_div_of_le hq hqy).trans this

/-- A point within `g` of `c` is `c + κg` for some `|κ| ≤ 1`. -/
theorem aux_hpMapF_factor {y c g : ℝ} (h : |y - c| ≤ g) :
    ∃ κ : ℝ, |κ| ≤ 1 ∧ y = c + κ * g := by -- --- PROOF ---
  rcases eq_or_lt_of_le ((abs_nonneg _).trans h) with h0 | hpos
  · refine ⟨0, by norm_num, ?_⟩
    rw [← h0] at h
    have := abs_nonpos_iff.mp h
    linarith
  · refine ⟨(y - c) / g, ?_, by field_simp; ring⟩
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact h

/-- A point of `[lo, hi]` is within `τ_g = max(⌈hi − τ_c⌉, ⌈τ_c − lo⌉)` of any float `τ_c`. -/
theorem aux_hpMapF_centre {lo hi c : 𝕋} {y : ℝ} (h1 : toReal lo ≤ y) (h2 : y ≤ toReal hi) :
    |y - toReal c| ≤ toReal (maximum (subUp hi c) (subUp c lo)) := by -- --- PROOF ---
  have e1 := sub_le_subUp hi c
  have e2 := sub_le_subUp c lo
  rw [toReal_maximum]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [le_max_right (toReal (subUp hi c)) (toReal (subUp c lo))]
  · linarith [le_max_left (toReal (subUp hi c)) (toReal (subUp c lo))]

/-- `res1`: the hitting point `y_h(x₀)` of a point of `R₀`, given `Λ ≠ 0` and `1/Λ²` within
`[φ̲, φ̄]` on a convex `S` holding `x₀` and the stored centre `ξ` of `R₀red`, and `τ(ξ)` within
`τ_g` of `τ_c`. -/
theorem aux_hpMapF_res1 (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋) (R₀ R0red : Zonotope (Vec 𝕋 n))
    (hcen : R0red.c = R₀.c) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ R₀.construct)
    (hx₀' : x₀ ∈ R0red.construct) {S : Set (Vec ℝ n)} (hS : Convex ℝ S)
    (hξS : toRealVec R0red.c ∈ S) (hx₀S : x₀ ∈ S)
    (hΛne : ∀ x ∈ S, toRealVec nv ⬝ᵥ (toRealMat A *ᵥ x + toRealVec b) ≠ 0) {φlo φhi : 𝕋}
    (hφ : ∀ x ∈ S, toReal φlo ≤ 1 / (toRealVec nv ⬝ᵥ (toRealMat A *ᵥ x + toRealVec b)) ^ 2 ∧
      1 / (toRealVec nv ⬝ᵥ (toRealMat A *ᵥ x + toRealVec b)) ^ 2 ≤ toReal φhi)
    {τc τg : 𝕋} (hτ : |(toReal d - toRealVec nv ⬝ᵥ toRealVec R0red.c) *
      (toRealVec nv ⬝ᵥ (toRealMat A *ᵥ toRealVec R0red.c + toRealVec b))⁻¹ - toReal τc|
        ≤ toReal τg)
    {k : Interval (Vec 𝕋 n)} {Lk : Interval (Mat 𝕋 n n)}
    (hk : GuardMap.hitPointFloat A b nv d R0red.c = some k)
    (hL : GuardMap.hitJacobianFloat A b nv d R0red.c = some Lk) :
    -- `k ⊕ L R₀_ ⊕ [φ̲/2, φ̄/2] R_quad`, as the guard mapping builds it
    GuardMap.hitPoint (toRealMat A) (toRealVec b) (toRealVec nv) (toReal d) x₀ ∈
      ((k.zonotope.plus (Zonotope.mtimesIntervalMat Lk R₀.recentre)).plus
        (Zonotope.mtimesIntervalMat (Interval.smul (half φlo) (half φhi)
          (Interval.point (diagonalBlock fun _ => (one : 𝕋))))
          (Zonotope.quadMapMatZono
            (fun i => ⟨fun l m => addDown
                ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).c l m)
                ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).E.inf l m),
              fun l m => addUp ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).c l m)
                ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).E.sup l m)⟩)
            (fun (j : Fin (1 + R0red.h + R0red.h)) i =>
              (GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).G j)
            R0red.recentre))).construct := by -- --- PROOF ---
  set Ar := toRealMat A with hAr
  set br := toRealVec b with hbr
  set nr := toRealVec nv with hnr
  set ξ := toRealVec R0red.c with hξdef
  -- the exact expansion around `ξ`
  set ν : Vec ℝ n := x₀ - ξ with hν
  have hx₀ν : ξ + ν = x₀ := by rw [hν]; abel
  have hexp := GuardMap.hitPoint_add_eq Ar br nr (toReal d) ξ ν (hΛne ξ hξS)
    (by rw [hx₀ν]; exact hΛne x₀ hx₀S)
  rw [hx₀ν] at hexp
  have hφm := GuardMap.hitFactor_mem_Icc Ar br nr hS hΛne hφ hξS hx₀S
  -- `Θ(ξ)/Λ(ξ) = ψ_c + κψ_g`: `τ(ξ) = τ_c + κτ_g`
  obtain ⟨κ, hκ, hκeq⟩ := aux_hpMapF_factor hτ
  set Υ : Vec ℝ n := nr ᵥ* Ar with hΥ
  set ψc : Vec ℝ n := -nr - toReal τc • Υ with hψc
  set ψg : Vec ℝ n := -(toReal τg • Υ) with hψg
  have hψ : (nr ⬝ᵥ (Ar *ᵥ ξ + br))⁻¹ • (-((nr ⬝ᵥ (Ar *ᵥ ξ + br)) • nr)
      - (toReal d - nr ⬝ᵥ ξ) • (nr ᵥ* Ar)) = ψc + κ • ψg := by
    have hne := hΛne ξ hξS
    funext i
    simp only [hψc, hψg, hΥ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    have e : (nr ⬝ᵥ (Ar *ᵥ ξ + br))⁻¹ * (-((nr ⬝ᵥ (Ar *ᵥ ξ + br)) * nr i)
        - (toReal d - nr ⬝ᵥ ξ) * (nr ᵥ* Ar) i)
        = -nr i - ((toReal d - nr ⬝ᵥ ξ) * (nr ⬝ᵥ (Ar *ᵥ ξ + br))⁻¹) * (nr ᵥ* Ar) i := by
      field_simp
    rw [e, hκeq]
    ring
  -- `Q⁽ⁱ⁾(ξ)`: the exact matrix zonotopes' point at `(κ, 0, 0)`, then the float ones'
  set R0r : Real.Zonotope (Vec ℝ n) := ⟨R0red.h, ξ, fun j => toRealVec (R0red.G j)⟩ with hR0r
  have hξeq : R0r.c + ∑ j, (0 : Fin R0red.h → ℝ) j • R0r.G j = ξ := by simp [hR0r]
  set fac : Fin (1 + R0red.h + R0red.h) → ℝ :=
    Fin.append (Fin.append ![κ] (0 : Fin R0red.h → ℝ)) fun α => κ * (0 : Fin R0red.h → ℝ) α
    with hfac
  have hQ : ∀ i, ∃ E ∈ (GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).E.construct,
      GuardMap.hitHessianNum Ar br nr (toReal d) ξ i
        = (toRealMat (GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).c + E)
          + ∑ j, fac j • toRealMat ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).G j) :=
    fun i => by
      have h := GuardMap.hitHessianNum_eq_hitHessianMatZono Ar br nr (toReal d) R0r ψc ψg i 0 κ
        (by rw [hξeq]; exact hψ)
      rw [hξeq] at h
      obtain ⟨E, hE, hEeq⟩ := GuardMap.hitHessianMatZonoFloat_mem A b nv d R0red τc τg i hκ
      exact ⟨E, hE, h.trans hEeq⟩
  choose E hE hEeq using hQ
  -- the factors are in `[-1, 1]`, and `ν ∈ R₀red ⊖ ξ`: the remainder is a point of `R_quad`
  have hfac1 : ∀ j, |fac j| ≤ 1 := fun j => by
    refine Fin.addCases (fun j => ?_) (fun α => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun α => ?_) j
      · rw [hfac, Fin.append_left, Fin.append_left, Fin.fin_one_eq_zero j]; simpa using hκ
      · rw [hfac, Fin.append_left, Fin.append_right]; simp
    · rw [hfac, Fin.append_right]; simp
  have hνmem : ν ∈ R0red.recentre.construct := Zonotope.sub_centre_mem_recentre hx₀'
  have hqmem : (fun i => ν ⬝ᵥ (GuardMap.hitHessianNum Ar br nr (toReal d) ξ i *ᵥ ν))
      ∈ (Zonotope.quadMapMatZono
            (fun i => ⟨fun l m => addDown
                ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).c l m)
                ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).E.inf l m),
              fun l m => addUp ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).c l m)
                ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).E.sup l m)⟩)
            (fun (j : Fin (1 + R0red.h + R0red.h)) i =>
              (GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).G j)
            R0red.recentre).construct := by
    refine Zonotope.quadMapMatZono_outer _ _ _ ⟨ν, hνmem, fun i => toRealMat
      (GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).c + E i, fun i => ?_, fac, hfac1,
      fun i => by dsimp only; exact congrArg (fun M => ν ⬝ᵥ (M *ᵥ ν)) (hEeq i)⟩
    -- `c + E` within the directed sums of the centre and the box
    refine Interval.mem_mat_iff.mpr fun l m => ?_
    have hEl := Interval.mem_mat_iff.mp (hE i) l m
    have h1 := addDown_le_add ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).c l m)
      ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).E.inf l m)
    have h2 := add_le_addUp ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).c l m)
      ((GuardMap.hitHessianMatZonoFloat A b nv d R0red τc τg i).E.sup l m)
    simp only [Matrix.add_apply, toRealMat]
    constructor <;> linarith [hEl.1, hEl.2]
  -- assemble `k + Lν + ½φq`
  rw [hexp]
  refine Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.plus_outer _ _ (Set.add_mem_add
    (Interval.zonotope_contains _ (GuardMap.hitPoint_mem_hitPointFloat A b nv d R0red.c hk).2)
    ?_)) ?_)
  · have hν' : ν = x₀ - toRealVec R₀.c := by rw [hν, hξdef, hcen]
    rw [hν']
    exact Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion
      (GuardMap.hitJacobian_mem_hitJacobianFloat A b nv d R0red.c hL)
      ⟨_, Zonotope.sub_centre_mem_recentre hx₀, rfl⟩)
  · rw [smul_smul]
    refine aux_hpMapF_smul_mem ?_ ?_ hqmem
    · rw [toReal_half]; linarith [hφm.1]
    · rw [toReal_half]; linarith [hφm.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.4] at floats: a run from `R₀` on the hyperplane at `t ≤ tmax` is in the float
mapped set, `η ≥ 1`. -/
theorem Location.guardIntersectHyperplaneMapFloat_outer
    (ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) G L 𝕋 n)
    (nv : Vec 𝕋 n) (d : 𝕋) (R₀ : Zonotope (Vec 𝕋 n)) (tmax : 𝕋) {η : ℕ}
    (guardOrder zonotopeOrder p : ℕ) (hη : 1 ≤ η) {τ : ℝ} {x u : ℝ → Vec ℝ n}
    (traj : ℓ.Trajectory τ x u) (h₀ : x 0 ∈ R₀.construct) {t : ℝ} (ht : t ∈ Set.Icc 0 τ)
    (htmax : t ≤ toReal tmax) (hhit : toRealVec nv ⬝ᵥ x t = toReal d) {Z : Zonotope (Vec 𝕋 n)}
    (hZ : ℓ.guardIntersectHyperplaneMapFloat nv d R₀ tmax η guardOrder zonotopeOrder p = some Z) :
    x t ∈ Z.construct := by -- --- PROOF ---
  set x₀ := x 0 with hx₀def
  set Ar := toRealMat ℓ.dynamics.A with hAr
  set nr := toRealVec nv with hnr
  have htm0 : 0 ≤ toReal tmax := ht.1.trans htmax
  have hth : 0 ≤ toReal (half tmax) := by rw [toReal_half]; linarith
  obtain ⟨bI, hbI⟩ : ∃ v, v = GuardMap.sdcInputFloat ℓ.dynamics.A ℓ.U.c (half tmax) η R₀.c :=
    ⟨_, rfl⟩
  set br := toRealVec bI.inf with hbr
  obtain ⟨R0red, hR0red⟩ : ∃ Z', Z' = R₀.reduceGirard guardOrder := ⟨_, rfl⟩
  have hcen : R0red.c = R₀.c := by
    rw [hR0red]
    unfold Zonotope.reduceGirard
    split_ifs <;> rfl
  have hsub : ∀ y ∈ R₀.construct, y ∈ R0red.construct :=
    fun y hy => by rw [hR0red]; exact Zonotope.reduceGirard_outer R₀ guardOrder hy
  -- the returned set, and the float tests it passed
  simp only [Location.guardIntersectHyperplaneMapFloat, Zonotope.materialise_eq,
    Interval.materialiseMat_eq, Vector.getElem_ofFn, Fin.eta] at hZ
  rw [← hbI, ← hR0red] at hZ
  split at hZ
  · rename_i k Lk hk hL
    split_ifs at hZ with hc
    obtain rfl := Option.some.inj hZ
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hcΛ, hcden⟩, hcm⟩, hcnrm⟩, hcA⟩ := hc
    -- the run, in closed form
    have tr := (traj.linearSys (R₀ := R₀) h₀).trajectory (convex_Icc 0 τ) ⟨le_rfl, traj.nonneg⟩
      (Zonotope.isCompact_construct ℓ.U).isBounded
    have hvoc := tr.variation_of_constants (a := 0) (b := t) (Set.Icc_subset_Icc_right ht.2)
      le_rfl ht.1 (Zonotope.isCompact_construct ℓ.U).isBounded
    simp only [sub_zero] at hvoc
    have hvoc' : x t = exp (t • Ar) *ᵥ x₀ + ∫ s in (0:ℝ)..t, exp ((t - s) • Ar) *ᵥ u s := hvoc
    have hmeas := tr.aestronglyMeasurable_input_reflected (c := t) (r := t)
      (by rw [sub_self]; exact Set.Icc_subset_Icc_right ht.2)
    have hu : ∀ s ∈ Set.Ioc (0:ℝ) t, u (t - s) ∈ ℓ.U.construct := fun s hs =>
      traj.input (t - s) ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
    have hUn : ℓ.U.construct.Nonempty := ⟨u 0, traj.input 0 ⟨le_rfl, traj.nonneg⟩⟩
    -- its error to the constant flow of the exact `b`, then of the float `b̲`
    have he := GuardMap.abstractionErrorFloat_outer ℓ.dynamics.A ℓ.U R0red hη ⟨ht.1, htmax⟩ hth
      hcA      (hsub x₀ h₀) hUn hu hmeas
    rw [hcen] at he
    obtain ⟨btrue, hbtrue⟩ : ∃ v, v = GuardMap.sdcInput (toRealMat ℓ.dynamics.A) (toRealVec ℓ.U.c)
        (toReal (half tmax)) η (toRealVec R₀.c) := ⟨_, rfl⟩
    have hbmem := GuardMap.sdcInput_mem_sdcInputFloat ℓ.dynamics.A ℓ.U.c η R₀.c hth
    rw [← hbI] at hbmem
    rw [← hbtrue] at hbmem he
    -- `e`, the error to the constant flow of `b̲`, splits into the two parts
    obtain ⟨e, he_def⟩ : ∃ v, v = x t - GuardMap.sdcFlow Ar br x₀ t := ⟨_, rfl⟩
    have hesplit : e = (exp (t • Ar) *ᵥ x₀ + (∫ s in (0:ℝ)..t, exp ((t - s) • Ar) *ᵥ u s)
        - GuardMap.sdcFlow Ar btrue x₀ t) + t • (btrue - br) := by
      rw [he_def, hvoc']
      simp only [GuardMap.sdcFlow]
      module
    have he' : e ∈ ((GuardMap.abstractionErrorFloat ℓ.dynamics.A ℓ.U R0red (half tmax) tmax η).plus
        (⟨fun i => Interval.mulLo zero tmax zero (subUp (bI.sup i) (bI.inf i)),
          fun i => Interval.mulHi zero tmax zero (subUp (bI.sup i) (bI.inf i))⟩ :
            Interval (Vec 𝕋 n)).zonotope).construct := by
      rw [hesplit]
      refine Zonotope.plus_outer _ _ (Set.add_mem_add he (Interval.zonotope_contains _
        fun i => ?_))
      -- `t(b − b̲)ᵢ` between the corners of `[0, tmax]` and `[0, b̄ − b̲]`
      have hb : toReal (bI.inf i) ≤ btrue i ∧ btrue i ≤ toReal (bI.sup i) := hbmem i
      have hw := sub_le_subUp (bI.sup i) (bI.inf i)
      have h := Interval.mul_between_corners (a := zero) (b := tmax) (c := zero)
        (d := subUp (bI.sup i) (bI.inf i)) (y := t) (x := btrue i - br i)
        (by rw [toReal_zero]; exact ht.1) htmax
        (by rw [toReal_zero]; exact sub_nonneg.mpr hb.1) (by
          show btrue i - toReal (bI.inf i) ≤ _
          linarith [hb.2])
      exact h
    have hxt : x t = x₀ + t • (Ar *ᵥ x₀ + br) + e := by
      rw [he_def, GuardMap.sdcFlow]; abel
    -- `Λ(x₀) ≠ 0`: the denominator's range over `AR₀ + b`
    have hflow : ∀ (Z' : Zonotope (Vec 𝕋 n)) y, y ∈ Z'.construct →
        Ar *ᵥ y + br ∈ ((Zonotope.mtimes ℓ.dynamics.A Z').plus (Zonotope.point bI.inf)).construct :=
      fun Z' y hy => Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.mtimes_outer ℓ.dynamics.A Z'
        ⟨y, hy, rfl⟩) (by rw [Zonotope.construct_point]; rfl))
    have hrange : ∀ (Z' : Zonotope (Vec 𝕋 n)) y, y ∈ Z'.construct →
        toReal (((Zonotope.mtimes ℓ.dynamics.A Z').plus (Zonotope.point bI.inf)).halfspaceRange nv
          zero).1
          ≤ nr ⬝ᵥ (Ar *ᵥ y + br) ∧ nr ⬝ᵥ (Ar *ᵥ y + br) ≤
          toReal (((Zonotope.mtimes ℓ.dynamics.A Z').plus (Zonotope.point bI.inf)).halfspaceRange
            nv zero).2 :=
      fun Z' y hy => by
        have h := Zonotope.halfspaceRange_mem nv zero (hflow Z' y hy)
        rw [toReal_zero, sub_zero] at h
        exact h
    have hden := hrange R₀ x₀ h₀
    have hΛ0 : nr ⬝ᵥ (Ar *ᵥ x₀ + br) ≠ 0 := by
      rcases aux_hpMapF_sign hcden with h | h
      · exact (lt_of_lt_of_le h hden.1).ne'
      · exact (lt_of_le_of_lt hden.2 h).ne
    -- the hit, as `y_h(x₀) + (−nᵀe/Λ(x₀))(Ax₀ + b) + e`
    have hsplit : x t = GuardMap.hitPoint Ar br nr (toReal d) x₀
        + ((-(nr ⬝ᵥ e) / (nr ⬝ᵥ (Ar *ᵥ x₀ + br))) • (Ar *ᵥ x₀ + br) + e) := by
      have hhit' : nr ⬝ᵥ (x₀ + t • (Ar *ᵥ x₀ + br) + e) = toReal d := by rw [← hxt]; exact hhit
      have htime : t = (toReal d - nr ⬝ᵥ x₀ - nr ⬝ᵥ e) / (nr ⬝ᵥ (Ar *ᵥ x₀ + br)) := by
        rw [eq_div_iff hΛ0, ← hhit']
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
        ring
      rw [hxt, GuardMap.hitPoint]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [htime]
      field_simp
      ring
    -- the convex set `R₀red ⊖ ξ ⊕ ξ` the ranges are taken over, holding `ξ` and `R₀red`
    have hhull : ∀ y ∈ R0red.construct,
        y ∈ (R0red.recentre.plus (Zonotope.point R0red.c)).construct :=
      fun y hy => by
        have h := Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.sub_centre_mem_recentre hy)
          (show toRealVec R0red.c ∈ (Zonotope.point R0red.c).construct by
            rw [Zonotope.construct_point]; rfl))
        rwa [sub_add_cancel] at h
    have hξS : toRealVec R0red.c ∈ (R0red.recentre.plus (Zonotope.point R0red.c)).construct := by
      have h := Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.zero_mem_recentre R0red)
        (show toRealVec R0red.c ∈ (Zonotope.point R0red.c).construct by
            rw [Zonotope.construct_point]; rfl))
      rwa [zero_add] at h
    have hx₀S := hhull x₀ (hsub x₀ h₀)
    have hΛS := fun y hy => hrange (R0red.recentre.plus (Zonotope.point R0red.c)) y hy
    -- `τ(ξ)` within `τ_g` of `τ_c`
    have hdξ : toReal ((R0red.recentre.plus (Zonotope.point R0red.c)).halfspaceRange nv d).1
        ≤ nr ⬝ᵥ toRealVec R0red.c - toReal d ∧ nr ⬝ᵥ toRealVec R0red.c - toReal d
        ≤ toReal ((R0red.recentre.plus (Zonotope.point R0red.c)).halfspaceRange nv d).2 :=
      Zonotope.halfspaceRange_mem nv d hξS
    have hinvξ := aux_hpMapF_recip hcΛ (hΛS _ hξS).1 (hΛS _ hξS).2
    have hτ := Interval.mul_between_corners (y := toReal d - nr ⬝ᵥ toRealVec R0red.c)
      (a := neg ((R0red.recentre.plus (Zonotope.point R0red.c)).halfspaceRange nv d).2)
      (b := neg ((R0red.recentre.plus (Zonotope.point R0red.c)).halfspaceRange nv d).1)
      (by rw [toReal_neg]; linarith [hdξ.2]) (by rw [toReal_neg]; linarith [hdξ.1])
      hinvξ.1 hinvξ.2
    -- `Λ ≠ 0` and `1/Λ² ∈ [φ̲, φ̄]` on the hull
    have hΛneS : ∀ y ∈ (R0red.recentre.plus (Zonotope.point R0red.c)).construct,
        nr ⬝ᵥ (Ar *ᵥ y + br) ≠ 0 := fun y hy => by
      rcases aux_hpMapF_sign hcΛ with h | h
      · exact (lt_of_lt_of_le h (hΛS y hy).1).ne'
      · exact (lt_of_le_of_lt (hΛS y hy).2 h).ne
    have hφS := fun y hy => aux_hpMapF_sq hcΛ hcm (hΛS y hy).1 (hΛS y hy).2
    -- `res2` holds `(−nᵀe/Λ(x₀))(Ax₀ + b) + e`
    have hnum := Zonotope.halfspaceRange_mem (fun i => neg (nv i)) zero he'
    have hneg : toRealVec (fun i => neg (nv i)) = -nr := funext fun i => toReal_neg (nv i)
    rw [hneg, toReal_zero, sub_zero, neg_dotProduct] at hnum
    have hinv0 := aux_hpMapF_recip hcden hden.1 hden.2
    have hI := Interval.mul_between_corners hnum.1 hnum.2 hinv0.1 hinv0.2
    have hres2 : (-(nr ⬝ᵥ e) / (nr ⬝ᵥ (Ar *ᵥ x₀ + br))) • (Ar *ᵥ x₀ + br) + e ∈ _ :=
      Zonotope.plus_outer _ _ (Set.add_mem_add (by
        rw [div_eq_mul_inv]
        exact aux_hpMapF_smul_mem hI.1 hI.2 (hflow R₀ x₀ h₀)) he')
    -- `n/‖n‖` and `d/‖n‖` in their boxes
    set nrm := Real.sqrt (nr ⬝ᵥ nr) with hnrm
    have hlo : toReal (sqrtDown p (dotDown nv nv)) ≤ nrm :=
      (sqrtDown_le p _).trans (Real.sqrt_le_sqrt (dotDown_le nv nv))
    have hhi : nrm ≤ toReal (sqrtUp p (dotUp nv nv)) :=
      (Real.sqrt_le_sqrt (le_dotUp nv nv)).trans (le_sqrtUp p _)
    have hlo0 : 0 < toReal (sqrtDown p (dotDown nv nv)) := by
      have := toReal_lt_of_ltStrict hcnrm
      rwa [toReal_zero] at this
    have hnrm0 : 0 < nrm := hlo0.trans_le hlo
    have hr : toReal (divDown one (sqrtUp p (dotUp nv nv))) ≤ nrm⁻¹ ∧
        nrm⁻¹ ≤ toReal (divUp one (sqrtDown p (dotDown nv nv))) := by
      have h1 := divDown_le_div (one : 𝕋) (sqrtUp p (dotUp nv nv)) (hnrm0.trans_le hhi)
      have h2 := div_le_divUp (one : 𝕋) (sqrtDown p (dotDown nv nv)) hlo0
      rw [toReal_one] at h1 h2
      rw [inv_eq_one_div]
      exact ⟨h1.trans (one_div_le_one_div_of_le hnrm0 hhi),
        (one_div_le_one_div_of_le hlo0 hlo).trans h2⟩
    have hδ := Interval.mul_between_corners (le_refl (toReal d)) (le_refl (toReal d)) hr.1 hr.2
    -- a point of the hyperplane is its own projection
    have hproj : x t - ((nrm⁻¹ • nr) ⬝ᵥ x t - toReal d * nrm⁻¹) • (nrm⁻¹ • nr) = x t := by
      rw [smul_dotProduct, hhit, smul_eq_mul, mul_comm, sub_self, zero_smul, sub_zero]
    refine ContSet.projectOnHyperplaneIntervalFloat_outer (S := fun n => Zonotope (Vec 𝕋 n)) _ _ _ _
      (cr := nrm⁻¹ • nr)
      (fun i => ?_) hδ.1 hδ.2 ⟨x t, ?_, hproj⟩
    · -- `n/‖n‖`, entry by entry
      have h := Interval.mul_between_corners (le_refl (toReal (nv i))) (le_refl (toReal (nv i)))
        hr.1 hr.2
      show toReal _ ≤ nrm⁻¹ * toReal (nv i) ∧ nrm⁻¹ * toReal (nv i) ≤ toReal _
      rw [mul_comm]
      exact h
    · -- the hit is in the reduced `res1 ⊕ res2`
      refine Zonotope.reduceGirard_outer _ _ ?_
      rw [hsplit]
      -- `res1` holds `y_h(x₀)`, `τ(ξ)` within `τ_g` of `τ_c`
      exact Zonotope.plus_outer _ _ (Set.add_mem_add (aux_hpMapF_res1 ℓ.dynamics.A bI.inf nv d R₀
        R0red hcen h₀ (hsub x₀ h₀) (Zonotope.convex_construct _) hξS hx₀S hΛneS hφS
        (aux_hpMapF_centre hτ.1 hτ.2) hk hL) hres2)
  · simp at hZ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
