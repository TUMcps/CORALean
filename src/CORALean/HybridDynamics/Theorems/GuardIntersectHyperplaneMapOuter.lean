import CORALean.HybridDynamics.Operations.GuardIntersectHyperplaneMap
import CORALean.HybridDynamics.Theorems.AbstractionErrorOuter
import CORALean.HybridDynamics.Theorems.HitPointAddEq
import CORALean.HybridDynamics.Theorems.HitFactorMemIcc
import CORALean.HybridDynamics.Theorems.HitHessianNumEqHitHessianMatZono
import CORALean.HybridDynamics.Theorems.LinearEmbedding
import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInputReflected
import CORALean.ContSet.ContSet.Theorems.ProjectOnHyperplaneOuter
import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapMatZonoOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter

/-!
# The hyperplane map holds every guard hit of a run from `R₀`

`Location.guardIntersectHyperplaneMap_outer`: a run of the location from `x(0) ∈ R₀` that is on
the hyperplane `nᵀx = d` at a time `t ≤ tmax` is, at `t`, in the set the guard mapping returns,
whenever it returns one (`some`: the intervals of `Λ` it divides by exclude `0`), for
`η ≥ 1` Taylor terms. No hypothesis on the run beyond its being one, and none on the result.

The chain is [1]'s: `x(t) = x₀ + (Ax₀ + b)t + e` with `e` in the abstraction error `E`
(`GuardMap.abstractionError_outer`, [1, Eq. 13]); a state of that form on the hyperplane is
`y_h(x₀) + (−nᵀe/Λ(x₀))(Ax₀ + b) + e` ([1, Eq. 15]); `y_h(x₀)` is in `res1` by the exact
expansion `GuardMap.hitPoint_add_eq` around the centre `ξ` of the reduced `R₀`, whose
remainder `½φ(νᵀQ⁽ⁱ⁾(ξ)ν)ᵢ` is a point of `R_quad` by [1, Thm. 1] with the factors of `ξ` in the
matrix zonotopes of [1, Prop. 3] (`GuardMap.hitHessianNum_eq_hitHessianMatZono`, at the
one-factor `ψ`) and `φ ∈ [φ̲, φ̄]` (`GuardMap.hitFactor_mem_Icc`); the rest is in `res2`; and a
point of the hyperplane is fixed by the projection onto it. This is the route of
`GuardMap.hitSet_subset_hitEnclosure`, with CORA's `R₀` (not its reduction) under `L`, CORA's
interval products, and the reduction and projection after.

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

open CORALean.Real Matrix NormedSpace MeasureTheory ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `nᵀx − d` of a point of `Z` lies in the range `Zonotope.halfspaceRange` computes. -/
theorem aux_hpMap_range {v : Vec ℝ n} {d : ℝ} {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ Z.construct) :
    (Z.halfspaceRange v d).1 ≤ v ⬝ᵥ x - d ∧
      v ⬝ᵥ x - d ≤ (Z.halfspaceRange v d).2 := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx
  have hb : |∑ i, β i * v ⬝ᵥ Z.G i| ≤ ∑ i, |v ⬝ᵥ Z.G i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hβ i)
  have he : v ⬝ᵥ (Z.c + ∑ i, β i • Z.G i) - d = v ⬝ᵥ Z.c - d + ∑ i, β i * v ⬝ᵥ Z.G i := by
    rw [dotProduct_add, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
    ring
  rw [he]
  simp only [Zonotope.halfspaceRange]
  constructor <;> linarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

/-- `1/y` of a point of an interval that excludes `0` lies in `[1/hi, 1/lo]`. -/
theorem aux_hpMap_inv {lo hi y : ℝ} (h : 0 < lo ∨ hi < 0) (h1 : lo ≤ y) (h2 : y ≤ hi) :
    hi⁻¹ ≤ y⁻¹ ∧ y⁻¹ ≤ lo⁻¹ := by -- --- PROOF ---
  rcases h with h | h
  · exact ⟨inv_anti₀ (lt_of_lt_of_le h h1) h2, inv_anti₀ h h1⟩
  · have hy : y < 0 := lt_of_le_of_lt h2 h
    have hl : lo < 0 := lt_of_le_of_lt h1 hy
    exact ⟨(inv_le_inv_of_neg h hy).mpr h2, (inv_le_inv_of_neg hy hl).mpr h1⟩

/-- `1/y²` of a point of an interval that excludes `0` lies in `[1/max, 1/min]` of the squared
ends, CORA's `1/Lambda_int^2`. -/
theorem aux_hpMap_sq {lo hi y : ℝ} (h : 0 < lo ∨ hi < 0) (h1 : lo ≤ y) (h2 : y ≤ hi) :
    1 / max (lo ^ 2) (hi ^ 2) ≤ 1 / y ^ 2 ∧
      1 / y ^ 2 ≤ 1 / min (lo ^ 2) (hi ^ 2) := by -- --- PROOF ---
  have hb : min (lo ^ 2) (hi ^ 2) ≤ y ^ 2 ∧ y ^ 2 ≤ max (lo ^ 2) (hi ^ 2) ∧
      0 < min (lo ^ 2) (hi ^ 2) := by
    rcases h with h | h
    · refine ⟨(min_le_left _ _).trans (by nlinarith), (by nlinarith : y ^ 2 ≤ hi ^ 2).trans
        (le_max_right _ _), lt_min (pow_pos h 2) (pow_pos (lt_of_lt_of_le h (h1.trans h2)) 2)⟩
    · refine ⟨(min_le_right _ _).trans (by nlinarith), (by nlinarith : y ^ 2 ≤ lo ^ 2).trans
        (le_max_left _ _), lt_min (by nlinarith) (by nlinarith)⟩
  obtain ⟨hlo, hhi, hpos⟩ := hb
  exact ⟨one_div_le_one_div_of_le (lt_of_lt_of_le hpos hlo) hhi,
    one_div_le_one_div_of_le hpos hlo⟩

/-- A point of `[lo, hi]` is `(lo + hi)/2 + κ(hi − lo)/2` for some `|κ| ≤ 1`. -/
theorem aux_hpMap_factor {lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) :
    ∃ κ : ℝ, |κ| ≤ 1 ∧ y = (lo + hi) / 2 + κ * ((hi - lo) / 2) := by -- --- PROOF ---
  rcases eq_or_lt_of_le (h1.trans h2) with heq | hlt
  · exact ⟨0, by norm_num, by rw [← heq] at h2 ⊢; linarith⟩
  · refine ⟨(y - (lo + hi) / 2) / ((hi - lo) / 2), abs_le.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ (by linarith)]; linarith
    · rw [div_le_iff₀ (by linarith)]; linarith
    · field_simp; ring

/-- `s I` for `s ∈ [a, b]` lies in CORA's interval matrix `[a, b] I`. -/
theorem aux_hpMap_smul_one_mem {a b s : ℝ} (hs : a ≤ s ∧ s ≤ b) :
    s • (1 : Mat ℝ n n) ∈ (⟨Matrix.of fun j k =>
      Interval.mulLo ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) a b,
      Matrix.of fun j k => Interval.mulHi ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) a b⟩ :
        Interval (Mat ℝ n n)).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  have h := Interval.mul_between_corners (le_refl ((1 : Mat ℝ n n) j k))
    (le_refl ((1 : Mat ℝ n n) j k)) hs.1 hs.2
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_comm s]
  exact h

/-- `s v ∈ [a, b] Z` for `s ∈ [a, b]` and `v ∈ Z`. -/
theorem aux_hpMap_smul_mem_mtimes {a b s : ℝ} (hs : a ≤ s ∧ s ≤ b) {Z : Zonotope (Vec ℝ n)}
    {v : Vec ℝ n} (hv : v ∈ Z.construct) :
    s • v ∈ (Zonotope.mtimesIntervalMat ⟨Matrix.of fun j k =>
      Interval.mulLo ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) a b,
      Matrix.of fun j k => Interval.mulHi ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) a b⟩
        Z).construct := by
  have h := Zonotope.mtimesIntervalMat_outer _ Z
    (Set.mem_biUnion (aux_hpMap_smul_one_mem hs) (Set.mem_image_of_mem _ hv))
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h
  exact h

/-- Girard's reduction keeps the centre. -/
theorem aux_hpMap_reduceGirard_c (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    (Z.reduceGirard o).c = Z.c := by
  unfold Zonotope.reduceGirard
  split_ifs
  · rfl
  · rfl

/-- `Ax + b` of a point of `Z` is in `AZ ⊕ b`. -/
theorem aux_hpMap_flow_mem (A : Mat ℝ n n) (b : Vec ℝ n) {Z : Zonotope (Vec ℝ n)}
    {x : Vec ℝ n} (hx : x ∈ Z.construct) :
    A *ᵥ x + b ∈ ((Zonotope.mtimes A Z).plus (Zonotope.ofPoint b)).construct := by
  rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
  exact Set.add_mem_add ⟨x, hx, rfl⟩ (Zonotope.mem_ofPoint b)

/-- `res1`: the hitting point `y_h(x₀)` of a point of `R₀`. -/
theorem aux_hpMap_res1 (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (R₀ R0red : Zonotope (Vec ℝ n))
    (hcen : R0red.c = R₀.c) (hsub : ∀ x ∈ R₀.construct, x ∈ R0red.construct) {x₀ : Vec ℝ n}
    (hx₀ : x₀ ∈ R₀.construct) :
    -- the lets of `Location.guardIntersectHyperplaneMap` that `res1` reads
    let Υ : Vec ℝ n := nv ᵥ* A
    let flowRed := (Zonotope.mtimes A R0red).plus (Zonotope.ofPoint b)
    let Λint := flowRed.halfspaceRange nv 0
    let dint := R0red.halfspaceRange nv d
    let τlo := Interval.mulLo (-dint.2) (-dint.1) Λint.2⁻¹ Λint.1⁻¹
    let τhi := Interval.mulHi (-dint.2) (-dint.1) Λint.2⁻¹ Λint.1⁻¹
    let ψc : Vec ℝ n := -nv - ((τlo + τhi) / 2) • Υ
    let ψg : Vec ℝ n := -(((τhi - τlo) / 2) • Υ)
    let φlo := 1 / max (Λint.1 ^ 2) (Λint.2 ^ 2)
    let φhi := 1 / min (Λint.1 ^ 2) (Λint.2 ^ 2)
    let Q := GuardMap.hitHessianMatZono A b nv d R0red ψc ψg
    let Rquad := Zonotope.quadMapMatZono (fun i => (Q i).c)
      (fun (j : Fin (1 + R0red.h + R0red.h)) i => (Q i).G j) R0red.recentre
    (0 < Λint.1 ∨ Λint.2 < 0) →
    GuardMap.hitPoint A b nv d x₀ ∈ (((Zonotope.ofPoint (GuardMap.hitPoint A b nv d R0red.c)).plus
      (Zonotope.mtimes (GuardMap.hitJacobian A b nv d R0red.c) R₀.recentre)).plus
      (Zonotope.mtimesIntervalMat ⟨Matrix.of fun j k =>
          Interval.mulLo ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) (φlo / 2) (φhi / 2),
        Matrix.of fun j k =>
          Interval.mulHi ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) (φlo / 2) (φhi / 2)⟩
        Rquad)).construct := by -- --- PROOF ---
  intro Υ flowRed Λint dint τlo τhi ψc ψg φlo φhi Q Rquad hΛ
  set ξ := R0red.c with hξdef
  have hξ : ξ ∈ R0red.construct := Zonotope.centre_mem_construct R0red
  have hx₀' : x₀ ∈ R0red.construct := hsub x₀ hx₀
  -- `Λ` on the reduced set, within `Λ_int`, so nonzero, and `1/Λ²` within `[φ̲, φ̄]`
  have hΛr : ∀ x ∈ R0red.construct,
      Λint.1 ≤ nv ⬝ᵥ (A *ᵥ x + b) ∧ nv ⬝ᵥ (A *ᵥ x + b) ≤ Λint.2 := fun x hx => by
    have h := aux_hpMap_range (v := nv) (d := 0) (aux_hpMap_flow_mem A b hx)
    rw [sub_zero] at h
    exact h
  have hΛne : ∀ x ∈ R0red.construct, nv ⬝ᵥ (A *ᵥ x + b) ≠ 0 := fun x hx => by
    obtain ⟨h1, h2⟩ := hΛr x hx
    rcases hΛ with h | h
    · exact (lt_of_lt_of_le h h1).ne'
    · exact (lt_of_le_of_lt h2 h).ne
  have hφ : ∀ x ∈ R0red.construct, φlo ≤ 1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ∧
      1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ≤ φhi := fun x hx =>
    aux_hpMap_sq hΛ (hΛr x hx).1 (hΛr x hx).2
  -- the exact expansion around `ξ`
  set ν : Vec ℝ n := x₀ - ξ with hν
  have hx₀ν : ξ + ν = x₀ := by rw [hν]; abel
  have hexp := GuardMap.hitPoint_add_eq A b nv d ξ ν (hΛne ξ hξ) (by rw [hx₀ν]; exact hΛne x₀ hx₀')
  rw [hx₀ν] at hexp
  have hφm := GuardMap.hitFactor_mem_Icc A b nv (Zonotope.convex_construct R0red) hΛne hφ hξ hx₀'
  -- `Θ(ξ)/Λ(ξ) = ψ_c + κψ_g`: `τ(ξ) = (d − nᵀξ)/Λ(ξ)` lies in `[τ̲, τ̄]`
  have hnum : -dint.2 ≤ d - nv ⬝ᵥ ξ ∧ d - nv ⬝ᵥ ξ ≤ -dint.1 := by
    have h := aux_hpMap_range (v := nv) (d := d) hξ
    constructor <;> linarith [h.1, h.2]
  have hinv := aux_hpMap_inv hΛ (hΛr ξ hξ).1 (hΛr ξ hξ).2
  have hτ := Interval.mul_between_corners hnum.1 hnum.2 hinv.1 hinv.2
  obtain ⟨κ, hκ, hκeq⟩ := aux_hpMap_factor hτ.1 hτ.2
  have hψ : (nv ⬝ᵥ (A *ᵥ ξ + b))⁻¹ • (-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A))
      = ψc + κ • ψg := by
    have hne := hΛne ξ hξ
    funext i
    simp only [ψc, ψg, Υ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    have e : (nv ⬝ᵥ (A *ᵥ ξ + b))⁻¹ * (-((nv ⬝ᵥ (A *ᵥ ξ + b)) * nv i)
        - (d - nv ⬝ᵥ ξ) * (nv ᵥ* A) i)
        = -nv i - ((d - nv ⬝ᵥ ξ) * (nv ⬝ᵥ (A *ᵥ ξ + b))⁻¹) * (nv ᵥ* A) i := by
      field_simp
    rw [e, hκeq]
    ring
  -- `Q⁽ⁱ⁾(ξ)` is the matrix zonotopes' point at the factors `(κ, 0, 0)` of `ξ`
  have hξeq : R0red.c + ∑ j, (0 : Fin R0red.h → ℝ) j • R0red.G j = ξ := by simp [hξdef]
  set fac : Fin (1 + R0red.h + R0red.h) → ℝ :=
    Fin.append (Fin.append ![κ] (0 : Fin R0red.h → ℝ)) fun α => κ * (0 : Fin R0red.h → ℝ) α
    with hfac
  have hQ : ∀ i, GuardMap.hitHessianNum A b nv d ξ i = (Q i).c + ∑ j, fac j • (Q i).G j :=
    fun i => by
      have h := GuardMap.hitHessianNum_eq_hitHessianMatZono A b nv d R0red ψc ψg i 0 κ
        (by rw [hξeq]; exact hψ)
      rw [hξeq] at h
      exact h
  -- the factors are in `[-1, 1]`, and `ν ∈ R0red ⊖ ξ`: `q ∈ R_quad` by [1, Thm. 1]
  have hfac1 : ∀ j, |fac j| ≤ 1 := fun j => by
    refine Fin.addCases (fun j => ?_) (fun α => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun α => ?_) j
      · rw [hfac, Fin.append_left, Fin.append_left, Fin.fin_one_eq_zero j]; simpa using hκ
      · rw [hfac, Fin.append_left, Fin.append_right]; simp
    · rw [hfac, Fin.append_right]; simp
  have hνmem : ν ∈ R0red.recentre.construct := Zonotope.sub_centre_mem_recentre hx₀'
  have hqmem : (fun i => ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν)) ∈ Rquad.construct :=
    Zonotope.quadMapMatZono_outer _ _ _ ⟨ν, hνmem, fac, hfac1, fun i => by
      dsimp only
      rw [hQ i]⟩
  -- assemble `k + Lν + ½φq`
  rw [hexp, ← Zonotope.plus_exact, ← Zonotope.plus_exact]
  refine Set.add_mem_add (Set.add_mem_add (Zonotope.mem_ofPoint _) ?_) ?_
  · rw [← Zonotope.mtimes_exact]
    refine ⟨ν, ?_, rfl⟩
    have h := Zonotope.sub_centre_mem_recentre hx₀
    rwa [← hcen] at h
  · rw [smul_smul]
    refine aux_hpMap_smul_mem_mtimes ⟨?_, ?_⟩ hqmem
    · linarith [hφm.1]
    · linarith [hφm.2]

/-- `res2`: `(−nᵀe₁/Λ(x₀))(Ax₀ + b) + e₂` for `x₀ ∈ R₀`, `e₁, e₂ ∈ E`. -/
theorem aux_hpMap_res2 (A : Mat ℝ n n) (b nv : Vec ℝ n) (R₀ E : Zonotope (Vec ℝ n))
    {x₀ e₁ e₂ : Vec ℝ n} (hx₀ : x₀ ∈ R₀.construct) (he₁ : e₁ ∈ E.construct)
    (he₂ : e₂ ∈ E.construct) :
    let flowSet := (Zonotope.mtimes A R₀).plus (Zonotope.ofPoint b)
    let numInt := E.halfspaceRange (-nv) 0
    let denInt := flowSet.halfspaceRange nv 0
    let Ilo := Interval.mulLo numInt.1 numInt.2 denInt.2⁻¹ denInt.1⁻¹
    let Ihi := Interval.mulHi numInt.1 numInt.2 denInt.2⁻¹ denInt.1⁻¹
    (0 < denInt.1 ∨ denInt.2 < 0) →
    (-(nv ⬝ᵥ e₁) / (nv ⬝ᵥ (A *ᵥ x₀ + b))) • (A *ᵥ x₀ + b) + e₂
      ∈ ((Zonotope.mtimesIntervalMat ⟨Matrix.of fun j k =>
          Interval.mulLo ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) Ilo Ihi,
        Matrix.of fun j k =>
          Interval.mulHi ((1 : Mat ℝ n n) j k) ((1 : Mat ℝ n n) j k) Ilo Ihi⟩ flowSet).plus
        E).construct := by -- --- PROOF ---
  intro flowSet numInt denInt Ilo Ihi hden
  have hf := aux_hpMap_flow_mem A b hx₀
  have hnum := aux_hpMap_range (v := -nv) (d := 0) he₁
  have hd := aux_hpMap_range (v := nv) (d := 0) hf
  simp only [sub_zero, neg_dotProduct] at hnum hd
  have hinv := aux_hpMap_inv hden hd.1 hd.2
  have hI := Interval.mul_between_corners hnum.1 hnum.2 hinv.1 hinv.2
  rw [← Zonotope.plus_exact]
  refine Set.add_mem_add ?_ he₂
  rw [div_eq_mul_inv]
  exact aux_hpMap_smul_mem_mtimes hI hf


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run from `R₀` on the hyperplane at `t ≤ tmax` is in the mapped set, `η ≥ 1`. -/
theorem Location.guardIntersectHyperplaneMap_outer (ℓ : Location 𝒵 G L ℝ n) (nv : Vec ℝ n)
    (d : ℝ) (R₀ : Zonotope (Vec ℝ n)) (tmax : ℝ) {η : ℕ} (guardOrder zonotopeOrder : ℕ)
    (hη : 1 ≤ η) {τ : ℝ} {x u : ℝ → Vec ℝ n} (traj : ℓ.Trajectory τ x u)
    (h₀ : x 0 ∈ R₀.construct) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) (htmax : t ≤ tmax)
    (hhit : nv ⬝ᵥ x t = d) {Z : Zonotope (Vec ℝ n)}
    (hZ : ℓ.guardIntersectHyperplaneMap nv d R₀ tmax η guardOrder zonotopeOrder = some Z) :
    x t ∈ Z.construct := by -- --- PROOF ---
  set A : Mat ℝ n n := ℓ.dynamics.A with hA
  set U : Zonotope (Vec ℝ n) := ℓ.U with hU
  set x₀ := x 0 with hx₀def
  set b : Vec ℝ n := GuardMap.sdcInput A U.c (tmax / 2) η R₀.c with hb
  set R0red := R₀.reduceGirard guardOrder with hR0red
  have hcen : R0red.c = R₀.c := aux_hpMap_reduceGirard_c R₀ guardOrder
  have hsub : ∀ x ∈ R₀.construct, x ∈ R0red.construct :=
    fun x hx => Zonotope.reduceGirard_outer R₀ guardOrder hx
  set err := GuardMap.abstractionError A U R0red (tmax / 2) tmax η with herr
  -- the run, in closed form, and its error to the constant flow
  have tr := (traj.linearSys (R₀ := R₀) h₀).trajectory (convex_Icc 0 τ) ⟨le_rfl, traj.nonneg⟩
    (Zonotope.isBounded_construct U)
  have hvoc := tr.variation_of_constants (a := 0) (b := t) (Set.Icc_subset_Icc_right ht.2)
    le_rfl ht.1 (Zonotope.isBounded_construct U)
  simp only [sub_zero, Scalar.toRealMat_real] at hvoc
  have hmeas := tr.aestronglyMeasurable_input_reflected (c := t) (r := t)
    (by rw [sub_self]; exact Set.Icc_subset_Icc_right ht.2)
  have hu : ∀ s ∈ Set.Ioc (0:ℝ) t, u (t - s) ∈ U.construct := fun s hs =>
    traj.input (t - s) ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
  have he := GuardMap.abstractionError_outer A U R0red (tmax / 2) hη ⟨ht.1, htmax⟩
    (hsub x₀ h₀) hu hmeas
  rw [hcen, ← hvoc] at he
  set e := x t - GuardMap.sdcFlow A b x₀ t with he_def
  have hxt : x t = x₀ + t • (A *ᵥ x₀ + b) + e := by
    rw [he_def, GuardMap.sdcFlow]; abel
  -- the returned set
  simp only [Location.guardIntersectHyperplaneMap] at hZ
  split_ifs at hZ with hc
  obtain rfl := Option.some.inj hZ
  have hΛ0 : nv ⬝ᵥ (A *ᵥ x₀ + b) ≠ 0 := by
    have h := aux_hpMap_range (v := nv) (d := 0) (aux_hpMap_flow_mem A b h₀)
    rw [sub_zero] at h
    rcases hc.2 with hc2 | hc2
    · exact (lt_of_lt_of_le hc2 h.1).ne'
    · exact (lt_of_le_of_lt h.2 hc2).ne
  -- the hit, as `y_h(x₀) + (−nᵀe/Λ(x₀))(Ax₀ + b) + e`
  have hsplit : x t = GuardMap.hitPoint A b nv d x₀
      + ((-(nv ⬝ᵥ e) / (nv ⬝ᵥ (A *ᵥ x₀ + b))) • (A *ᵥ x₀ + b) + e) := by
    have hhit' : nv ⬝ᵥ (x₀ + t • (A *ᵥ x₀ + b) + e) = d := by rw [← hxt]; exact hhit
    have htime : t = (d - nv ⬝ᵥ x₀ - nv ⬝ᵥ e) / (nv ⬝ᵥ (A *ᵥ x₀ + b)) := by
      rw [eq_div_iff hΛ0, ← hhit']
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    rw [hxt, GuardMap.hitPoint]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [htime]
    field_simp
    ring
  -- a point of the hyperplane is its own projection
  have hproj : x t = x t - (((Real.sqrt (nv ⬝ᵥ nv))⁻¹ • nv) ⬝ᵥ x t
      - d / Real.sqrt (nv ⬝ᵥ nv)) • ((Real.sqrt (nv ⬝ᵥ nv))⁻¹ • nv) := by
    rw [smul_dotProduct, hhit, smul_eq_mul, div_eq_inv_mul, sub_self, zero_smul, sub_zero]
  refine ContSet.projectOnHyperplane_outer (S := 𝒵) _ _ _ ⟨x t, ?_, hproj.symm⟩
  refine Zonotope.reduceGirard_outer _ _ ?_
  rw [← Zonotope.plus_exact, hsplit]
  refine Set.add_mem_add (aux_hpMap_res1 A b nv d R₀ R0red hcen hsub h₀ hc.1) ?_
  exact aux_hpMap_res2 A b nv R₀ err h₀ he he hc.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
