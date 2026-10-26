module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrSolInf
public import CORALean.ContSet.Zonotope.Real.Theorems.SupportBoundAttained
public import CORALean.Global.BoxDiameter
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The diameter of the set of abstraction errors

`[1, Prop. 1]`: with `Ψ(h)` the zonotope `⟨c(h), G(h)⟩_Z`, the `i`-th side of the box over
`R^∞_abs(h)` is `2 Σₚ h^{p+1}/(p+1)! ‖Aᵖ(h)G(h)‖₁,ᵢ`, the 1-norm of the `i`-th *row*; the factor
`2` is the set being symmetric about its center. An `=` and not a `⊆`: each summand's maximum is
attained at the sign pattern of its own row, and the choices are independent
(`Zonotope.supportBound_attained`). Generators are a family, so the norm is `Σⱼ |(Aᵖ(h) gʲ)ᵢ|`.
`0 ≤ h` is the paper's implicit reading of a time span; nothing else is asked.

## Inputs
* `A` – matrix as a function of the step
* `Ψ` – error set as a function of the step
* `h` – step size
* `Z` – error zonotope at the step
* `i` – dimension

## Hypotheses
* `hh` – step size nonnegative
* `hΨ` – error set is the zonotope

## Conclusion
* the box side equals twice the series of row norms

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

-- `[1, (32)]` iterates a matrix, so this file picks the norm that bounds it
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The operator-norm bound iterated: `Mᵖ` moves a vector no further than
`‖M‖ᵖ` does. -/
private theorem aux_norm_pow_mulVec_le (M : Mat ℝ n n) (p : ℕ) (v : Vec ℝ n) : -- --- CONCL ---
    ‖M ^ p *ᵥ v‖ ≤ ‖M‖ ^ p * ‖v‖ := by -- --- PROOF ---
  induction p with
  | zero => simp
  | succ p ih =>
    -- peel one factor off the front, so that `mulVec` sees `M` alone
    have hrw : M ^ (p + 1) *ᵥ v = M *ᵥ (M ^ p *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hrw, pow_succ']
    calc ‖M *ᵥ (M ^ p *ᵥ v)‖ ≤ ‖M‖ * ‖M ^ p *ᵥ v‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ ‖M‖ * (‖M‖ ^ p * ‖v‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖M‖ * ‖M‖ ^ p * ‖v‖ := by ring

/-- `[1, (32)]`'s terms are dominated by the exponential series: `hᵖ⁺¹/(p+1)!
aᵖR` sits under `hR·(ha)ᵖ/p!`. -/
private theorem aux_summable_majorant {h a R : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hR : 0 ≤ R) : -- --- CONCL ---
    Summable (fun p : ℕ =>
      h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * (a ^ p * R)) := by -- --- PROOF ---
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    ((Real.summable_pow_div_factorial (h * a)).mul_left (h * R))
  · -- every term is non-negative, `h` and `a` being
    have hc : (0:ℝ) ≤ h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) :=
      div_nonneg (pow_nonneg hh _) (Nat.cast_nonneg _)
    exact mul_nonneg hc (mul_nonneg (pow_nonneg ha _) hR)
  · -- the two sides share a numerator and differ only in `p!` against `(p+1)!`
    have hnum : (0:ℝ) ≤ h * (h * a) ^ p * R := by positivity
    have hp : (0:ℝ) < (Nat.factorial p : ℝ) := by exact_mod_cast p.factorial_pos
    have hle : (Nat.factorial p : ℝ) ≤ (Nat.factorial (p + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ p)
    have hlhs : h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * (a ^ p * R)
        = (h * (h * a) ^ p * R) / (Nat.factorial (p + 1) : ℝ) := by
      rw [mul_pow]; ring
    have hrhs : h * R * ((h * a) ^ p / (Nat.factorial p : ℝ))
        = (h * (h * a) ^ p * R) / (Nat.factorial p : ℝ) := by ring
    rw [hlhs, hrhs]
    exact div_le_div_of_nonneg_left hnum hp hle

/-- A zonotope reaches no further than its center plus all of its generators. -/
private theorem aux_norm_le_of_mem_construct {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ Z.construct) : -- --- CONCL ---
    ‖x‖ ≤ ‖Z.c‖ + ∑ j, ‖Z.G j‖ := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  -- each coefficient is at most one, so each generator contributes at most its norm
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hβ j)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, (35)]`: a side of the box over `R^∞_abs(h)` is twice the series of the
row norms of `Aᵖ(h)G(h)`. -/
theorem boxDiameter_abstrSolInf (A : ℝ → Mat ℝ n n) (Ψ : ℝ → Set (Vec ℝ n)) {h : ℝ}
    (hh : 0 ≤ h) {Z : Zonotope (Vec ℝ n)} (hΨ : Ψ h = Z.construct) (i : Fin n) : -- --- CONCL ---
    boxDiameter (abstrSolInf A Ψ h) i =
      2 * ∑' p : ℕ, h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ)
        * ∑ j, |(A h ^ p *ᵥ Z.G j) i| := by -- --- PROOF ---
  classical
  -- the three pieces of `[1, (35)]`: the coefficient, the center's share, the row norm
  set coef : ℕ → ℝ := fun p => h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) with hcoefd
  set ctr : ℕ → ℝ := fun p => (A h ^ p *ᵥ Z.c) i with hctrd
  set row : ℕ → ℝ := fun p => ∑ j, |(A h ^ p *ᵥ Z.G j) i| with hrowd
  show boxDiameter (abstrSolInf A Ψ h) i = 2 * ∑' p, coef p * row p
  -- the direction `dᵢ` reads the `p`-th summand in: one row of `Aᵖ(h)`
  set L : ℕ → (Vec ℝ n →ₗ[ℝ] ℝ) :=
    fun p => (LinearMap.proj i).comp (Matrix.mulVecLin (A h ^ p)) with hLd
  have hcoefnn : ∀ p, 0 ≤ coef p := fun p =>
    div_nonneg (pow_nonneg hh _) (Nat.cast_nonneg _)
  -- the support value of `Ψ(h)` in direction `±L p` is the center's share ± the row norm
  have hsupp : ∀ p, (Z.supportBound (L p)).val = ctr p + row p := fun p => rfl
  have hsuppneg : ∀ p, (Z.supportBound (-(L p))).val = -ctr p + row p := by
    intro p
    show -(L p Z.c) + ∑ j, |(-(L p)) (Z.G j)| = -ctr p + row p
    simp only [LinearMap.neg_apply, abs_neg]
    rfl
  have hub : ∀ p, ∀ x ∈ Z.construct, (A h ^ p *ᵥ x) i ≤ ctr p + row p := by
    intro p x hx
    have hle := (Z.supportBound (L p)).le x hx
    rw [hsupp p] at hle
    exact hle
  have hlb : ∀ p, ∀ x ∈ Z.construct, ctr p - row p ≤ (A h ^ p *ᵥ x) i := by
    intro p x hx
    have hle := (Z.supportBound (-(L p))).le x hx
    rw [hsuppneg p] at hle
    -- the same bound read on `-L p`, which is the lower one on `L p`
    have hle' : -((A h ^ p *ᵥ x) i) ≤ -ctr p + row p := hle
    linarith
  -- a coordinate is under the vector's norm, and `Aᵖ(h)` grows a norm by at most `‖A h‖ᵖ`
  have habs : ∀ (p : ℕ) (x : Vec ℝ n), |(A h ^ p *ᵥ x) i| ≤ ‖A h‖ ^ p * ‖x‖ := by
    intro p x
    calc |(A h ^ p *ᵥ x) i| = ‖(A h ^ p *ᵥ x) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖A h ^ p *ᵥ x‖ := norm_le_pi_norm _ i
      _ ≤ ‖A h‖ ^ p * ‖x‖ := aux_norm_pow_mulVec_le _ _ _
  have hRnn : (0:ℝ) ≤ ‖Z.c‖ + ∑ j, ‖Z.G j‖ := by positivity
  have hmaj := aux_summable_majorant hh (norm_nonneg (A h)) hRnn
  -- center and generators alike sit under the one majorant, so all three series converge
  have hctrb : ∀ p, |ctr p| ≤ ‖A h‖ ^ p * (‖Z.c‖ + ∑ j, ‖Z.G j‖) := by
    intro p
    refine (habs p Z.c).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hg : (0:ℝ) ≤ ∑ j, ‖Z.G j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    linarith
  have hrownn : ∀ p, 0 ≤ row p := fun p => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hrowb : ∀ p, row p ≤ ‖A h‖ ^ p * (‖Z.c‖ + ∑ j, ‖Z.G j‖) := by
    intro p
    calc row p ≤ ∑ j, ‖A h‖ ^ p * ‖Z.G j‖ := Finset.sum_le_sum fun j _ => habs p (Z.G j)
      _ = ‖A h‖ ^ p * ∑ j, ‖Z.G j‖ := by rw [Finset.mul_sum]
      _ ≤ ‖A h‖ ^ p * (‖Z.c‖ + ∑ j, ‖Z.G j‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [norm_nonneg Z.c]
  -- comparison against that majorant, in absolute value for the center's series
  have hsc : Summable (fun p => coef p * ctr p) := by
    refine Summable.of_norm_bounded hmaj (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hcoefnn p)]
    exact mul_le_mul_of_nonneg_left (hctrb p) (hcoefnn p)
  have hsr : Summable (fun p => coef p * row p) := by
    refine Summable.of_norm_bounded hmaj (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hcoefnn p), abs_of_nonneg (hrownn p)]
    exact mul_le_mul_of_nonneg_left (hrowb p) (hcoefnn p)
  -- so the two extreme series split into the center's and the generators' halves
  have hadd : ∑' p, coef p * (ctr p + row p)
      = (∑' p, coef p * ctr p) + ∑' p, coef p * row p := by
    simp only [mul_add]
    exact hsc.tsum_add hsr
  have hsub : ∑' p, coef p * (ctr p - row p)
      = (∑' p, coef p * ctr p) - ∑' p, coef p * row p := by
    simp only [mul_sub]
    exact hsc.tsum_sub hsr
  have hsaddS : Summable (fun p => coef p * (ctr p + row p)) := by
    simpa [mul_add] using hsc.add hsr
  have hssubS : Summable (fun p => coef p * (ctr p - row p)) := by
    simpa [mul_sub] using hsc.sub hsr
  -- a point of `R^∞_abs(h)` is a sum of choices, each under its own summand's bound
  have hmemle : ∀ x ∈ abstrSolInf A Ψ h,
      x i ≤ (∑' p, coef p * ctr p) + ∑' p, coef p * row p := by
    rintro x ⟨ψ, hψ, hs⟩
    have hsi : HasSum (fun p => coef p * (A h ^ p *ᵥ ψ p) i) (x i) := Pi.hasSum.mp hs i
    calc x i = ∑' p, coef p * (A h ^ p *ᵥ ψ p) i := hsi.tsum_eq.symm
      _ ≤ ∑' p, coef p * (ctr p + row p) :=
          Summable.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_left
            (hub p (ψ p) (hΨ ▸ hψ p)) (hcoefnn p)) hsi.summable hsaddS
      _ = _ := hadd
  have hmemge : ∀ x ∈ abstrSolInf A Ψ h,
      (∑' p, coef p * ctr p) - ∑' p, coef p * row p ≤ x i := by
    rintro x ⟨ψ, hψ, hs⟩
    have hsi : HasSum (fun p => coef p * (A h ^ p *ᵥ ψ p) i) (x i) := Pi.hasSum.mp hs i
    calc (∑' p, coef p * ctr p) - ∑' p, coef p * row p
        = ∑' p, coef p * (ctr p - row p) := hsub.symm
      _ ≤ ∑' p, coef p * (A h ^ p *ᵥ ψ p) i :=
          Summable.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_left
            (hlb p (ψ p) (hΨ ▸ hψ p)) (hcoefnn p)) hssubS hsi.summable
      _ = x i := hsi.tsum_eq
  -- and one summand at a time the bound is met, so the whole series is met too
  have hwit : ∀ (s : ℕ → ℝ), (∀ p, ∃ y ∈ Z.construct, (A h ^ p *ᵥ y) i = s p) →
      ∃ x ∈ abstrSolInf A Ψ h, x i = ∑' p, coef p * s p := by
    intro s hs
    choose y hy hyv using hs
    have hsumvec : Summable (fun p => coef p • (A h ^ p *ᵥ y p)) := by
      refine Summable.of_norm_bounded hmaj (fun p => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hcoefnn p)]
      refine mul_le_mul_of_nonneg_left ?_ (hcoefnn p)
      exact (aux_norm_pow_mulVec_le _ _ _).trans
        (mul_le_mul_of_nonneg_left (aux_norm_le_of_mem_construct (hy p)) (by positivity))
    refine ⟨∑' p, coef p • (A h ^ p *ᵥ y p), ⟨y, fun p => hΨ ▸ hy p, hsumvec.hasSum⟩, ?_⟩
    have hco : HasSum (fun p => coef p * (A h ^ p *ᵥ y p) i)
        ((∑' p, coef p • (A h ^ p *ᵥ y p)) i) := Pi.hasSum.mp hsumvec.hasSum i
    rw [← hco.tsum_eq]
    exact tsum_congr fun p => by rw [hyv p]
  -- the sign pattern of the `p`-th row is the choice that attains it
  obtain ⟨xmax, hxmaxmem, hxmaxval⟩ := hwit (fun p => ctr p + row p)
    (fun p => by
      obtain ⟨y, hy, hyv⟩ := Z.supportBound_attained (L p)
      exact ⟨y, hy, by rw [← hsupp p]; exact hyv⟩)
  obtain ⟨xmin, hxminmem, hxminval⟩ := hwit (fun p => ctr p - row p)
    (fun p => by
      obtain ⟨y, hy, hyv⟩ := Z.supportBound_attained (-(L p))
      refine ⟨y, hy, ?_⟩
      rw [hsuppneg p] at hyv
      have hyv' : -((A h ^ p *ᵥ y) i) = -ctr p + row p := hyv
      linarith)
  -- attained above and below, so both are the supremum and the infimum rather than bounds
  have hgreat : IsGreatest ((fun x : Vec ℝ n => x i) '' abstrSolInf A Ψ h)
      ((∑' p, coef p * ctr p) + ∑' p, coef p * row p) := by
    refine ⟨⟨xmax, hxmaxmem, show xmax i = _ by rw [hxmaxval, hadd]⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hmemle x hx
  have hleast : IsLeast ((fun x : Vec ℝ n => x i) '' abstrSolInf A Ψ h)
      ((∑' p, coef p * ctr p) - ∑' p, coef p * row p) := by
    refine ⟨⟨xmin, hxminmem, show xmin i = _ by rw [hxminval, hsub]⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hmemge x hx
  -- the center's share cancels in the difference, leaving twice the row-norm series
  rw [boxDiameter, hgreat.csSup_eq, hleast.csInf_eq]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
