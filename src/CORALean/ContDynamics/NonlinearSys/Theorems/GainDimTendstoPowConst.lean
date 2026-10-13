import CORALean.ContDynamics.NonlinearSys.Theorems.BoxDiameterAbstrSolInf
import CORALean.ContDynamics.NonlinearSys.Theorems.GainDimTendstoPow
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The limit gain at a fixed linearization

`[2, Prop. 1]`: at a *constant* `A` and `Ψ`, the gain of dimension `i` tends to `ζ_δ^{λᵢ}`
as `Δt → 0`, with `λᵢ = j+1` for the first `j` such that `(Aʲ Ψ)ᵢ ≠ {0}` — read off the
generator row, as `[1, Def. 6]`/`gainOrderDim` already does, since a centre shifts a box
without widening it. `R_abs` is `abstrSolInf` at that fixed `A` and `Ψ`, matching `[1]`'s
own convention of the un-truncated `[1, (8)]` rather than `[2]`'s own truncated `(6)`; see
the paper page's finding.

This is `gainDim_tendsto_pow` — `[1, Thm. 2]` — at `A t = A` and `Ψ t = Ψ` for every `t`,
proved rather than restated: `[1, Thm. 2]`'s `hexp` is a hypothesis there because passing a
limit inside an infinite series needs uniform control over the index that a moving `A(h)`,
`Ψ(h)` does not give. Here every summand is already independent of `t`, so the same
expansion is elementary, and is proved below by peeling the vanishing leading terms off the
series `boxDiameter_abstrSolInf` supplies and showing what is left is continuous into `0`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
* [2] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology Matrix CORALean.Real

-- read at the l-infinity operator norm, as `BoxDiameterAbstrSolInf` already does
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[2, Prop. 1]`: at a fixed `A` and zonotope `Ψ`, the gain of dimension `i` tends to
`δ^{j+1}`, `j` being the first order at which `Aʲ`'s `i`-th row of `Ψ`'s generators survives. -/
theorem gainDim_tendsto_pow_const (A : Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) (i : Fin n)
    {j : ℕ} (hj : ∑ l, |(A ^ j *ᵥ Z.G l) i| ≠ 0)
    (hjmin : ∀ p < j, ∑ l, |(A ^ p *ᵥ Z.G l) i| = 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto (fun h => gainDim (fun _ => A) (fun _ => Z.construct) h δ i) (𝓝[>] (0:ℝ))
      (𝓝 (δ ^ (j + 1))) := by -- --- PROOF ---
  classical
  -- the `i`-th row of `Aᵖ`'s generators, and the constant that bounds its norm
  set row : ℕ → ℝ := fun p => ∑ l, |(A ^ p *ᵥ Z.G l) i| with hrowd
  set R : ℝ := ∑ l, ‖Z.G l‖ with hRd
  have hRnn : (0:ℝ) ≤ R := Finset.sum_nonneg fun l _ => norm_nonneg _
  have hrownn : ∀ p, 0 ≤ row p := fun p => Finset.sum_nonneg fun l _ => abs_nonneg _
  -- the operator-norm bound iterated, as `BoxDiameterAbstrSolInf` proves it once for `abstrSolInf`
  have hpowmulvec : ∀ (p : ℕ) (v : Vec ℝ n), ‖A ^ p *ᵥ v‖ ≤ ‖A‖ ^ p * ‖v‖ := by
    intro p
    induction p with
    | zero => intro v; simp
    | succ p ih =>
      intro v
      have hrw : A ^ (p + 1) *ᵥ v = A *ᵥ (A ^ p *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, ← pow_succ']
      rw [hrw, pow_succ']
      calc ‖A *ᵥ (A ^ p *ᵥ v)‖ ≤ ‖A‖ * ‖A ^ p *ᵥ v‖ := Matrix.linfty_opNorm_mulVec _ _
        _ ≤ ‖A‖ * (‖A‖ ^ p * ‖v‖) := mul_le_mul_of_nonneg_left (ih v) (norm_nonneg _)
        _ = ‖A‖ * ‖A‖ ^ p * ‖v‖ := by ring
  -- so the row itself sits under the same power, one generator at a time
  have hrowb : ∀ p, row p ≤ ‖A‖ ^ p * R := by
    intro p
    calc row p ≤ ∑ l, ‖A ^ p *ᵥ Z.G l‖ := by
          refine Finset.sum_le_sum fun l _ => ?_
          calc |(A ^ p *ᵥ Z.G l) i| = ‖(A ^ p *ᵥ Z.G l) i‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖A ^ p *ᵥ Z.G l‖ := norm_le_pi_norm _ i
      _ ≤ ∑ l, ‖A‖ ^ p * ‖Z.G l‖ := Finset.sum_le_sum fun l _ => hpowmulvec p (Z.G l)
      _ = ‖A‖ ^ p * R := by rw [Finset.mul_sum]
  -- the shifted coefficient series, standing in for `[1]`'s continuous non-vanishing factor
  set g : ℝ → ℝ := fun h => 2 * ∑' k : ℕ, h ^ k / (Nat.factorial (k + j + 1) : ℝ) * row (k + j)
    with hgd
  -- `g` is dominated by a shift of the exponential series on `[-1, 1]`
  have hu : Summable (fun k : ℕ => ‖A‖ ^ (k + j) * R / (Nat.factorial (k + j + 1) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((Real.summable_pow_div_factorial ‖A‖).mul_left (‖A‖ ^ j * R))
    have hnum : (0:ℝ) ≤ ‖A‖ ^ j * R * ‖A‖ ^ k := by positivity
    have hle : (Nat.factorial k : ℝ) ≤ (Nat.factorial (k + j + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hlhs : ‖A‖ ^ (k + j) * R / (Nat.factorial (k + j + 1) : ℝ)
        = (‖A‖ ^ j * R * ‖A‖ ^ k) / (Nat.factorial (k + j + 1) : ℝ) := by
      rw [pow_add]; ring
    have hrhs : ‖A‖ ^ j * R * (‖A‖ ^ k / (Nat.factorial k : ℝ))
        = (‖A‖ ^ j * R * ‖A‖ ^ k) / (Nat.factorial k : ℝ) := by ring
    rw [hlhs, hrhs]
    exact div_le_div_of_nonneg_left hnum (by exact_mod_cast k.factorial_pos) hle
  -- so, termwise continuous and uniformly bounded there, its sum is too
  have hcont : ContinuousOn (fun h : ℝ => ∑' k : ℕ, h ^ k / (Nat.factorial (k + j + 1) : ℝ)
      * row (k + j)) (Set.Icc (-1:ℝ) 1) := by
    refine continuousOn_tsum (fun k => ((continuous_pow k).div_const _).mul continuous_const
      |>.continuousOn) hu (fun k h hh => ?_)
    have hb : |h| ≤ 1 := by
      rw [abs_le]; exact ⟨hh.1, hh.2⟩
    calc ‖h ^ k / (Nat.factorial (k + j + 1) : ℝ) * row (k + j)‖
        = |h| ^ k / (Nat.factorial (k + j + 1) : ℝ) * row (k + j) := by
          rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ (Nat.factorial (k + j + 1) : ℝ)),
            abs_of_nonneg (hrownn (k + j))]
      _ ≤ 1 ^ k / (Nat.factorial (k + j + 1) : ℝ) * (‖A‖ ^ (k + j) * R) := by
          have h1 : |h| ^ k ≤ (1:ℝ) ^ k := pow_le_pow_left₀ (abs_nonneg h) hb k
          have h1' : |h| ^ k / (Nat.factorial (k + j + 1) : ℝ)
              ≤ (1:ℝ) ^ k / (Nat.factorial (k + j + 1) : ℝ) :=
            div_le_div_of_nonneg_right h1 (by positivity)
          exact mul_le_mul h1' (hrowb (k + j)) (hrownn (k + j)) (by positivity)
      _ = ‖A‖ ^ (k + j) * R / (Nat.factorial (k + j + 1) : ℝ) := by rw [one_pow]; ring
  -- `Icc (-1) 1` is a neighborhood of `0`, so `g` is continuous there, hence from the right too
  have hgcont : ContinuousWithinAt g (Set.Ici (0:ℝ)) 0 := by
    have hat : ContinuousAt (fun h : ℝ => ∑' k : ℕ, h ^ k / (Nat.factorial (k + j + 1) : ℝ)
        * row (k + j)) 0 :=
      hcont.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
    have hg2 : ContinuousAt g 0 := by
      simpa [hgd] using hat.const_mul (2:ℝ)
    exact hg2.continuousWithinAt
  -- `g 0`'s series has only the `k = 0` term alive, and it is `j`'s own row
  have hg0 : g 0 ≠ 0 := by
    have hsingle : (0:ℝ) ^ (0:ℕ) / (Nat.factorial (0 + j + 1) : ℝ) * row (0 + j)
        = row j / (Nat.factorial (j + 1) : ℝ) := by
      rw [show (0:ℕ) + j = j from Nat.zero_add j, pow_zero]; ring
    have heq : ∑' k : ℕ, (0:ℝ) ^ k / (Nat.factorial (k + j + 1) : ℝ) * row (k + j)
        = row j / (Nat.factorial (j + 1) : ℝ) := by
      rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk]; ring), hsingle]
    have hne : row j / (Nat.factorial (j + 1) : ℝ) ≠ 0 :=
      div_ne_zero hj (by exact_mod_cast (j + 1).factorial_ne_zero)
    simpa [hgd, heq] using hne
  -- the box-diameter series, split at order `j`, is exactly `t^{j+1} * g t` for every `t ≥ 0`
  have hexpall : ∀ h : ℝ, 0 ≤ h →
      boxDiameter (abstrSolInf (fun _ => A) (fun _ => Z.construct) h) i = h ^ (j + 1) * g h := by
    intro h hh
    rw [boxDiameter_abstrSolInf (fun _ => A) (fun _ => Z.construct) hh rfl i]
    -- `f` is the printed series, `f'` its tail from order `j`, both in `row`
    set f : ℕ → ℝ := fun p => h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * row p with hfd
    set f' : ℕ → ℝ := fun k => h ^ (k + j + 1) / (Nat.factorial (k + j + 1) : ℝ) * row (k + j)
      with hf'd
    -- every term of `f` below order `j` vanishes, `j` being the first surviving row
    have hfsum0 : ∑ p ∈ Finset.range j, f p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp0 : row p = 0 := hjmin p (Finset.mem_range.mp hp)
      show h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * row p = 0
      rw [hp0]; ring
    -- `f` sits under the same exponential-type majorant `BoxDiameterAbstrSolInf` uses
    have hmaj : Summable (fun p : ℕ =>
        h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * (‖A‖ ^ p * R)) := by
      refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
        ((Real.summable_pow_div_factorial (h * ‖A‖)).mul_left (h * R))
      · have hc : (0:ℝ) ≤ h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) :=
          div_nonneg (pow_nonneg hh _) (Nat.cast_nonneg _)
        exact mul_nonneg hc (mul_nonneg (pow_nonneg (norm_nonneg A) _) hRnn)
      -- the two sides share a numerator and differ only in `p!` against `(p+1)!`
      · have hnum : (0:ℝ) ≤ h * (h * ‖A‖) ^ p * R := by positivity
        have hp : (0:ℝ) < (Nat.factorial p : ℝ) := by exact_mod_cast p.factorial_pos
        have hle : (Nat.factorial p : ℝ) ≤ (Nat.factorial (p + 1) : ℝ) := by
          exact_mod_cast Nat.factorial_le (Nat.le_succ p)
        have hlhs : h ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * (‖A‖ ^ p * R)
            = (h * (h * ‖A‖) ^ p * R) / (Nat.factorial (p + 1) : ℝ) := by
          rw [mul_pow]; ring
        have hrhs : h * R * ((h * ‖A‖) ^ p / (Nat.factorial p : ℝ))
            = (h * (h * ‖A‖) ^ p * R) / (Nat.factorial p : ℝ) := by ring
        rw [hlhs, hrhs]
        exact div_le_div_of_nonneg_left hnum hp hle
    have hfsummable : Summable f := by
      refine Summable.of_norm_bounded hmaj (fun p => ?_)
      rw [hfd, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (hrownn p)]
      exact mul_le_mul_of_nonneg_left (hrowb p) (by positivity)
    -- shifting `f` by its `j` leading (zero) terms gives `f'`, with the same sum
    have hshift : HasSum f' (∑' p, f p) := by
      have hh2 : HasSum f (∑' p, f p + ∑ p ∈ Finset.range j, f p) := by
        rw [hfsum0, add_zero]; exact hfsummable.hasSum
      have hshift' := (hasSum_nat_add_iff j).mpr hh2
      have hfe : (fun k : ℕ => f (k + j)) = f' := by funext k; simp only [hfd, hf'd]
      rwa [hfe] at hshift'
    have htsum : ∑' k, f' k = ∑' p, f p := hshift.tsum_eq
    -- and `f'`'s own terms already factor `h^{j+1}` out of `g`'s series
    have hf'eq : ∀ k, f' k
        = h ^ (j + 1) * (h ^ k / (Nat.factorial (k + j + 1) : ℝ) * row (k + j)) := by
      intro k
      show h ^ (k + j + 1) / (Nat.factorial (k + j + 1) : ℝ) * row (k + j)
          = h ^ (j + 1) * (h ^ k / (Nat.factorial (k + j + 1) : ℝ) * row (k + j))
      rw [show k + j + 1 = j + 1 + k from by omega, pow_add]; ring
    calc 2 * ∑' p, f p = 2 * ∑' k, f' k := by rw [htsum]
      _ = 2 * ∑' k, h ^ (j + 1) * (h ^ k / (Nat.factorial (k + j + 1) : ℝ) * row (k + j)) := by
          rw [tsum_congr hf'eq]
      _ = 2 * (h ^ (j + 1) * ∑' k, h ^ k / (Nat.factorial (k + j + 1) : ℝ) * row (k + j)) := by
          rw [tsum_mul_left]
      _ = h ^ (j + 1) * g h := by simp only [hgd]; ring
  have hexp : ∀ᶠ t in 𝓝[≥] (0:ℝ),
      boxDiameter (abstrSolInf (fun _ => A) (fun _ => Z.construct) t) i = t ^ (j + 1) * g t := by
    filter_upwards [self_mem_nhdsWithin] with t ht using hexpall t ht
  exact gainDim_tendsto_pow (fun _ => A) (fun _ => Z.construct) i hδ hgcont hg0 hexp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
