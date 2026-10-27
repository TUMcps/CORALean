module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryOfHasDerivWithinAt
public import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffAddSubsetReachSetExact
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddAssoc
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Brouwer
public import CORALean.Global.EuclideanGenOpNorm
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.EMetricSpace.Lipschitz

@[expose] public section

/-!
# The hull of the two eroded time-point sets, shrunk by `B_µ`, as an inner time-interval set

[1, Prop. 2] with (23)'s hull eroded by the ball `B_µ` of [2], `µ = √γ‖(e^{AΔt} - I)G‖₂`,
for a convex `X₀` in a zonotope `⟨c₀, G⟩`, `γ` generators: `conv(A₀ ∪ A₁) ⊖ B_µ + 2c ⊆ R(τ₀)`,
`A₀ = (X₀ ⊖ C) ⊖ R̂_err`, `A₁ = (R_aff ⊖ R̂_err) ⊖ C`. `R̂(Δt)`'s shift `2 cen(R̂_err)` is `0`, (13)
making `R̂_err` symmetric about `0`. A hull point `θa + (1 - θ)k` is within
`θ(1 - θ)‖(M - I)(a₂ - a₁)‖₂ ≤ µ/2` of the chord of `θa₁ + (1 - θ)a₂` at `1 - θ`; Brouwer's
theorem on `B_µ(y) × E`, with the hull representation interpolated continuously over a finite
net, and Grönwall give a run through `y + 2c`. That every solution stays within `E = C ⊕ R̂_err`
of its chord is a hypothesis.

## Inputs
* `sys` – system
* `X₀` – initial set
* `Z` – zonotope containing it
* `U` – input set
* `Δt` – step size
* `M` – transition matrix
* `v` – particular solution
* `C` – curvature error set
* `Rerr` – abstraction error set
* `c` – center of symmetry
* `u₀` – constant input
* `Ω` – Lipschitz region
* `K` – Lipschitz constant

## Hypotheses
* `hX₀` – initial set convex
* `hXZ` – initial set inside the zonotope
* `hΔt` – step size positive
* `hM` – matrix invertible
* `hE` – error set compact
* `hEc` – error set convex
* `hEne` – error set nonempty
* `hEs` – error set symmetric about center
* `hu₀` – input in input set
* `hLip` – field Lipschitz on region
* `hex` – solutions exist from every start
* `herr` – solutions lie within the error set of their chord

## Conclusion
* the shifted, ball-eroded hull lies in the exact time-interval reachable set

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
* [2] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix Pointwise Set

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A Minkowski difference from a convex set is convex. -/
private theorem NonlinearSys.aux_convex_minkowskiDiff {A B : Set (Vec ℝ n)} (hA : Convex ℝ A) :
    Convex ℝ (minkowskiDiff A B) := by
  intro x hx z hz a b ha hb hab e he
  have h := hA (hx e he) (hz e he) ha hb hab
  convert h using 1
  rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]

/-- The Euclidean ball `{p | ‖p - y‖₂ ≤ r}` is compact and convex. -/
private theorem NonlinearSys.aux_ball₂ (y : Vec ℝ n) (r : ℝ) : -- --- CONCL ---
    IsCompact {p : Vec ℝ n | ‖p - y‖₂ ≤ r} ∧
      Convex ℝ {p : Vec ℝ n | ‖p - y‖₂ ≤ r} := by -- --- PROOF ---
  -- closed and inside the sup-norm ball of radius `r`
  refine ⟨Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_norm₂.comp (continuous_id.sub continuous_const)) continuous_const)
    ((Metric.isBounded_closedBall (x := y) (r := r)).subset fun p hp => ?_), ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg ((norm₂_nonneg _).trans hp)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact (abs_le_norm₂ _ i).trans hp
  · -- `‖·‖₂` is convex
    intro p hp q hq a b ha hb hab
    show ‖a • p + b • q - y‖₂ ≤ r
    have he : a • (p - y) + b • (q - y) = a • p + b • q - (a + b) • y := by
      simp only [smul_sub, add_smul]; abel
    rw [hab, one_smul] at he
    rw [← he]
    refine (norm₂_add_le _ _).trans ?_
    rw [norm₂_smul, norm₂_smul, abs_of_nonneg ha, abs_of_nonneg hb]
    have h1 := mul_le_mul_of_nonneg_left (show ‖p - y‖₂ ≤ r from hp) ha
    have h2 := mul_le_mul_of_nonneg_left (show ‖q - y‖₂ ≤ r from hq) hb
    have h3 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
    linarith

/-- Two points `a`, `b` of a zonotope differ by `G β`, `‖β‖₂ ≤ 2√γ`, so
`‖N (b - a)‖₂ ≤ 2 √γ ‖N G‖₂`. -/
private theorem NonlinearSys.aux_norm₂_mulVec_sub_le (Z : Real.Zonotope (Vec ℝ n))
    (N : Mat ℝ n n) {a b : Vec ℝ n} (ha : a ∈ Z.construct)
    (hb : b ∈ Z.construct) : -- --- CONCL ---
    ‖N *ᵥ (b - a)‖₂ ≤ 2 * (Real.sqrt Z.h * genOpNorm₂ fun j => N *ᵥ Z.G j) := by -- --- PROOF ---
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  have hdiff : N *ᵥ (Z.c + ∑ j, β j • Z.G j - (Z.c + ∑ j, α j • Z.G j)) =
      ∑ j, (β - α) j • (N *ᵥ Z.G j) := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, Matrix.mulVec_smul, Pi.sub_apply]
  rw [hdiff]
  refine (norm₂_sum_smul_le_genOpNorm₂_mul_norm₂ _ _).trans ?_
  have hn : ‖β - α‖ ≤ 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun j => by
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have := abs_sub (β j) (α j)
    linarith [hα j, hβ j]
  have h2 : ‖β - α‖₂ ≤ Real.sqrt Z.h * 2 :=
    (norm₂_le_sqrt_mul_norm _).trans (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))
  have hg := genOpNorm₂_nonneg fun j => N *ᵥ Z.G j
  nlinarith

/-- The hull point `θa₁ + (1 - θ)(M a₂ + v)` minus the chord of `θa₁ + (1 - θ)a₂` at `1 - θ` is
`θ(1 - θ)(M - I)(a₂ - a₁)`. -/
private theorem NonlinearSys.aux_sub_chord (M : Mat ℝ n n) (v a₁ a₂ : Vec ℝ n) (θ : ℝ) :
    θ • a₁ + (1 - θ) • (M *ᵥ a₂ + v) - (θ • a₁ + (1 - θ) • a₂ + (1 - θ) •
      (M *ᵥ (θ • a₁ + (1 - θ) • a₂) + v - (θ • a₁ + (1 - θ) • a₂))) =
      (θ * (1 - θ)) • ((M - 1) *ᵥ (a₂ - a₁)) := by
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_sub]
  module

/-- A nonnegatively weighted sum of points of a convex set `A` is its total weight times a
point of `A`. -/
private theorem NonlinearSys.aux_exists_sum_smul_eq {ι : Type} {A : Set (Vec ℝ n)}
    (hA : Convex ℝ A) {a₀ : Vec ℝ n} (ha₀ : a₀ ∈ A) (T : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ T, 0 ≤ w i) (z : ι → Vec ℝ n) (hz : ∀ i ∈ T, z i ∈ A) : -- --- CONCL ---
    ∃ a ∈ A, ∑ i ∈ T, w i • z i = (∑ i ∈ T, w i) • a := by -- --- PROOF ---
  by_cases hs : ∑ i ∈ T, w i = 0
  · -- every weight vanishes
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hs
    refine ⟨a₀, ha₀, ?_⟩
    rw [hs, zero_smul]
    exact Finset.sum_eq_zero fun i hi => by rw [h0 i hi, zero_smul]
  · refine ⟨∑ i ∈ T, ((∑ j ∈ T, w j)⁻¹ * w i) • z i,
      hA.sum_mem (fun i hi => mul_nonneg (inv_nonneg.mpr (Finset.sum_nonneg hw)) (hw i hi))
        (by rw [← Finset.mul_sum, inv_mul_cancel₀ hs]) hz, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- A continuous representation of the hull over the ball `B_µ(y)`: weights `θ` and weighted
points `α = θa`, `β = (1 - θ)k`, `a ∈ A₀`, `k ∈ A₁`, interpolated over a finite net, whose sum is
within `µ/2` of the point and `µ/2` short of the ball's radius. -/
private theorem NonlinearSys.aux_exists_continuous_rep {A₀ A₁ : Set (Vec ℝ n)}
    (hA₀ : Convex ℝ A₀) (hA₁ : Convex ℝ A₁) (h₀ : A₀.Nonempty) (h₁ : A₁.Nonempty) (y : Vec ℝ n)
    {μ : ℝ} (hμ : 0 ≤ μ)
    (hy : ∀ p : Vec ℝ n, ‖p - y‖₂ ≤ μ → p ∈ convexHull ℝ (A₀ ∪ A₁)) : -- --- CONCL ---
    ∃ (θR : Vec ℝ n → ℝ) (αR βR : Vec ℝ n → Vec ℝ n),
      ContinuousOn θR {p | ‖p - y‖₂ ≤ μ} ∧ ContinuousOn αR {p | ‖p - y‖₂ ≤ μ} ∧
      ContinuousOn βR {p | ‖p - y‖₂ ≤ μ} ∧ ∀ q, ‖q - y‖₂ ≤ μ → θR q ∈ Icc 0 1 ∧
        (∃ a ∈ A₀, αR q = θR q • a) ∧ (∃ k ∈ A₁, βR q = (1 - θR q) • k) ∧
        μ / 2 + ‖αR q + βR q - q‖₂ ≤ μ := by -- --- PROOF ---
  classical
  set Q := {p : Vec ℝ n | ‖p - y‖₂ ≤ μ}
  -- every point of the ball has a representation `θa + (1 - θ)k`
  have hrep : ∀ p, ∃ θ : ℝ, ∃ a k : Vec ℝ n, p ∈ Q →
      θ ∈ Icc 0 1 ∧ a ∈ A₀ ∧ k ∈ A₁ ∧ θ • a + (1 - θ) • k = p := by
    intro p
    by_cases hp : p ∈ Q
    · have h := hy p hp
      rw [hA₀.convexHull_union hA₁ h₀ h₁] at h
      obtain ⟨a, ha, k, hk, θ₁, θ₂, h1, h2, h12, hp'⟩ := mem_convexJoin.mp h
      refine ⟨θ₁, a, k, fun _ => ⟨⟨h1, by linarith⟩, ha, hk, ?_⟩⟩
      rw [← hp', ← h12, add_sub_cancel_left]
    · exact ⟨0, 0, 0, fun h => absurd h hp⟩
  choose θf af kf hrepf using hrep
  -- a finite net of the ball at radius `ε`
  set ε : ℝ := if 0 < μ then μ / 2 else 1
  have hε : 0 < ε := by
    simp only [ε]; split_ifs with h
    · exact half_pos h
    · exact one_pos
  have hQc : IsCompact Q := (aux_ball₂ y μ).1
  have hcov : Q ⊆ ⋃ p ∈ Q, {q : Vec ℝ n | ‖q - p‖₂ < ε} := fun q hq =>
    mem_biUnion hq (show ‖q - q‖₂ < ε by rw [sub_self, norm₂_zero]; exact hε)
  obtain ⟨T', hT'Q, hT'f, hT'cov⟩ := hQc.elim_finite_subcover_image (b := Q)
    (c := fun p => {q : Vec ℝ n | ‖q - p‖₂ < ε})
    (fun p _ => isOpen_lt (continuous_norm₂.comp (continuous_id.sub continuous_const))
      continuous_const) hcov
  set T := hT'f.toFinset
  have hTQ : ∀ p ∈ T, p ∈ Q := fun p hp => hT'Q (hT'f.mem_toFinset.mp hp)
  -- tent weights `max 0 (ε - ‖q - p‖₂)`, normalized, positive somewhere on the ball
  set w : Vec ℝ n → Vec ℝ n → ℝ := fun p q => max 0 (ε - ‖q - p‖₂)
  set S : Vec ℝ n → ℝ := fun q => ∑ p ∈ T, w p q
  have hw0 : ∀ p q, 0 ≤ w p q := fun p q => le_max_left _ _
  have hS : ∀ q ∈ Q, 0 < S q := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := mem_iUnion₂.mp (hT'cov hq)
    exact Finset.sum_pos' (fun p _ => hw0 p q)
      ⟨p, hT'f.mem_toFinset.mpr hp, lt_max_of_lt_right (sub_pos.mpr hpq)⟩
  set ψ : Vec ℝ n → Vec ℝ n → ℝ := fun p q => w p q / S q
  have hψ0 : ∀ p q, q ∈ Q → 0 ≤ ψ p q := fun p q hq => div_nonneg (hw0 p q) (hS q hq).le
  have hψ1 : ∀ q ∈ Q, ∑ p ∈ T, ψ p q = 1 := fun q hq => by
    simp only [ψ, ← Finset.sum_div]; exact div_self (hS q hq).ne'
  -- the weights are continuous on the ball, so the interpolated representation is
  have hwc : ∀ p, Continuous (w p) := fun p =>
    continuous_const.max (continuous_const.sub
      (continuous_norm₂.comp (continuous_id.sub continuous_const)))
  have hψc : ∀ p, ContinuousOn (ψ p) Q := fun p =>
    (hwc p).continuousOn.div (continuous_finsetSum _ fun p _ => hwc p).continuousOn
      fun q hq => (hS q hq).ne'
  refine ⟨fun q => ∑ p ∈ T, ψ p q * θf p, fun q => ∑ p ∈ T, (ψ p q * θf p) • af p,
    fun q => ∑ p ∈ T, (ψ p q * (1 - θf p)) • kf p,
    continuousOn_finsetSum _ fun p _ => (hψc p).mul continuousOn_const,
    continuousOn_finsetSum _ fun p _ => ((hψc p).mul continuousOn_const).smul continuousOn_const,
    continuousOn_finsetSum _ fun p _ => ((hψc p).mul continuousOn_const).smul continuousOn_const,
    fun q hq => ?_⟩
  beta_reduce
  have hθ : ∀ p ∈ T, θf p ∈ Icc 0 1 := fun p hp => (hrepf p (hTQ p hp)).1
  -- the total weight on `A₁` is `1 - θ`
  have h1θ : ∑ p ∈ T, ψ p q * (1 - θf p) = 1 - ∑ p ∈ T, ψ p q * θf p := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hψ1 q hq]
  refine ⟨⟨Finset.sum_nonneg fun p hp => mul_nonneg (hψ0 p q hq) (hθ p hp).1, ?_⟩, ?_, ?_, ?_⟩
  · calc ∑ p ∈ T, ψ p q * θf p ≤ ∑ p ∈ T, ψ p q :=
          Finset.sum_le_sum fun p hp => mul_le_of_le_one_right (hψ0 p q hq) (hθ p hp).2
      _ = 1 := hψ1 q hq
  · exact aux_exists_sum_smul_eq hA₀ h₀.some_mem T _
      (fun p hp => mul_nonneg (hψ0 p q hq) (hθ p hp).1) af fun p hp => (hrepf p (hTQ p hp)).2.1
  · obtain ⟨k, hk, hsum⟩ := aux_exists_sum_smul_eq hA₁ h₁.some_mem T _
      (fun p hp => mul_nonneg (hψ0 p q hq) (sub_nonneg.mpr (hθ p hp).2)) kf
      fun p hp => (hrepf p (hTQ p hp)).2.2.1
    exact ⟨k, hk, by rw [hsum, h1θ]⟩
  · -- the represented point is `∑ ψ p`, each `p` with `ψ > 0` within `ε` of `q` and `2µ` of it
    have hsum : ∑ p ∈ T, (ψ p q * θf p) • af p + ∑ p ∈ T, (ψ p q * (1 - θf p)) • kf p - q =
        ∑ p ∈ T, ψ p q • (p - q) := by
      -- each net point's two weighted parts add up to it
      have e1 : ∀ p ∈ T, (ψ p q * θf p) • af p + (ψ p q * (1 - θf p)) • kf p = ψ p q • p :=
        fun p hp => by rw [mul_smul, mul_smul, ← smul_add, (hrepf p (hTQ p hp)).2.2.2]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl e1]
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hψ1 q hq, one_smul]
    rw [hsum]
    set B : ℝ := if 0 < μ then μ / 2 else 0
    have hB : μ / 2 + B ≤ μ := by
      simp only [B]; split_ifs with h
      · linarith
      · linarith
    have hcomm : ∀ x z : Vec ℝ n, ‖x - z‖₂ = ‖z - x‖₂ := fun x z => by
      rw [← neg_sub, ← neg_one_smul ℝ (z - x), norm₂_smul, abs_neg, abs_one, one_mul]
    have hterm : ∀ p ∈ T, ‖ψ p q • (p - q)‖₂ ≤ ψ p q * B := by
      intro p hp
      rw [norm₂_smul, abs_of_nonneg (hψ0 p q hq)]
      by_cases hψp : ψ p q = 0
      · rw [hψp, zero_mul, zero_mul]
      refine mul_le_mul_of_nonneg_left ?_ (hψ0 p q hq)
      simp only [B]
      split_ifs with h
      · -- a positive weight puts `p` within `ε = µ/2` of `q`
        have hw : 0 < w p q := lt_of_le_of_ne (hw0 p q) fun h' => hψp (by simp [ψ, ← h'])
        have hlt : ‖q - p‖₂ < ε := by
          by_contra hc
          exact absurd hw (not_lt.mpr (max_le le_rfl (by linarith)))
        simp only [ε, if_pos h] at hlt
        rw [hcomm]; exact hlt.le
      · -- `µ = 0`: the ball is the point `y`
        have hμ0 : μ = 0 := le_antisymm (not_lt.mp h) hμ
        have hp' : ‖p - y‖₂ ≤ 0 := hμ0 ▸ hTQ p hp
        have hq' : ‖q - y‖₂ ≤ 0 := hμ0 ▸ hq
        have := norm₂_add_le (p - y) (y - q)
        rw [sub_add_sub_cancel, hcomm y q] at this
        linarith
    calc μ / 2 + ‖∑ p ∈ T, ψ p q • (p - q)‖₂ ≤ μ / 2 + ∑ p ∈ T, ψ p q * B := by
          gcongr
          exact (norm₂_sum_le _ _).trans (Finset.sum_le_sum hterm)
      _ = μ / 2 + B := by rw [← Finset.sum_mul, hψ1 q hq, one_mul]
      _ ≤ μ := hB

/-- Brouwer's theorem on `B_µ(y) × E`: with the hull represented continuously over the ball and
the chords' deviation within `µ/2`, some run passes through `y + 2c`. -/
private theorem NonlinearSys.aux_add_mem_of_continuous_rep (sys : NonlinearSys n m)
    {X₀ : Set (Vec ℝ n)} (hX₀ : Convex ℝ X₀) (U : Set (Vec ℝ m)) {Δt : ℝ} (hΔt : 0 < Δt)
    (M Minv : Mat ℝ n n) (hMM : M * Minv = 1) (v : Vec ℝ n)
    {E : Set (Vec ℝ n)} (hE : IsCompact E) (hEc : Convex ℝ E) (hEne : E.Nonempty) {c : Vec ℝ n}
    (hEs : ∀ e ∈ E, (2 : ℝ) • c - e ∈ E) {u₀ : Vec ℝ m} (hu₀ : u₀ ∈ U)
    {Ω : Set (Vec ℝ n)} {K : NNReal} (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ X₀, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t)
    (herr : ∀ t ∈ Icc 0 Δt, ∀ x₀ ∈ X₀, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ s ∈ Icc 0 t, HasDerivWithinAt x (sys.f (x s) u₀) (Icc 0 t) s) →
      x t - (x₀ + (t / Δt) • (M *ᵥ x₀ + v - x₀)) ∈ E)
    {A₀ A₁ : Set (Vec ℝ n)} (hA₀ : ∀ a ∈ A₀, ∀ e ∈ E, a + e ∈ X₀)
    (hA₁ : ∀ k ∈ A₁, ∀ e ∈ E, Minv *ᵥ (k + e - v) ∈ X₀)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ∀ a ∈ X₀, ∀ b ∈ X₀, ‖(M - 1) *ᵥ (b - a)‖₂ ≤ 2 * μ)
    (y : Vec ℝ n) (θR : Vec ℝ n → ℝ) (αR βR : Vec ℝ n → Vec ℝ n)
    (hθc : ContinuousOn θR {p | ‖p - y‖₂ ≤ μ}) (hαc : ContinuousOn αR {p | ‖p - y‖₂ ≤ μ})
    (hβc : ContinuousOn βR {p | ‖p - y‖₂ ≤ μ})
    (hR : ∀ q, ‖q - y‖₂ ≤ μ → θR q ∈ Icc 0 1 ∧ (∃ a ∈ A₀, αR q = θR q • a) ∧
      (∃ k ∈ A₁, βR q = (1 - θR q) • k) ∧ μ / 2 + ‖αR q + βR q - q‖₂ ≤ μ) : -- --- CONCL ---
    y + (2 : ℝ) • c ∈
      ⋃ t ∈ Icc 0 Δt, sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t := by -- --- PROOF ---
  classical
  choose sol hsol0 hsol using hex
  set F : Vec ℝ n × ℝ → Vec ℝ n := fun q => if h : q.1 ∈ X₀ then sol q.1 h q.2 else 0
  -- each solution is continuous on `[0, Δt]` and solves the equation from the right
  have hcont : ∀ x₀ (h : x₀ ∈ X₀), ContinuousOn (sol x₀ h) (Icc 0 Δt) := fun x₀ h t ht =>
    (hsol x₀ h t ht).2.continuousWithinAt
  have hIci : ∀ x₀ (h : x₀ ∈ X₀), ∀ t ∈ Ico 0 Δt,
      HasDerivWithinAt (sol x₀ h) (sys.f (sol x₀ h t) u₀) (Ici t) t := fun x₀ h t ht =>
    (hsol x₀ h t (Ico_subset_Icc_self ht)).2.mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  -- Grönwall: `x₀ ↦ x(t)` is `e^{KΔt}`-Lipschitz on `X₀` at every `t`, so `F` is continuous
  have hF : ContinuousOn F (X₀ ×ˢ Icc 0 Δt) := by
    refine continuousOn_prod_of_continuousOn_lipschitzOnWith F
      ⟨Real.exp (K * Δt), (Real.exp_pos _).le⟩ (fun a ha => ?_) (fun t ht => ?_)
    · refine (hcont a ha).congr fun s _ => ?_
      simp only [F, dif_pos ha]
    · refine LipschitzOnWith.of_dist_le_mul fun b hb b' hb' => ?_
      have hd := dist_le_of_trajectories_ODE_of_mem (v := fun _ x => sys.f x u₀)
        (s := fun _ => Ω) (fun _ _ => hLip) (hcont b hb) (hIci b hb)
        (fun t ht => (hsol b hb t (Ico_subset_Icc_self ht)).1) (hcont b' hb') (hIci b' hb')
        (fun t ht => (hsol b' hb' t (Ico_subset_Icc_self ht)).1)
        (le_of_eq (by rw [hsol0 b hb, hsol0 b' hb'])) t ht
      have hk : Real.exp (K * t) ≤ Real.exp (K * Δt) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.2)
      simp only [F, dif_pos hb, dif_pos hb']
      calc _ ≤ dist b b' * Real.exp (K * (t - 0)) := hd
        _ ≤ dist b b' * Real.exp (K * Δt) := by
          rw [sub_zero]; exact mul_le_mul_of_nonneg_left hk dist_nonneg
        _ = _ := by rw [mul_comm]; rfl
  set Q := {p : Vec ℝ n | ‖p - y‖₂ ≤ μ}
  -- the start `θ(a + e) + (1 - θ)M⁻¹(k + e - v)`, the time `(1 - θ)Δt`, the chord point, `d`, `φ`
  set x₀f : Vec ℝ n × Vec ℝ n → Vec ℝ n := fun pe =>
    αR pe.1 + θR pe.1 • pe.2 + Minv *ᵥ (βR pe.1 + (1 - θR pe.1) • (pe.2 - v))
  set sf : Vec ℝ n × Vec ℝ n → ℝ := fun pe => 1 - θR pe.1
  set chord : Vec ℝ n × Vec ℝ n → Vec ℝ n := fun pe =>
    x₀f pe + sf pe • (M *ᵥ x₀f pe + v - x₀f pe)
  set d : Vec ℝ n × Vec ℝ n → Vec ℝ n := fun pe => αR pe.1 + βR pe.1 + pe.2 - chord pe
  set φ : Vec ℝ n × Vec ℝ n → Vec ℝ n := fun pe => F (x₀f pe, sf pe * Δt) - chord pe
  set G : Vec ℝ n × Vec ℝ n → Vec ℝ n × Vec ℝ n := fun pe =>
    (y + d pe + (pe.1 - (αR pe.1 + βR pe.1)), (2 : ℝ) • c - φ pe)
  -- on `Q × E` the start lies in `X₀`, the time in `[0, Δt]`, and `‖d‖₂ ≤ µ/2`
  have hval : ∀ pe ∈ Q ×ˢ E, x₀f pe ∈ X₀ ∧ sf pe * Δt ∈ Icc 0 Δt ∧ ‖d pe‖₂ ≤ μ / 2 := by
    rintro ⟨q, e⟩ ⟨hq, he⟩
    obtain ⟨hθ, ⟨a, ha, hα⟩, ⟨k, hk, hβ⟩, -⟩ := hR q hq
    have ha₁ := hA₀ a ha e he
    have ha₂ := hA₁ k hk e he
    have hinner : (1 - θR q) • k + (1 - θR q) • (e - v) = (1 - θR q) • (k + e - v) := by
      module
    have hx : x₀f (q, e) = θR q • (a + e) + (1 - θR q) • (Minv *ᵥ (k + e - v)) := by
      simp only [x₀f, hα, hβ, hinner, Matrix.mulVec_smul]
      module
    have hMa₂ : M *ᵥ (Minv *ᵥ (k + e - v)) + v = k + e := by
      rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec, sub_add_cancel]
    have hP : αR q + βR q + e =
        θR q • (a + e) + (1 - θR q) • (M *ᵥ (Minv *ᵥ (k + e - v)) + v) := by
      rw [hMa₂, hα, hβ]; module
    -- the start is in `X₀`, the time in `[0, Δt]`; `d` is `θ(1 - θ)(M - I)(a₂ - a₁)`
    refine ⟨hx ▸ hX₀ ha₁ ha₂ hθ.1 (sub_nonneg.mpr hθ.2) (by ring),
      ⟨mul_nonneg (sub_nonneg.mpr hθ.2) hΔt.le, by nlinarith [hθ.1]⟩, ?_⟩
    have hd : d (q, e) =
        (θR q * (1 - θR q)) • ((M - 1) *ᵥ (Minv *ᵥ (k + e - v) - (a + e))) := by
      rw [← aux_sub_chord M v (a + e) (Minv *ᵥ (k + e - v)) (θR q)]
      simp only [d, chord, sf]
      rw [hP, hx]
    rw [hd, norm₂_smul]
    have h4 : |θR q * (1 - θR q)| ≤ 1 / 4 := by
      rw [abs_of_nonneg (mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2))]
      nlinarith [sq_nonneg (θR q - 1 / 2)]
    have hb := hμ _ ha₁ _ ha₂
    nlinarith [norm₂_nonneg ((M - 1) *ᵥ (Minv *ᵥ (k + e - v) - (a + e))),
      abs_nonneg (θR q * (1 - θR q))]
  -- the run's deviation `φ` lies in `E`
  have hφ : ∀ pe ∈ Q ×ˢ E, φ pe ∈ E := by
    intro pe hpe
    obtain ⟨hx₀, ht, -⟩ := hval pe hpe
    have h := herr _ ht _ hx₀ _ (hsol0 _ hx₀) fun s hs =>
      (hsol _ hx₀ s ⟨hs.1, hs.2.trans ht.2⟩).2.mono (Icc_subset_Icc_right ht.2)
    rw [mul_div_cancel_right₀ _ hΔt.ne'] at h
    simpa only [φ, F, dif_pos hx₀] using h
  -- `G` maps `Q × E` into itself
  have hcomm : ∀ x z : Vec ℝ n, ‖x - z‖₂ = ‖z - x‖₂ := fun x z => by
    rw [← neg_sub, ← neg_one_smul ℝ (z - x), norm₂_smul, abs_neg, abs_one, one_mul]
  have hGmaps : MapsTo G (Q ×ˢ E) (Q ×ˢ E) := by
    intro pe hpe
    refine ⟨?_, hEs _ (hφ pe hpe)⟩
    show ‖y + d pe + (pe.1 - (αR pe.1 + βR pe.1)) - y‖₂ ≤ μ
    have h1 := (hval pe hpe).2.2
    have h2 := (hR pe.1 hpe.1).2.2.2
    rw [add_assoc, add_sub_cancel_left]
    refine (norm₂_add_le _ _).trans ?_
    rw [hcomm pe.1]
    linarith
  -- `G` is continuous on `Q × E`
  have hfst : MapsTo Prod.fst (Q ×ˢ E) Q := fun pe hpe => hpe.1
  have hθc' := hθc.comp continuousOn_fst hfst
  have hαc' := hαc.comp continuousOn_fst hfst
  have hβc' := hβc.comp continuousOn_fst hfst
  have hlin : ∀ N : Mat ℝ n n, Continuous fun x : Vec ℝ n => N *ᵥ x := fun N =>
    (Matrix.mulVecLin N).continuous_of_finiteDimensional
  have hx₀c : ContinuousOn x₀f (Q ×ˢ E) :=
    (hαc'.add (hθc'.smul continuousOn_snd)).add ((hlin Minv).comp_continuousOn
      (hβc'.add ((continuousOn_const.sub hθc').smul (continuousOn_snd.sub continuousOn_const))))
  have hsc : ContinuousOn sf (Q ×ˢ E) := continuousOn_const.sub hθc'
  have hchc : ContinuousOn chord (Q ×ˢ E) :=
    hx₀c.add (hsc.smul (((hlin M).comp_continuousOn hx₀c).add continuousOn_const |>.sub hx₀c))
  have hFc : ContinuousOn (fun pe => F (x₀f pe, sf pe * Δt)) (Q ×ˢ E) :=
    hF.comp (hx₀c.prodMk (hsc.mul continuousOn_const)) fun pe hpe =>
      ⟨(hval pe hpe).1, (hval pe hpe).2.1⟩
  -- and so is `G`
  have hGc : ContinuousOn G (Q ×ˢ E) :=
    (((continuousOn_const.add (((hαc'.add hβc').add continuousOn_snd).sub hchc)).add
      (continuousOn_fst.sub (hαc'.add hβc')))).prodMk (continuousOn_const.sub (hFc.sub hchc))
  -- Brouwer's fixed point `(q, e)`: `d = P - y`, `φ = 2c - e`, so the run is at `y + 2c`
  obtain ⟨hQc, hQconv⟩ := aux_ball₂ y μ
  obtain ⟨e₀, he₀⟩ := hEne
  have hy₀ : y ∈ Q := show ‖y - y‖₂ ≤ μ by rw [sub_self, norm₂_zero]; exact hμ0
  obtain ⟨⟨q, e⟩, hqe, hfix⟩ := exists_fixedPoint_of_isCompact_convex (hQc.prod hE)
    (hQconv.prod hEc) ⟨(y, e₀), hy₀, he₀⟩ hGc hGmaps
  obtain ⟨hx₀, ht, -⟩ := hval (q, e) hqe
  have h1 : y + d (q, e) + (q - (αR q + βR q)) = q := congrArg Prod.fst hfix
  have h2 : (2 : ℝ) • c - φ (q, e) = e := congrArg Prod.snd hfix
  -- the run's value: chord plus `φ`, the chord `P + e - d`
  have hval' : y + (2 : ℝ) • c = sol (x₀f (q, e)) hx₀ (sf (q, e) * Δt) := by
    have hF' : F (x₀f (q, e), sf (q, e) * Δt) = sol (x₀f (q, e)) hx₀ (sf (q, e) * Δt) :=
      dif_pos hx₀
    rw [← hF']
    have hφ' : F (x₀f (q, e), sf (q, e) * Δt) = φ (q, e) + chord (q, e) := by
      simp only [φ, sub_add_cancel]
    have hd' : chord (q, e) = αR q + βR q + e - d (q, e) := by simp only [d]; abel
    have hφe : φ (q, e) = (2 : ℝ) • c - e := eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp h2).symm
    have hdP : d (q, e) = αR q + βR q - y := by
      rw [← sub_eq_zero] at h1 ⊢
      rw [← h1]
      abel
    rw [hφ', hd', hφe, hdP]
    abel
  -- the solution, restricted to `[0, t]`, is a run
  set t := sf (q, e) * Δt
  have hfc : ContinuousOn (fun s => sys.f (sol (x₀f (q, e)) hx₀ s) u₀) (Icc 0 t) :=
    hLip.continuousOn.comp ((hcont _ hx₀).mono (Icc_subset_Icc_right ht.2))
      fun s hs => (hsol _ hx₀ s ⟨hs.1, hs.2.trans ht.2⟩).1
  refine mem_iUnion₂.mpr ⟨t, ht, sol _ hx₀, fun _ => u₀,
    NonlinearSys.IsTrajectory.of_hasDerivWithinAt (convex_Icc 0 t) ⟨le_rfl, ht.1⟩
      (by rw [hsol0 _ hx₀]; exact hx₀) (fun _ _ => hu₀)
      (fun s hs => (hsol _ hx₀ s ⟨hs.1, hs.2.trans ht.2⟩).2.mono (Icc_subset_Icc_right ht.2))
      (fun s hs => (hfc.mono (uIcc_subset_Icc ⟨le_rfl, ht.1⟩ hs)).intervalIntegrable),
    hval'.symm⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] with (23)'s hull eroded by `B_µ`, `µ = √γ‖(M - I)G‖₂`: for a convex `X₀` in the
zonotope `⟨c₀, G⟩`, `conv(A₀ ∪ A₁) ⊖ B_µ + 2c ⊆ R(τ₀)`, given that every solution stays within
`E = C ⊕ R̂_err` of its chord. -/
theorem NonlinearSys.minkowskiDiff_convexHull_ball_subset_reachSetExact (sys : NonlinearSys n m)
    {X₀ : Set (Vec ℝ n)} (hX₀ : Convex ℝ X₀) (Z : Real.Zonotope (Vec ℝ n))
    (hXZ : X₀ ⊆ Z.construct) (U : Set (Vec ℝ m)) {Δt : ℝ} (hΔt : 0 < Δt) (M : Mat ℝ n n)
    (hM : IsUnit M.det) (v : Vec ℝ n) (C Rerr : Set (Vec ℝ n)) (hE : IsCompact (C + Rerr))
    (hEc : Convex ℝ (C + Rerr)) (hEne : (C + Rerr).Nonempty) {c : Vec ℝ n}
    (hEs : ∀ e ∈ C + Rerr, (2 : ℝ) • c - e ∈ C + Rerr) {u₀ : Vec ℝ m} (hu₀ : u₀ ∈ U)
    {Ω : Set (Vec ℝ n)} {K : NNReal} (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ X₀, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t)
    (herr : ∀ t ∈ Icc 0 Δt, ∀ x₀ ∈ X₀, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ s ∈ Icc 0 t, HasDerivWithinAt x (sys.f (x s) u₀) (Icc 0 t) s) →
      x t - (x₀ + (t / Δt) • (M *ᵥ x₀ + v - x₀)) ∈ C + Rerr) : -- --- CONCL ---
    let Raff := (fun x₀ => M *ᵥ x₀ + v) '' X₀ -- (10)
    let μ := Real.sqrt Z.h * genOpNorm₂ fun j => (M - 1) *ᵥ Z.G j -- [2]
    (fun s => s + (2 : ℝ) • c) '' minkowskiDiff (convexHull ℝ
        (minkowskiDiff (minkowskiDiff X₀ C) Rerr ∪ minkowskiDiff (minkowskiDiff Raff Rerr) C))
        {y | ‖y‖₂ ≤ μ}
      ⊆ ⋃ t ∈ Icc 0 Δt, sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t := by -- --- PROOF ---
  intro Raff μ
  rintro _ ⟨y, hy, rfl⟩
  set E := C + Rerr
  set A₀ := minkowskiDiff (minkowskiDiff X₀ C) Rerr
  set A₁ := minkowskiDiff (minkowskiDiff Raff Rerr) C
  have hμ0 : 0 ≤ μ := mul_nonneg (Real.sqrt_nonneg _) (genOpNorm₂_nonneg _)
  have hRaff : Convex ℝ Raff := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩ a b ha hb hab
    refine ⟨a • x + b • z, hX₀ hx hz ha hb hab, ?_⟩
    show M *ᵥ (a • x + b • z) + v = a • (M *ᵥ x + v) + b • (M *ᵥ z + v)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_add, smul_add,
      add_add_add_comm, ← add_smul, hab, one_smul]
  -- `A₀ = X₀ ⊖ E`, `A₁ = R_aff ⊖ E`
  have hA₀E : A₀ = minkowskiDiff X₀ E := (minkowskiDiff_add_assoc X₀ C Rerr).symm
  have hA₁E : A₁ = minkowskiDiff Raff E := by
    rw [show E = Rerr + C from add_comm C Rerr]
    exact (minkowskiDiff_add_assoc Raff Rerr C).symm
  have hA₀c : Convex ℝ A₀ := hA₀E ▸ aux_convex_minkowskiDiff hX₀
  have hA₁c : Convex ℝ A₁ := hA₁E ▸ aux_convex_minkowskiDiff hRaff
  have hy0 : y ∈ convexHull ℝ (A₀ ∪ A₁) := by
    have h := hy 0 (show ‖(0 : Vec ℝ n)‖₂ ≤ μ by rw [norm₂_zero]; exact hμ0)
    rwa [add_zero] at h
  by_cases h₀ : A₀.Nonempty
  · by_cases h₁ : A₁.Nonempty
    · -- both nonempty: Brouwer on `B_µ(y) × E`
      obtain ⟨θR, αR, βR, hθc, hαc, hβc, hR⟩ := aux_exists_continuous_rep hA₀c hA₁c h₀ h₁ y
        hμ0 fun p hp => by
          have h := hy (p - y) hp
          rwa [add_sub_cancel] at h
      refine aux_add_mem_of_continuous_rep sys hX₀ U hΔt M M⁻¹ (Matrix.mul_nonsing_inv M hM) v
        hE hEc hEne hEs hu₀ hLip hex herr (A₀ := A₀) (A₁ := A₁) (fun a ha e he => ?_)
        (fun k hk e he => ?_) hμ0
        (fun a ha b hb => aux_norm₂_mulVec_sub_le Z (M - 1) (hXZ ha) (hXZ hb)) y θR αR βR hθc hαc
        hβc hR
      · exact (show a ∈ minkowskiDiff X₀ E from hA₀E ▸ ha) e he
      · obtain ⟨x, hx, hxe⟩ := (show k ∈ minkowskiDiff Raff E from hA₁E ▸ hk) e he
        rw [← hxe, add_sub_cancel_right, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM,
          Matrix.one_mulVec]
        exact hx
    · -- `A₁ = ∅`: `y ⊕ E ⊆ X₀`, and `0 ∈ E`, so `y + 2c ∈ X₀`, reached at `t = 0`
      rw [not_nonempty_iff_eq_empty.mp h₁, union_empty, hA₀c.convexHull_eq, hA₀E] at hy0
      obtain ⟨e₀, he₀⟩ := hEne
      obtain ⟨x, hx0, hx⟩ := hex _ (hy0 e₀ he₀)
      have hd0 : ∀ x : ℝ → Vec ℝ n, (∀ t ∈ Icc 0 Δt,
          x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t) →
          ∀ s ∈ Icc (0 : ℝ) 0, HasDerivWithinAt x (sys.f (x s) u₀) (Icc 0 0) s :=
        fun x hx s hs => (hx s ⟨hs.1, hs.2.trans hΔt.le⟩).2.mono (Icc_subset_Icc_right hΔt.le)
      have h0E : (0 : Vec ℝ n) ∈ E := by
        have h := herr 0 ⟨le_rfl, hΔt.le⟩ _ (hy0 e₀ he₀) x hx0 (hd0 x hx)
        rwa [zero_div, zero_smul, add_zero, hx0, sub_self] at h
      have hmem : y + (2 : ℝ) • c ∈ X₀ := by
        have h := hy0 _ (hEs 0 h0E)
        rwa [sub_zero] at h
      obtain ⟨x', hx'0, hx'⟩ := hex _ hmem
      refine mem_iUnion₂.mpr ⟨0, ⟨le_rfl, hΔt.le⟩, x', fun _ => u₀,
        NonlinearSys.IsTrajectory.of_hasDerivWithinAt (convex_Icc 0 0) ⟨le_rfl, le_rfl⟩
          (by rw [hx'0]; exact hmem) (fun _ _ => hu₀) (hd0 x' hx')
          (fun s hs => by rw [le_antisymm hs.2 hs.1]), hx'0⟩
  · -- `A₀ = ∅`: `y ∈ R_aff ⊖ E`, [1, Prop. 1] at `Δt`
    rw [not_nonempty_iff_eq_empty.mp h₀, empty_union, hA₁c.convexHull_eq, hA₁E] at hy0
    refine mem_iUnion₂.mpr ⟨Δt, ⟨hΔt.le, le_rfl⟩,
      NonlinearSys.minkowskiDiff_add_subset_reachSetExact (S := 𝒮) sys X₀ U hΔt.le M hM v hE hEc
        ⟨_, hEne.some_mem⟩ hEs hu₀ hLip hex (fun x₀ hx₀ x hx0 hd => ?_) ⟨y, hy0, rfl⟩⟩
    have h := herr Δt ⟨hΔt.le, le_rfl⟩ x₀ hx₀ x hx0 hd
    rwa [div_self hΔt.ne', one_smul, add_sub_cancel] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
