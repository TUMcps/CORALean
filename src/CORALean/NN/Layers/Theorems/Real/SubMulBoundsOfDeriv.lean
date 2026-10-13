module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# A slope out of a bound on the derivative

The mean value theorem read as a bracket. `Relaxation.ofMonotone` carries slope zero because
monotonicity is all it has; a slope needs second-order information, and the cheapest form is a
bracket `m ≤ σ' ≤ M` over the box. Every increment of `σ` is then between `m` and `M` times the
increment of its argument, so `σ t - λ t` stays within `(M - m) (u - l)` of its value at `l`.
The theorem asks only what that argument uses: continuity on the closed box and a derivative on
the open one, so a kink at an endpoint costs nothing. It is about the exact `σ` and the exact
reals a scalar's values denote, which is why `Relaxation.ofDeriv` reuses it at every scalar.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `m ≤ σ' ≤ M` over the box, `σ t - lam * t` cannot leave the ends the bracket allows. -/
theorem sub_mul_bounds_of_deriv {σ σ' : ℝ → ℝ} {m M lam l u t : ℝ}
    (hc : ContinuousOn σ (Set.Icc l u))
    (hd : ∀ x, l < x → x < u → HasDerivAt σ (σ' x) x)
    (hm : ∀ x, l ≤ x → x ≤ u → m ≤ σ' x) (hM : ∀ x, l ≤ x → x ≤ u → σ' x ≤ M)
    (hml : m ≤ lam) (hlM : lam ≤ M) (hl : l ≤ t) (hu : t ≤ u) :
    σ l - lam * l + (m - lam) * (u - l) ≤ σ t - lam * t
      ∧ σ t - lam * t ≤ σ l - lam * l + (M - lam) * (u - l) := by -- --- PROOF ---
  have hw : 0 ≤ u - l := by linarith
  rcases eq_or_lt_of_le hl with hlt | hlt
  · -- a box with `t` at its left end: both ends straddle zero, which is the claim
    subst hlt
    have h₁ : 0 ≤ (lam - m) * (u - l) := mul_nonneg (by linarith) hw
    have h₂ : 0 ≤ (M - lam) * (u - l) := mul_nonneg (by linarith) hw
    exact ⟨by linarith, by linarith⟩
  · have hcont : ContinuousOn σ (Set.Icc l t) := hc.mono (Set.Icc_subset_Icc le_rfl hu)
    obtain ⟨c, hcm, hceq⟩ := exists_hasDerivAt_eq_slope σ σ' hlt hcont
      fun x hx => hd x hx.1 (hx.2.trans_le hu)
    have hlow := hm c (le_of_lt hcm.1) (le_trans (le_of_lt hcm.2) hu)
    have hhigh := hM c (le_of_lt hcm.1) (le_trans (le_of_lt hcm.2) hu)
    rw [hceq] at hlow hhigh
    have hpos : 0 < t - l := by linarith
    -- the slope over `[l, t]` is in the bracket, so the increment is bracketed too
    rw [le_div_iff₀ hpos] at hlow
    rw [div_le_iff₀ hpos] at hhigh
    have hspan : t - l ≤ u - l := by linarith
    have hup : (M - lam) * (t - l) ≤ (M - lam) * (u - l) :=
      mul_le_mul_of_nonneg_left hspan (by linarith)
    have hdn : (m - lam) * (u - l) ≤ (m - lam) * (t - l) :=
      mul_le_mul_of_nonpos_left hspan (by linarith)
    exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
