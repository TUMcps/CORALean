import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsSubsetIff
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp

/-!
# AH-polytope in AH-polytope, exactly, when `Y` is injective

`[1, Cor. 1]`: when `Y` has a left inverse (independent columns), `[1, Thm. 1, Eq. 12]` is
necessary as well as sufficient. A full-dimensional `Px` (`[1, Thm. 1]`'s hypothesis) puts
every column of `X` and `ȳ - x̄` in `range Y`, giving `Γ` and `β`; injectivity of `Y` then
turns the containment into `-β + Γ Px ⊆ Py`, an H-in-H containment, and
`ineqs_subset_iff` supplies `Λ`.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nx ny qx qy : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_subset_iff_of_injective {xbar ybar : Vec ℝ n} {X : Mat ℝ n nx}
    {Y : Mat ℝ n ny} {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx} {Hy : Mat ℝ qy ny} {hy : Vec ℝ qy}
    (hY : Function.Injective Y.mulVec)
    (hfull : (interior (HPolytope.ineqs Hx hx).construct).Nonempty) :
    HPolytope.ahPolytope xbar X (HPolytope.ineqs Hx hx)
        ⊆ HPolytope.ahPolytope ybar Y (HPolytope.ineqs Hy hy) ↔
      ∃ (Γ : Mat ℝ ny nx) (β : Vec ℝ ny) (Λ : Mat ℝ qy qx), X = Y * Γ ∧
        ybar - xbar = Y *ᵥ β ∧ (∀ i j, 0 ≤ Λ i j) ∧ Λ * Hx = Hy * Γ ∧
        Λ *ᵥ hx ≤ hy + Hy *ᵥ β := by -- --- PROOF ---
  constructor
  · intro hsub
    obtain ⟨p0, hp0⟩ := hfull
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p0 hp0
    have hmem : ∀ p ∈ (HPolytope.ineqs Hx hx).construct,
        ∃ q ∈ (HPolytope.ineqs Hy hy).construct, xbar + X *ᵥ p = ybar + Y *ᵥ q :=
      fun p hp => by
        obtain ⟨q, hq, he⟩ := hsub ⟨p, hp, rfl⟩
        exact ⟨q, hq, he⟩
    obtain ⟨q0, -, he0⟩ := hmem p0 (interior_subset hp0)
    -- each column of `X` is a difference of two points of `Y Py`, scaled
    have hcol : ∀ k, ∃ w : Vec ℝ ny, Y *ᵥ w = X *ᵥ Pi.single k 1 := by
      intro k
      have hin : p0 + (ε / 2) • Pi.single k (1 : ℝ) ∈ (HPolytope.ineqs Hx hx).construct := by
        refine interior_subset (hball ?_)
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Pi.norm_single,
          norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
        exact half_lt_self hε
      obtain ⟨q, -, he⟩ := hmem _ hin
      rw [mulVec_add, mulVec_smul] at he
      have e1 : Y *ᵥ q = xbar + (X *ᵥ p0 + (ε / 2) • X *ᵥ Pi.single k 1) - ybar := by
        rw [he]; abel
      have e2 : Y *ᵥ q0 = xbar + X *ᵥ p0 - ybar := by rw [he0]; abel
      refine ⟨(2 / ε) • (q - q0), ?_⟩
      rw [mulVec_smul, mulVec_sub, e1, e2,
        show xbar + (X *ᵥ p0 + (ε / 2) • X *ᵥ Pi.single k 1) - ybar - (xbar + X *ᵥ p0 - ybar)
          = (ε / 2) • X *ᵥ Pi.single k 1 by abel,
        smul_smul, show 2 / ε * (ε / 2) = 1 by field_simp, one_smul]
    -- `Γ` collects those preimages column by column
    choose w hw using hcol
    let Γ : Mat ℝ ny nx := Matrix.of fun r k => w k r
    have hXΓ : X = Y * Γ := by
      ext i k
      have := congrFun (hw k) i
      simp only [mulVec_single_one, Matrix.col_apply] at this
      rw [Matrix.mul_apply, ← this]
      simp [mulVec, dotProduct, Γ]
    -- `ȳ - x̄ = X p₀ - Y q₀ = Y (Γ p₀ - q₀)`
    let β := Γ *ᵥ p0 - q0
    have hβ : ybar - xbar = Y *ᵥ β := by
      simp only [β]
      rw [mulVec_sub, mulVec_mulVec, ← hXΓ, eq_sub_of_add_eq he0.symm]
      abel
    -- injectivity turns the containment into `Γ p - β ∈ Py`
    have hPx : (HPolytope.ineqs Hx hx).construct
        ⊆ (HPolytope.ineqs (Hy * Γ) (hy + Hy *ᵥ β)).construct := by
      intro p hp
      obtain ⟨q, hq, he⟩ := hmem p hp
      have hq' : Γ *ᵥ p - β = q := hY (by
        rw [mulVec_sub, mulVec_mulVec, ← hXΓ, ← hβ]
        rw [eq_sub_of_add_eq he.symm]
        abel)
      rw [HPolytope.mem_ineqs_iff] at hq ⊢
      intro i
      have := hq i
      rw [← hq', mulVec_sub, mulVec_mulVec, Pi.sub_apply] at this
      rw [Pi.add_apply]
      linarith
    obtain ⟨Λ, hΛ, h1, h2⟩ :=
      (HPolytope.ineqs_subset_iff ⟨p0, interior_subset hp0⟩).mp hPx
    exact ⟨Γ, β, Λ, hXΓ, hβ, hΛ, h1, h2⟩
  · rintro ⟨Γ, β, Λ, hX, hβ, hΛ, h1, h2⟩
    exact HPolytope.ahPolytope_subset_of_cert hX hβ hΛ h1 h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
