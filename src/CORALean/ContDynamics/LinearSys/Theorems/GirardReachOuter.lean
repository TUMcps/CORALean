import CORALean.ContDynamics.LinearSys.Theorems.GirardReachEq
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetAddEq
import CORALean.ContDynamics.LinearSys.Theorems.IUnionReachSetSubsetLinCombPlusCube
import CORALean.ContSet.Zonotope.Real.Theorems.IsLUBNormFoldMaxAbsBound

/-!
# [1, Alg. 1] encloses the reachable set

[1, Thm. 1], conservative approximation: `R_[0,T](I) ⊆ R_{N-1}`, the union of the `Qᵢ`
`girardReach` returns. The printed induction: `Φ_t(I) ⊆ Q₀` for `t ∈ [0, r]` by [1, Lemma 2],
and `Φ_t(I) = e^{rA}Φ_{t-r}(I) + inputReach U r ⊆ e^{rA}Qᵢ + □(β_r) = Qᵢ₊₁` for
`t ∈ [(i+1)r, (i+2)r]` by `reachSet_add_eq` and eq. 3 of [1]. A time in `[0, T]` lies in
one of the `N = ⌈T/r⌉` windows, so `T` need not be a multiple of `r`.

`R_[0,T](I)` is the union of `Φ_t(I)` over `t ∈ [0, T]`, as Sec. 3 of [1] defines it.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A time in `[0, T]` lies in the window `[i r, (i+1) r]` of some `i < ⌈T/r⌉`, or of `i = 0`. -/
theorem aux_exists_window {r T t : ℝ} (hr : 0 < r) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∃ i < ⌈T / r⌉₊ - 1 + 1, (i : ℝ) * r ≤ t ∧ t ≤ ((i : ℝ) + 1) * r := by -- --- PROOF ---
  set N := ⌈T / r⌉₊
  have hfl := Nat.floor_le (div_nonneg ht0 hr.le)
  have hlt := Nat.lt_floor_add_one (t / r)
  rcases le_or_gt ⌊t / r⌋₊ (N - 1) with h | h
  · refine ⟨⌊t / r⌋₊, by omega, ?_, ?_⟩
    · rwa [le_div_iff₀ hr] at hfl
    · exact ((div_le_iff₀ hr).mp hlt.le)
  · refine ⟨N - 1, by omega, ?_, ?_⟩
    · have : ((N - 1 : ℕ) : ℝ) ≤ ⌊t / r⌋₊ := by exact_mod_cast h.le
      calc ((N - 1 : ℕ) : ℝ) * r ≤ ⌊t / r⌋₊ * r := by gcongr
        _ ≤ t := (le_div_iff₀ hr).mp hfl
    · have hN : (N : ℝ) ≤ ((N - 1 : ℕ) : ℝ) + 1 := by
        have : N ≤ N - 1 + 1 := by omega
        exact_mod_cast this
      have hT : T / r ≤ N := Nat.le_ceil _
      calc t ≤ T := htT
        _ ≤ N * r := (div_le_iff₀ hr).mp hT
        _ ≤ (((N - 1 : ℕ) : ℝ) + 1) * r := by gcongr


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], conservative approximation: `R_[0,T](I) ⊆ R_{N-1}`. -/
theorem LinearSys.girardReach_outer (sys : LinearSys 𝕋 n) (I U : Zonotope (Vec ℝ n))
    {μ r T : ℝ} (hA : 0 < ‖toRealMat sys.A‖) (hr : 0 < r) (hμ : 0 ≤ μ)
    (hU : U.construct = Metric.closedBall 0 μ) :
    ⋃ t ∈ Set.Icc (0:ℝ) T, sys.reachSet (S := 𝒵) (Set.Icc 0 t) I U t
      ⊆ ⋃ Q ∈ sys.girardReach I μ r T, Q.construct := by -- --- PROOF ---
  set A := toRealMat sys.A
  set E := exp (r • A)
  set β := (Real.exp (r * ‖A‖) - 1) / ‖A‖ * μ
  set f : Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n) := fun Q => (Q.mtimes E).plus (Zonotope.cube n β)
  set Q₀ := (I.linComb (I.mtimes E)).plus (Zonotope.cube n
    ((Real.exp (r * ‖A‖) - 1 - r * ‖A‖) * Finset.univ.fold max 0 I.absBound + β))
  have hx := Real.add_one_le_exp (r * ‖A‖)
  have hβ0 : 0 ≤ β := mul_nonneg (div_nonneg (by nlinarith [mul_pos hr hA]) hA.le) hμ
  have hUb : Bornology.IsBounded (construct U) := Zonotope.isBounded_construct U
  have hUle : ∀ u ∈ construct U, ‖u‖ ≤ μ := fun u hu => by
    have : u ∈ Metric.closedBall (0 : Vec ℝ n) μ := hU ▸ hu
    exact mem_closedBall_zero_iff.mp this
  -- every window lands in its own iterate
  have hwin : ∀ i : ℕ, ∀ t ∈ Set.Icc ((i : ℝ) * r) (((i : ℝ) + 1) * r),
      sys.reachSet (S := 𝒵) (Set.Icc 0 t) I U t ⊆ (f^[i] Q₀).construct := by
    intro i
    induction i with
    | zero =>
      intro t ht y hy
      simp only [Nat.cast_zero, zero_mul, zero_add, one_mul] at ht
      exact sys.iUnion_reachSet_subset_linComb_plus_cube I U hA hr.le hμ hU
        (fun z hz => (I.isLUB_norm_image_fold_max_absBound).1 ⟨z, hz, rfl⟩)
        (Set.mem_iUnion₂.mpr ⟨t, ht, hy⟩)
    | succ i ih =>
      intro t ht y hy
      -- the next window is `e^{rA}` of this one plus the input over `r`
      have ht' : t - r ∈ Set.Icc ((i : ℝ) * r) (((i : ℝ) + 1) * r) := by
        push_cast at ht; constructor <;> linarith [ht.1, ht.2]
      have hti : 0 ≤ t - r := (mul_nonneg (Nat.cast_nonneg i) hr.le).trans ht'.1
      rw [show t = (t - r) + r by ring,
        sys.reachSet_add_eq (S := 𝒵) I U hti hr.le hUb] at hy
      obtain ⟨_, ⟨q, hq, rfl⟩, v, hv, rfl⟩ := hy
      rw [Function.iterate_succ_apply']
      show E *ᵥ q + v ∈ ((f^[i] Q₀).mtimes E |>.plus (Zonotope.cube n β)).construct
      rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact, Zonotope.cube_exact n hβ0]
      exact ⟨_, ⟨q, ih _ ht' hq, rfl⟩, v,
        mem_closedBall_zero_iff.mpr (sys.norm_le_of_mem_inputReach hA hr.le hUle hv), rfl⟩
  -- and every time in `[0, T]` lies in one of the `N` windows
  intro y hy
  obtain ⟨t, ⟨ht0, htT⟩, hyt⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨i, hi, hti⟩ := aux_exists_window hr ht0 htT
  rw [sys.girardReach_eq]
  exact Set.mem_iUnion₂.mpr ⟨f^[i] Q₀, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩,
    hwin i t hti hyt⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
