module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStepEqIff
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStepPos
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStepContinuousAt
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStepMonotoneOn
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStationarityStrictAntiOn
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-!
# Halder's fixed-point iteration converges

[1, Thm. 3]: from any `β₀ > 0` the iteration `β ↦ g(β)` of [1, Eq. 26] converges to the
unique positive root of [1, Eq. 18]. The printed proof calls `g` a contraction in the Hilbert
metric on the cone `ℝ₊`, which is degenerate on a one-dimensional cone; here `g` is monotone
and fixes the root, so the orbit from below rises to it and the orbit from above falls to
it, and the limit of a bounded monotone orbit is a fixed point by continuity.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_limit_root [Nonempty ι] (hlam : ∀ i, 0 < lam i) {r L : ℝ} (hr : 0 < r)
    (hroot : Ellipsoid.halderStationarity lam r = 0) (hL : 0 < L) {b : ℕ → ℝ}
    (hb : ∀ n, b (n + 1) = Ellipsoid.halderStep lam (b n))
    (hlim : Filter.Tendsto b Filter.atTop (nhds L)) : L = r := by -- --- PROOF ---
  -- the limit is fixed by the step, since the step is continuous there
  have hg : Filter.Tendsto (fun n => Ellipsoid.halderStep lam (b n)) Filter.atTop
      (nhds (Ellipsoid.halderStep lam L)) :=
    ((Ellipsoid.halderStep_continuousAt hlam hL).tendsto).comp hlim
  have hshift : Filter.Tendsto (fun n => b (n + 1)) Filter.atTop (nhds L) :=
    hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hfix : Ellipsoid.halderStep lam L = L := by
    refine tendsto_nhds_unique hg ?_
    simpa [hb] using hshift
  -- a fixed point is a root, and the root is unique
  have hLroot := (Ellipsoid.halderStep_eq_iff hlam hL).1 hfix
  exact (Ellipsoid.halderStationarity_strictAntiOn hlam).injOn (Set.mem_Ici.2 hL.le)
    (Set.mem_Ici.2 hr.le) (by rw [hLroot, hroot])


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3]: the iteration [1, Eq. 26] converges to the root of [1, Eq. 18]. -/
theorem Ellipsoid.halderStep_iterate_tendsto [Nonempty ι] (hlam : ∀ i, 0 < lam i)
    {r : ℝ} (hr : 0 < r) (hroot : Ellipsoid.halderStationarity lam r = 0) {b₀ : ℝ}
    (hb₀ : 0 < b₀) :
    Filter.Tendsto (fun n => (Ellipsoid.halderStep lam)^[n] b₀) Filter.atTop
      (nhds r) := by -- --- PROOF ---
  -- the orbit, positive throughout
  set b : ℕ → ℝ := fun n => (Ellipsoid.halderStep lam)^[n] b₀ with hbdef
  have hb : ∀ n, b (n + 1) = Ellipsoid.halderStep lam (b n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hbpos : ∀ n, 0 < b n := by
    intro n
    induction n with
    | zero => exact hb₀
    | succ n ih => rw [hb]; exact Ellipsoid.halderStep_pos hlam ih.le
  have hfix : Ellipsoid.halderStep lam r = r := (Ellipsoid.halderStep_eq_iff hlam hr).2 hroot
  have hanti := Ellipsoid.halderStationarity_strictAntiOn hlam
  have hmono := Ellipsoid.halderStep_monotoneOn hlam
  -- `β ≤ g(β)` below the root and `g(β) ≤ β` above it
  have hup : ∀ β, 0 < β → β ≤ r → β ≤ Ellipsoid.halderStep lam β := by
    intro β hβ hβr
    have h0 := hanti.antitoneOn (Set.mem_Ici.2 hβ.le) (Set.mem_Ici.2 hr.le) hβr
    rw [hroot] at h0
    rcases h0.lt_or_eq with h0 | h0
    · exact ((Ellipsoid.lt_halderStep_iff hlam hβ.le).2 h0).le
    · exact ((Ellipsoid.halderStep_eq_iff hlam hβ).2 h0.symm).ge
  have hdown : ∀ β, 0 < β → r ≤ β → Ellipsoid.halderStep lam β ≤ β := by
    intro β hβ hrβ
    have h0 := hanti.antitoneOn (Set.mem_Ici.2 hr.le) (Set.mem_Ici.2 hβ.le) hrβ
    rw [hroot] at h0
    rcases h0.lt_or_eq with h0 | h0
    · exact ((Ellipsoid.halderStep_lt_iff hlam hβ).2 h0).le
    · exact ((Ellipsoid.halderStep_eq_iff hlam hβ).2 h0).le
  rcases le_total b₀ r with hle | hle
  · -- below the root the orbit rises and stays below it
    have hbd : ∀ n, b n ≤ r := by
      intro n
      induction n with
      | zero => exact hle
      | succ n ih =>
        rw [hb]
        exact (hmono (Set.mem_Ici.2 (hbpos n).le) (Set.mem_Ici.2 hr.le) ih).trans_eq hfix
    have hmon : Monotone b := monotone_nat_of_le_succ fun n => by
      rw [hb]
      exact hup _ (hbpos n) (hbd n)
    have hbdd : BddAbove (Set.range b) := ⟨r, by rintro _ ⟨n, rfl⟩; exact hbd n⟩
    have hlim := tendsto_atTop_ciSup hmon hbdd
    have hLpos : 0 < ⨆ n, b n := lt_of_lt_of_le hb₀ (le_ciSup hbdd 0)
    have := Ellipsoid.aux_limit_root hlam hr hroot hLpos hb hlim
    rwa [this] at hlim
  · -- above the root it falls and stays above it
    have hbd : ∀ n, r ≤ b n := by
      intro n
      induction n with
      | zero => exact hle
      | succ n ih =>
        rw [hb]
        exact hfix ▸ hmono (Set.mem_Ici.2 hr.le) (Set.mem_Ici.2 (hbpos n).le) ih
    have hmon : Antitone b := antitone_nat_of_succ_le fun n => by
      rw [hb]
      exact hdown _ (hbpos n) (hbd n)
    have hbdd : BddBelow (Set.range b) := ⟨r, by rintro _ ⟨n, rfl⟩; exact hbd n⟩
    have hlim := tendsto_atTop_ciInf hmon hbdd
    have hLpos : 0 < ⨅ n, b n := lt_of_lt_of_le hr (le_ciInf hbd)
    have := Ellipsoid.aux_limit_root hlam hr hroot hLpos hb hlim
    rwa [this] at hlim

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
