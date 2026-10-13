module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLogDet
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderLogDetHasDerivAt
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStationarityStrictAntiOn
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# The root of Halder's stationarity equation minimises the volume

[1, Eq. 19]: the positive root of [1, Eq. 18] is a minimum of `log det Q(β)`. Here it is
the global one over `β > 0`: the derivative is `−(1/(β(1+β)))` times a strictly decreasing
function that vanishes at the root, so it is negative before it and positive after, and the
criterion falls to the root and rises from it.

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 19]: the root of [1, Eq. 18] minimises the criterion of [1, Eq. 14] on `(0, ∞)`. -/
theorem Ellipsoid.halderLogDet_isMinOn [Nonempty ι] (hlam : ∀ i, 0 < lam i) {r : ℝ}
    (hr : 0 < r) (hroot : Ellipsoid.halderStationarity lam r = 0) :
    IsMinOn (Ellipsoid.halderLogDet lam) (Set.Ioi 0) r := by -- --- PROOF ---
  have hanti := Ellipsoid.halderStationarity_strictAntiOn hlam
  have hd := fun β (hβ : 0 < β) => Ellipsoid.halderLogDet_hasDerivAt hlam hβ
  have hcont : ContinuousOn (Ellipsoid.halderLogDet lam) (Set.Ioi 0) :=
    fun β hβ => (hd β hβ).continuousAt.continuousWithinAt
  intro β hβ
  simp only [Set.mem_setOf_eq]
  rcases le_total β r with h | h
  · -- left of the root the derivative is negative
    have hanti' : AntitoneOn (Ellipsoid.halderLogDet lam) (Set.Ioc 0 r) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 r) (hcont.mono fun x hx => hx.1) ?_ ?_
      · intro x hx
        rw [interior_Ioc] at hx
        exact (hd x hx.1).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ioc] at hx
        rw [(hd x hx.1).deriv]
        have hpos : 0 < Ellipsoid.halderStationarity lam x := by
          have := hanti (Set.mem_Ici.2 hx.1.le) (Set.mem_Ici.2 hr.le) hx.2
          rwa [hroot] at this
        have : 0 < 1 / (x * (1 + x)) := by have := hx.1; positivity
        nlinarith
    exact hanti' ⟨hβ, h⟩ ⟨hr, le_rfl⟩ h
  · -- right of it, positive
    have hmono : MonotoneOn (Ellipsoid.halderLogDet lam) (Set.Ici r) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici r)
        (hcont.mono fun x hx => lt_of_lt_of_le hr hx) ?_ ?_
      · intro x hx
        rw [interior_Ici] at hx
        exact (hd x (hr.trans hx)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        have hx0 : 0 < x := hr.trans hx
        rw [(hd x hx0).deriv]
        have hneg : Ellipsoid.halderStationarity lam x < 0 := by
          have := hanti (Set.mem_Ici.2 hr.le) (Set.mem_Ici.2 hx0.le) hx
          rwa [hroot] at this
        have : 0 < 1 / (x * (1 + x)) := by positivity
        nlinarith
    exact hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
