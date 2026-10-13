import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullSatisfies
import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConPolyZono.Real.Theorems.ConvHullSingleExact
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Interval.Real.Theorems.Convex
import Mathlib.Analysis.Convex.Combination

/-!
# `ConPolyZono.convHullSingle` contains the convex hull

The exact layer's closed form is the convex hull of the read-back operand's nominal set
(`convHullSingle_exact`, with Carathéodory at `a = n + 1` or more), and the hull of the nominal
set plus a box is the hull of the nominal set plus the box, a box being convex. A point of the
exact form lies in the stored one at the same factors, up to the centre `a c`, which is stored from
below: its shortfall is the residual the stored box holds.

No independent generators, as over ℝ, and at least `n + 1` copies.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Read back, a stored generator is the exact layer's. -/
theorem ConPolyZono.aux_toReal_convHullG (a : ℕ) {h : ℕ} (c : Vec 𝕋 n) (G : Fin h → Vec 𝕋 n)
    (l : Fin (a + (a * h + a * h))) (i : Fin n) :
    toReal (ConPolyZono.convHullG a c G l i)
      = Real.ConPolyZono.convHullG a (toRealVec c) (fun l i => toReal (G l i))
        l i := by -- --- PROOF ---
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · simp only [ConPolyZono.convHullG, Real.ConPolyZono.convHullG, Fin.append_left, toRealVec]
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
      simp only [ConPolyZono.convHullG, Real.ConPolyZono.convHullG, Fin.append_left,
        Fin.append_right, Real.ConPolyZono.repVec]

/-- The stored nominal point at factors the exact form satisfies, which the stored form does
too, moved by the shortfall of the centre. -/
theorem ConPolyZono.aux_convHullSingle_mem (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (v : Fin (a * cPZ.p + a) → ℝ) (hv : ∀ k, |v k| ≤ 1)
    (hsat : (Real.ConPolyZono.convHullSingle a (nominal cPZ)).satisfies v) :
    (fun i => toReal ((cPZ.convHullSingle a).c i)
      + ∑ l, toReal ((cPZ.convHullSingle a).G l i)
        * Real.PolyZonotope.monomial (cPZ.convHullSingle a).E v l)
      ∈ nominalSet (cPZ.convHullSingle a) := by -- --- PROOF ---
  refine ConPolyZono.mem_nominalSet_iff.mpr ⟨v, fun j => j.elim0, hv, fun j => j.elim0,
    ConPolyZono.convHullSingle_satisfies_of_real a cPZ v hsat, fun i => ?_⟩
  -- no independent generators
  have h0 : ∀ f : Fin (cPZ.convHullSingle a).q → ℝ, ∑ j, f j = 0 := fun f =>
    Finset.sum_eq_zero fun j _ => Fin.elim0 (show Fin 0 from j)
  rw [h0, add_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.convHullSingle_outer (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (hq : cPZ.q = 0)
    (ha : n + 1 ≤ a) :
    convexHull ℝ cPZ.construct ⊆ (cPZ.convHullSingle a).construct := by -- --- PROOF ---
  intro x hx
  -- the hull of the nominal set plus the box is the nominal hull plus the box
  have hx' : x ∈ convexHull ℝ (nominalSet cPZ + cPZ.err.construct) := hx
  have hconv : Convex ℝ cPZ.err.construct := Real.Interval.convex_construct _
  rw [convexHull_add, hconv.convexHull_eq] at hx'
  obtain ⟨r, hr, e, he, rfl⟩ := hx'
  -- the nominal hull is the exact form on the read-back operand
  have hR := Real.ConPolyZono.convHullSingle_exact a (nominal cPZ) hq
    (by rw [Module.finrank_fin_fun]; exact ha)
  have hr' : r ∈ (Real.ConPolyZono.convHullSingle a (nominal cPZ)).construct := by
    rw [hR]
    exact hr
  obtain ⟨v, β, hv, hβ, hsat, hr⟩ := hr'
  -- no independent generators in the exact form, and the factor vector with its own type
  have h0 : (∑ j, β j • (Real.ConPolyZono.convHullSingle a (nominal cPZ)).GI j) = 0 :=
    Finset.sum_eq_zero fun j _ => Fin.elim0 (show Fin 0 from j)
  obtain ⟨w, hw, hsatw, hrw⟩ : ∃ w : Fin (a * cPZ.p + a) → ℝ, (∀ k, |w k| ≤ 1)
      ∧ (Real.ConPolyZono.convHullSingle a (nominal cPZ)).satisfies w
      ∧ r = (a : ℝ) • toRealVec cPZ.c
        + ∑ l, Real.PolyZonotope.monomial (Real.ConPolyZono.convHullE a cPZ.E) w l
          • Real.ConPolyZono.convHullG a (toRealVec cPZ.c) (fun l i => toReal (cPZ.G l i)) l :=
    ⟨v, hv, hsat, by rw [hr, h0, add_zero]; rfl⟩
  have hz := ConPolyZono.aux_convHullSingle_mem a cPZ w hw hsatw
  -- what storing `a c` from below leaves to pay
  have hd : (fun i => (a : ℝ) * toReal (cPZ.c i) - toReal (nsmulDown a (cPZ.c i)))
      ∈ (Interval.residual (fun i => nsmulDown a (cPZ.c i)) (fun i => nsmulUp a (cPZ.c i))
        (fun i => nsmulDown a (cPZ.c i))).construct :=
    Interval.sub_mem_residual fun i => ⟨nsmulDown_le a (cPZ.c i), le_nsmulUp a (cPZ.c i)⟩
  refine ⟨_, hz, e + _, Interval.plus_outer _ _ ⟨e, he, _, hd, rfl⟩, ?_⟩
  funext i
  have hri := congrFun hrw i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hri ⊢
  -- the stored generator sum is the exact form's, read at coordinate `i`
  have hsum : (∑ l, toReal ((cPZ.convHullSingle a).G l i)
        * Real.PolyZonotope.monomial (cPZ.convHullSingle a).E w l)
      = ∑ l, Real.PolyZonotope.monomial (Real.ConPolyZono.convHullE a cPZ.E) w l
        * Real.ConPolyZono.convHullG a (toRealVec cPZ.c) (fun l i => toReal (cPZ.G l i)) l i :=
    Finset.sum_congr rfl fun l _ => by
      rw [mul_comm]
      exact congrArg _ (ConPolyZono.aux_toReal_convHullG a cPZ.c cPZ.G l i)
  -- the centre `a c` against its stored shortfall
  have hc : (cPZ.convHullSingle a).c i = nsmulDown a (cPZ.c i) := rfl
  rw [hc, hsum]
  simp only [toRealVec] at hri
  linarith [hri]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
