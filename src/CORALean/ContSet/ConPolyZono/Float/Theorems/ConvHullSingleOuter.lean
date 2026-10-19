module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullSatisfies
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ConvHullSingleExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConvHullSingleConsIff
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.ExistsRelaxIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialConvHullEPadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.Relax
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# `ConPolyZono.convHullSingle` contains the convex hull

The exact layer's closed form is the convex hull of the operand's nominal set
(`convHullSingle_exact`, with Carathéodory at `a = n + 1` or more), and the hull of the nominal
set plus a box is the hull of the nominal set plus the box, a box being convex. A point of the
exact form lies in the stored one at the same factors with each copy's slack factors dropped
(`monomial_convHullE_padE`), a copy's row then being within its slack
(`PolyLevelSet.exists_relax_iff`), up to the
center `a c`, which is stored from below: its shortfall is the residual the stored box holds.

No independent generators, as over ℝ, and at least `n + 1` copies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Read back, a stored generator is the exact layer's. -/
theorem ConPolyZono.aux_toReal_convHullG (a : ℕ) {h : ℕ} (c : Vec 𝕋 n) (G : Fin h → Vec 𝕋 n)
    (l : Fin (a + (a * h + a * h))) (i : Fin n) : -- --- STMT ---
    toReal (ConPolyZono.convHullG a c G l i)
      = Real.ConPolyZono.convHullG a (toRealVec c) (fun l i => toReal (G l i))
        l i := by -- --- PROOF ---
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · simp only [ConPolyZono.convHullG, Real.ConPolyZono.convHullG, Fin.append_left, toRealVec]
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
      simp only [ConPolyZono.convHullG, Real.ConPolyZono.convHullG, Fin.append_left,
        Fin.append_right, repVec]

/-- The stored nominal point at factors whose copies the stored operand's constraints admit and
whose weights add up to `1 - a`. -/
theorem ConPolyZono.aux_convHullSingle_mem (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (v : Fin (a * cPZ.p + a) → ℝ) (hv : ∀ k, |v k| ≤ 1)
    (hcopy : ∀ j, (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) ∈ cPZ.cons.construct)
    (hw : ∑ j, v (Fin.natAdd (a * cPZ.p) j) = 1 - (a : ℝ)) : -- --- STMT ---
    (fun i => toReal ((cPZ.convHullSingle a).c i)
      + ∑ l, toReal ((cPZ.convHullSingle a).G l i)
        * Real.PolyZonotope.monomial (cPZ.convHullSingle a).E v l)
      ∈ nominalSet (cPZ.convHullSingle a) := by -- --- PROOF ---
  refine ConPolyZono.mem_nominalSet_iff.mpr ⟨v, fun j => j.elim0, hv, fun j => j.elim0,
    ConPolyZono.convHullSingle_satisfies_of_real a cPZ v hcopy (fun j => hv _) hw, fun i => ?_⟩
  -- no independent generators
  have h0 : ∀ f : Fin (cPZ.convHullSingle a).qI → ℝ, ∑ j, f j = 0 := fun f =>
    Finset.sum_eq_zero fun j _ => Fin.elim0 (show Fin 0 from j)
  rw [h0, add_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.convHullSingle_outer (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (hq : cPZ.qI = 0)
    (ha : n + 1 ≤ a) :
    convexHull ℝ cPZ.construct ⊆ (cPZ.convHullSingle a).construct := by -- --- PROOF ---
  intro x hx
  -- the hull of the nominal set plus the box is the nominal hull plus the box
  have hx' : x ∈ convexHull ℝ (nominalSet cPZ + cPZ.I_error.construct) := hx
  have hconv : Convex ℝ cPZ.I_error.construct := Real.Interval.convex_construct _
  rw [convexHull_add, hconv.convexHull_eq] at hx'
  obtain ⟨r, hr, e, he, rfl⟩ := hx'
  -- the nominal hull is the exact form on the read-back operand
  have hR := Real.ConPolyZono.convHullSingle_exact a (nominal cPZ) hq
    (by rw [Module.finrank_fin_fun]; exact ha)
  have hr' : r ∈ (Real.ConPolyZono.convHullSingle a (nominal cPZ)).construct := by
    rw [hR]
    exact hr
  obtain ⟨v, β, hβ, hsat, hr⟩ := hr'
  -- the factors lie in the unit box, the constraint's domain
  have hv : ∀ k, |v k| ≤ 1 := (Real.Interval.mem_unit_iff v).mp
    ((Real.ConPolyZono.convHullSingle a (nominal cPZ)).cons_dom ▸ hsat.1)
  -- each copy of the relaxed operand, and the weights
  obtain ⟨hj, -, hl⟩ := (Real.ConPolyZono.mem_convHullSingle_cons_iff a (nominal cPZ) v).mp hsat
  -- the factors with every copy's slack factors dropped
  set w : Fin (a * cPZ.p + a) → ℝ := Fin.append
    (fun x => v (Fin.castAdd a (finProdFinEquiv ((finProdFinEquiv.symm x).1,
      Fin.castAdd cPZ.cons.m (finProdFinEquiv.symm x).2)))) fun j => v (Fin.natAdd _ j) with hwdef
  have hw : ∀ k, |w k| ≤ 1 := Fin.addCases (fun x => by simpa [hwdef] using hv _)
    (fun j => by simpa [hwdef] using hv _)
  -- a copy's slack factor makes up what its row is off by, so the row is within its slack
  have hcopy : ∀ j, (fun k => w (Fin.castAdd a (finProdFinEquiv (j, k)))) ∈ cPZ.cons.construct := by
    intro j
    have hcopyw : (fun k => w (Fin.castAdd a (finProdFinEquiv (j, k))))
        = fun k => v (Fin.castAdd a (finProdFinEquiv (j, Fin.castAdd cPZ.cons.m k))) :=
      funext fun k => by simp only [hwdef, Fin.append_left, Equiv.symm_apply_apply]
    rw [hcopyw]
    refine (PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mpr
      ((Real.PolyLevelSet.exists_relax_iff (P := cPZ.cons.nominalCore) cPZ.cons_eq
        (toRealVec cPZ.cons.b_error) _).mp
          ⟨fun i => v (Fin.castAdd a (finProdFinEquiv (j, Fin.natAdd cPZ.p i))), ?_⟩)
    rw [Fin.append_castAdd_natAdd (f := fun k => v (Fin.castAdd a (finProdFinEquiv (j, k))))]
    exact hj j
  -- the weights are the exact form's own
  have hsum : ∑ j, w (Fin.natAdd (a * cPZ.p) j) = 1 - (a : ℝ) := by
    simpa [hwdef] using hl
  -- no independent generators in the exact form
  have h0 : (∑ j, β j • (Real.ConPolyZono.convHullSingle a (nominal cPZ)).GI j) = 0 :=
    Finset.sum_eq_zero fun j _ => Fin.elim0 (show Fin 0 from j)
  have hrw : r = (a : ℝ) • toRealVec cPZ.c
      + ∑ l, Real.PolyZonotope.monomial (Real.ConPolyZono.convHullE a cPZ.E) w l
        • Real.ConPolyZono.convHullG a (toRealVec cPZ.c) (fun l i => toReal (cPZ.G l i)) l := by
    rw [hr, h0, add_zero]
    refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
    exact congrArg (· • _) (Real.ConPolyZono.monomial_convHullE_padE cPZ.E v l)
  have hz := ConPolyZono.aux_convHullSingle_mem a cPZ w hw hcopy hsum
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
  -- the center `a c` against its stored shortfall
  have hc : (cPZ.convHullSingle a).c i = nsmulDown a (cPZ.c i) := rfl
  rw [hc, hsum]
  simp only [toRealVec] at hri
  linarith [hri]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
