module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactConsEqSpec
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Float.Theorems.Merge
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeFiberUp
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# `compactCons` over-approximates, merging constraint rows

A merged constraint row has no ambient box to reach, so `b` absorbs it:
`abs_sum_le_radius` turns the row of gaps into one bound, the constraint
monomials being in `[-1,1]`, and the bound moves out by it on both sides. The
nominal set only *grows*, and the error box does not move.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A merged constraint column is off by at most the gap between the two
directed masked sums, as a generator column is. -/
theorem ConPolyZono.aux_compactConsGap (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin cPZ.cons.m)
    (l : Fin (PolyZonotope.repKeep cPZ.cons.R).card) : -- --- STMT ---
    |Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.cons.R)
        (fun r => toReal (cPZ.cons.A i r)) (PolyZonotope.keepIdx cPZ.cons.R l)
      - toReal (cPZ.mergedConsCol i l)|
        ≤ toReal (ConPolyZono.compactConsGap cPZ i l) := by -- --- PROOF ---
  have hlo : toReal (cPZ.mergedConsCol i l)
      ≤ Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.cons.R)
          (fun r => toReal (cPZ.cons.A i r)) (PolyZonotope.keepIdx cPZ.cons.R l) :=
    PolyZonotope.fiberDown_le (Real.PolyZonotope.rep cPZ.cons.R) cPZ.cons.A i
        (PolyZonotope.keepIdx cPZ.cons.R l)
  have hhi : Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.cons.R)
        (fun r => toReal (cPZ.cons.A i r)) (PolyZonotope.keepIdx cPZ.cons.R l)
      ≤ toReal (cPZ.mergedConsColUp i l) :=
    PolyZonotope.le_fiberUp (Real.PolyZonotope.rep cPZ.cons.R) cPZ.cons.A i
      (PolyZonotope.keepIdx cPZ.cons.R l)
  have hgap := sub_le_subUp (cPZ.mergedConsColUp i l) (cPZ.mergedConsCol i l)
  rw [abs_le]
  simp only [ConPolyZono.compactConsGap]
  constructor <;> linarith

/-- The widened slack admits every factor vector the old one did: the row moved
by at most one `radius` of its gaps, and the slack grew by exactly that. -/
theorem ConPolyZono.aux_satisfies_compactCons (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) {a : Fin cPZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (hsat : a ∈ cPZ.cons.construct) :
    a ∈ cPZ.compactConsSpec.cons.construct := by -- --- PROOF ---
  -- the kept exponents of the constraints, the monomials on them, and the exact fibre sums
  set Rk : Fin cPZ.p → Fin (PolyZonotope.repKeep cPZ.cons.R).card → ℕ :=
    fun k j' => cPZ.cons.R k (PolyZonotope.keepIdx cPZ.cons.R j') with hRk
  set mon := Real.PolyZonotope.monomial Rk a with hmon
  set fib : Fin cPZ.cons.m → Fin (PolyZonotope.repKeep cPZ.cons.R).card → ℝ := fun i j =>
    Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep cPZ.cons.R) (fun r => toReal (cPZ.cons.A i r))
      (PolyZonotope.keepIdx cPZ.cons.R j) with hfib
  rw [PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq] at hsat
  refine (PolyLevelSet.mem_construct_iff_of_eq cPZ.compactConsSpec.cons_eq).mpr fun i => ?_
  -- the constraint row at `a`, within its slack of `b`
  set row := ∑ l, toReal (cPZ.cons.A i l) * Real.PolyZonotope.monomial cPZ.cons.R a l with hrow
  have hb : |row - toReal (cPZ.cons.b i)| ≤ |toReal (cPZ.cons.b_error i)| := hsat i
  have hex := ConPolyZono.merge cPZ.cons.R cPZ.cons.A a Rk (fun _ _ => rfl) i
  -- the exact merged row is the stored one plus what the gaps carry
  have hsplit : (∑ j, fib i j * mon j) = (∑ j, toReal (cPZ.mergedConsCol i j) * mon j)
        + ∑ j, (fib i j - toReal (cPZ.mergedConsCol i j)) * mon j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- one radius bounds the whole row, every constraint monomial lying in `[-1,1]`
  have hrad : |∑ j, (fib i j - toReal (cPZ.mergedConsCol i j)) * mon j|
      ≤ toReal (radius (ConPolyZono.compactConsGap cPZ) i) :=
    abs_sum_le_radius
      (Δ := fun i j => fib i j - toReal (cPZ.mergedConsCol i j))
      (fun i j => le_trans (ConPolyZono.aux_compactConsGap cPZ i j) (le_abs_self _))
      (fun j => Real.PolyZonotope.abs_monomial_le_one Rk ha j) i
  -- the slack has grown by the very number `hrad` supplies
  have hu := add_le_addUp (absolute (cPZ.cons.b_error i))
    (radius (ConPolyZono.compactConsGap cPZ) i)
  rw [toReal_absolute] at hu
  show |(∑ j, toReal (cPZ.mergedConsCol i j) * mon j) - toReal (cPZ.cons.b i)|
    ≤ |toReal (addUp (absolute (cPZ.cons.b_error i)) (radius (ConPolyZono.compactConsGap cPZ) i))|
  rw [abs_le] at hb hrad ⊢
  have hu' := le_abs_self
    (toReal (addUp (absolute (cPZ.cons.b_error i)) (radius (ConPolyZono.compactConsGap cPZ) i)))
  constructor <;> linarith [hb.1, hb.2, hex, hsplit, hrad.1, hrad.2]

/-- Only the constraint weakens, so the nominal set grows and the error box does
not move. -/
theorem ConPolyZono.aux_compactCons_nominal (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    nominalSet cPZ ⊆ nominalSet cPZ.compactConsSpec := by
  intro x hx
  obtain ⟨a, β, ha, hβ, hsat, hxi⟩ := ConPolyZono.mem_nominalSet_iff.mp hx
  exact ConPolyZono.mem_nominalSet_iff.mpr
    ⟨a, β, ha, hβ, ConPolyZono.aux_satisfies_compactCons cPZ ha hsat, hxi⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactCons_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.compactCons.construct := by
  rw [ConPolyZono.compactCons_eq_spec]
  exact InflatedContSet.mono_subset (ConPolyZono.aux_compactCons_nominal cPZ) (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
