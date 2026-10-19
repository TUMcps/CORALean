module

public import CORALean.ContSet.PolyLevelSet.Float.Theorems.CompactEqSpec
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeFiberUp
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SumToRealMerge
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

@[expose] public section

/-!
# `PolyLevelSet.compact` over-approximates on the unit box

A merged row moves by what its merged coefficients are off by, so the slack absorbs it:
`abs_sum_le_radius` turns the row of gaps into one bound, every monomial being in `[-1,1]` on the
unit box, and the slack grows by it (`compactSlack`). So every point of the box the rows admitted
they still admit.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A merged coefficient column is off by at most the gap between the two directed masked sums. -/
theorem PolyLevelSet.aux_compactGap (P : PolyLevelSet 𝕋 n) (i : Fin P.m)
    (l : Fin (PolyZonotope.repKeep P.R).card) : -- --- STMT ---
    |Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep P.R)
        (fun r => toReal (P.A i r)) (PolyZonotope.keepIdx P.R l)
      - toReal (P.mergedCol i l)|
        ≤ toReal (P.compactGap i l) := by -- --- PROOF ---
  have hlo : toReal (P.mergedCol i l)
      ≤ Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep P.R)
          (fun r => toReal (P.A i r)) (PolyZonotope.keepIdx P.R l) :=
    PolyZonotope.fiberDown_le (Real.PolyZonotope.rep P.R) P.A i (PolyZonotope.keepIdx P.R l)
  have hhi : Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep P.R)
        (fun r => toReal (P.A i r)) (PolyZonotope.keepIdx P.R l)
      ≤ toReal (P.mergedColUp i l) :=
    PolyZonotope.le_fiberUp (Real.PolyZonotope.rep P.R) P.A i (PolyZonotope.keepIdx P.R l)
  have hgap := sub_le_subUp (P.mergedColUp i l) (P.mergedCol i l)
  rw [abs_le]
  simp only [PolyLevelSet.compactGap]
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The widened slack admits every point of the unit box the old one did: the row moved by at
most one `radius` of its gaps, and the slack grew by exactly that. -/
theorem PolyLevelSet.mem_compact_of_mem (P : PolyLevelSet 𝕋 n) (hP : ∀ i, P.op i = .eq)
    {a : Fin n → ℝ} (ha : ∀ k, |a k| ≤ 1) (hsat : a ∈ P.construct) :
    a ∈ P.compact.construct := by -- --- PROOF ---
  rw [PolyLevelSet.compact_eq_spec]
  -- the kept exponents, the monomials on them, and the exact fibre sums
  set Rk : Fin n → Fin (PolyZonotope.repKeep P.R).card → ℕ :=
    fun k j' => P.R k (PolyZonotope.keepIdx P.R j') with hRk
  set mon := Real.PolyZonotope.monomial Rk a with hmon
  set fib : Fin P.m → Fin (PolyZonotope.repKeep P.R).card → ℝ := fun i j =>
    Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep P.R) (fun r => toReal (P.A i r))
      (PolyZonotope.keepIdx P.R j) with hfib
  rw [PolyLevelSet.mem_construct_iff_of_eq hP] at hsat
  refine (PolyLevelSet.mem_construct_iff_of_eq (P := P.compactSpec) hP).mpr fun i => ?_
  -- the row at `a`, within its slack of `b`
  set row := ∑ l, toReal (P.A i l) * Real.PolyZonotope.monomial P.R a l with hrow
  have hb : |row - toReal (P.b i)| ≤ |toReal (P.b_error i)| := hsat i
  have hex := PolyZonotope.sum_toReal_merge P.R P.A a Rk (fun _ _ => rfl) i
  -- the exact merged row is the stored one plus what the gaps carry
  have hsplit : (∑ j, fib i j * mon j) = (∑ j, toReal (P.mergedCol i j) * mon j)
        + ∑ j, (fib i j - toReal (P.mergedCol i j)) * mon j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- one radius bounds the whole row, every monomial lying in `[-1,1]`
  have hrad : |∑ j, (fib i j - toReal (P.mergedCol i j)) * mon j|
      ≤ toReal (radius P.compactGap i) :=
    abs_sum_le_radius
      (Δ := fun i j => fib i j - toReal (P.mergedCol i j))
      (fun i j => le_trans (PolyLevelSet.aux_compactGap P i j) (le_abs_self _))
      (fun j => Real.PolyZonotope.abs_monomial_le_one Rk ha j) i
  -- the slack has grown by the very number `hrad` supplies
  have hu := add_le_addUp (absolute (P.b_error i)) (radius P.compactGap i)
  rw [toReal_absolute] at hu
  show |(∑ j, toReal (P.mergedCol i j) * mon j) - toReal (P.b i)|
    ≤ |toReal (addUp (absolute (P.b_error i)) (radius P.compactGap i))|
  rw [abs_le] at hb hrad ⊢
  have hu' := le_abs_self (toReal (addUp (absolute (P.b_error i)) (radius P.compactGap i)))
  constructor <;> linarith [hb.1, hb.2, hex, hsplit, hrad.1, hrad.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
