import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMid
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.MergedGenGap
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialMemEDrift
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient

/-!
# The recentred relaxation over-approximates at any parity, at the stored fields

The exact layer's argument at this layer's stored fields.
`sub_monomial_mem_eDrift` is the exact layer's and is what brackets the drift;
both ends of that bracket are natural numbers the two layers read off the same
exponent matrix, so the midpoint and the half-width are the same halves here as
there.

Three gaps, as in the all-even case, and the centre's is the one that changes.
The shift has no sign to case on, being a difference of two folds, so it is
stored at its lower rounding and added downward; the gap up to the same sum
taken at the shift's upper rounding then covers the centre whichever way the
shift went.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `relaxExpMid`'s dependent count, stated through the
projection because that is the form the goal has. -/
theorem PolyZonotope.aux_sum_univ_relaxExpMid_h {pZ : PolyZonotope 𝕋 n}
    {part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)} {k₀ : Fin pZ.p} (f : Fin (d + 1) → ℝ) :
    ∑ l : Fin (pZ.relaxExpMid part k₀).h, f l
      = ∑ l, f (Fin.castAdd 1 l) + ∑ l : Fin 1, f (Fin.natAdd d l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent count. -/
theorem PolyZonotope.aux_sum_univ_relaxExpMid_q {pZ : PolyZonotope 𝕋 n}
    {part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)} {k₀ : Fin pZ.p} (f : Fin (pZ.q + 1) → ℝ) :
    ∑ j : Fin (pZ.relaxExpMid part k₀).q, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j : Fin 1, f (Fin.natAdd pZ.q j) :=
  Fin.sum_univ_add f

/-- The halved column is stored downward and its upward twin lies above the
exact half-width, so the gap between them covers it. -/
theorem PolyZonotope.aux_relaxGenMid_gap (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) (i : Fin n) :
    |(((pZ.relaxDrift part k₀).1 : ℝ) / 2 + ((pZ.relaxDrift part k₀).2 : ℝ) / 2)
        * toReal (pZ.G (part.right 0) i) - toReal (pZ.relaxGenMid part k₀ i)|
      ≤ toReal (pZ.relaxGapMid part k₀ i 1) := by -- --- PROOF ---
  -- the fold counts both reaches, so its bound casts to their sum
  have hcast : (((pZ.relaxDrift part k₀).1 + (pZ.relaxDrift part k₀).2 : ℕ) : ℝ)
      = ((pZ.relaxDrift part k₀).1 : ℝ) + ((pZ.relaxDrift part k₀).2 : ℝ) := Nat.cast_add _ _
  have hlo : toReal (pZ.relaxGenMid part k₀ i)
      ≤ (((pZ.relaxDrift part k₀).1 : ℝ) / 2 + ((pZ.relaxDrift part k₀).2 : ℝ) / 2)
        * toReal (pZ.G (part.right 0) i) := by
    rw [PolyZonotope.relaxGenMid, toReal_half]
    have h := nsmulDown_le ((pZ.relaxDrift part k₀).1 + (pZ.relaxDrift part k₀).2)
      (pZ.G (part.right 0) i)
    rw [hcast] at h
    linarith
  -- the same fold upward, which the stored column's gap is measured against
  have hhi : (((pZ.relaxDrift part k₀).1 : ℝ) / 2 + ((pZ.relaxDrift part k₀).2 : ℝ) / 2)
      * toReal (pZ.G (part.right 0) i) ≤ toReal (pZ.relaxGenMidUp part k₀ i) := by
    rw [PolyZonotope.relaxGenMidUp, toReal_half]
    have h := le_nsmulUp ((pZ.relaxDrift part k₀).1 + (pZ.relaxDrift part k₀).2)
      (pZ.G (part.right 0) i)
    rw [hcast] at h
    linarith
  have hgap : toReal (pZ.relaxGenMidUp part k₀ i) - toReal (pZ.relaxGenMid part k₀ i)
      ≤ toReal (pZ.relaxGapMid part k₀ i 1) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

/-- The shift is stored below the exact midpoint and its upward twin above it,
so the centre stored downward stays below the exact one and the gap covers it. -/
theorem PolyZonotope.aux_relaxCentreMid_gap (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) (i : Fin n) :
    |toReal (pZ.c i)
        + (((pZ.relaxDrift part k₀).2 : ℝ) / 2 - ((pZ.relaxDrift part k₀).1 : ℝ) / 2)
          * toReal (pZ.G (part.right 0) i) - toReal (pZ.relaxCentreMid part k₀ i)|
      ≤ toReal (pZ.relaxGapMid part k₀ i 2) := by -- --- PROOF ---
  -- the shift is stored below the exact midpoint
  have hshiftlo : toReal (pZ.relaxShiftMid part k₀ i)
      ≤ (((pZ.relaxDrift part k₀).2 : ℝ) / 2 - ((pZ.relaxDrift part k₀).1 : ℝ) / 2)
        * toReal (pZ.G (part.right 0) i) := by
    rw [PolyZonotope.relaxShiftMid, toReal_half]
    have h1 := subDown_le_sub (nsmulDown (pZ.relaxDrift part k₀).2 (pZ.G (part.right 0) i))
      (nsmulUp (pZ.relaxDrift part k₀).1 (pZ.G (part.right 0) i))
    have h2 := nsmulDown_le (pZ.relaxDrift part k₀).2 (pZ.G (part.right 0) i)
    have h3 := le_nsmulUp (pZ.relaxDrift part k₀).1 (pZ.G (part.right 0) i)
    linarith
  -- and above it at the rounding that takes each fold the other way
  have hshifthi : (((pZ.relaxDrift part k₀).2 : ℝ) / 2 - ((pZ.relaxDrift part k₀).1 : ℝ) / 2)
      * toReal (pZ.G (part.right 0) i) ≤ toReal (pZ.relaxShiftMidUp part k₀ i) := by
    rw [PolyZonotope.relaxShiftMidUp, toReal_half]
    have h1 := sub_le_subUp (nsmulUp (pZ.relaxDrift part k₀).2 (pZ.G (part.right 0) i))
      (nsmulDown (pZ.relaxDrift part k₀).1 (pZ.G (part.right 0) i))
    have h2 := le_nsmulUp (pZ.relaxDrift part k₀).2 (pZ.G (part.right 0) i)
    have h3 := nsmulDown_le (pZ.relaxDrift part k₀).1 (pZ.G (part.right 0) i)
    linarith
  -- the stored centre is the shift added downward, so it stays below the exact one
  have hstore : toReal (pZ.relaxCentreMid part k₀ i)
      ≤ toReal (pZ.c i) + toReal (pZ.relaxShiftMid part k₀ i) := addDown_le_add _ _
  have hup : toReal (pZ.c i) + toReal (pZ.relaxShiftMidUp part k₀ i)
      ≤ toReal (addUp (pZ.c i) (pZ.relaxShiftMidUp part k₀ i)) := add_le_addUp _ _
  have hgap : toReal (addUp (pZ.c i) (pZ.relaxShiftMidUp part k₀ i))
      - toReal (pZ.relaxCentreMid part k₀ i)
      ≤ toReal (pZ.relaxGapMid part k₀ i 2) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

-- the three stored quantities and their three gaps, the drift split in two
theorem PolyZonotope.aux_relaxExpMid_nominal (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p)
    (hsim : ∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1)) :
    nominalSet pZ ⊆ nominalSet (pZ.relaxExpMid part k₀)
      + (PolyZonotope.generatorError (pZ.relaxGapMid part k₀)).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  obtain ⟨hdlo, hdhi⟩ := Set.mem_Icc.mp
    (Real.PolyZonotope.sub_monomial_mem_eDrift (k₀ := k₀) pZ.E ha hsim)
  have hlo : -((pZ.relaxDrift part k₀).1 : ℝ)
      ≤ Real.PolyZonotope.monomial pZ.E a (part.right 0)
        - Real.PolyZonotope.monomial pZ.E a (part.right 1) := hdlo
  have hhi : Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)
      ≤ ((pZ.relaxDrift part k₀).2 : ℝ) := hdhi
  have hfst : (0:ℝ) ≤ ((pZ.relaxDrift part k₀).1 : ℝ) := Nat.cast_nonneg _
  have hsnd : (0:ℝ) ≤ ((pZ.relaxDrift part k₀).2 : ℝ) := Nat.cast_nonneg _
  have hnn : (0:ℝ) ≤ ((pZ.relaxDrift part k₀).1 : ℝ) / 2
      + ((pZ.relaxDrift part k₀).2 : ℝ) / 2 := by linarith
  -- the bracket read as a midpoint and a half-width
  have hmid : |Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)
      - (((pZ.relaxDrift part k₀).2 : ℝ) / 2 - ((pZ.relaxDrift part k₀).1 : ℝ) / 2)|
        ≤ ((pZ.relaxDrift part k₀).1 : ℝ) / 2 + ((pZ.relaxDrift part k₀).2 : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  set t := Real.Zonotope.coefficient
    (((pZ.relaxDrift part k₀).1 : ℝ) / 2 + ((pZ.relaxDrift part k₀).2 : ℝ) / 2)
    (Real.PolyZonotope.monomial pZ.E a (part.right 0)
      - Real.PolyZonotope.monomial pZ.E a (part.right 1)
      - (((pZ.relaxDrift part k₀).2 : ℝ) / 2 - ((pZ.relaxDrift part k₀).1 : ℝ) / 2)) with ht
  have hcoef : (((pZ.relaxDrift part k₀).1 : ℝ) / 2 + ((pZ.relaxDrift part k₀).2 : ℝ) / 2) * t
      = Real.PolyZonotope.monomial pZ.E a (part.right 0)
        - Real.PolyZonotope.monomial pZ.E a (part.right 1)
        - (((pZ.relaxDrift part k₀).2 : ℝ) / 2 - ((pZ.relaxDrift part k₀).1 : ℝ) / 2) := by
    rw [ht]
    exact Real.Zonotope.mul_coefficient hmid
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d,
      Real.PolyZonotope.monomial (pZ.relaxExpMid part k₀).E a (Fin.castAdd 1 l)
        = Real.PolyZonotope.monomial pZ.E a (part.left l) := fun l => by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpMid, Fin.append_left]
    rfl
  have hlast : Real.PolyZonotope.monomial (pZ.relaxExpMid part k₀).E a (Fin.natAdd d 0)
      = Real.PolyZonotope.monomial pZ.E a (part.right 1) := by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpMid, Fin.append_right]
    rfl
  -- the point at the stored fields, and what the three gaps still owe it
  refine ⟨fun i => toReal (pZ.relaxCentreMid part k₀ i)
      + (∑ l : Fin d, toReal (pZ.G (part.left l) i)
            * Real.PolyZonotope.monomial pZ.E a (part.left l)
          + toReal (pZ.mergedGen part i) * Real.PolyZonotope.monomial pZ.E a (part.right 1))
      + (∑ j, toReal (pZ.GI j i) * β j + toReal (pZ.relaxGenMid part k₀ i) * t),
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩,
    _, PolyZonotope.mem_generatorError (G := pZ.relaxGapMid part k₀)
      (Δ := fun i => ![toReal (pZ.G (part.right 1) i) + toReal (pZ.G (part.right 0) i)
          - toReal (pZ.mergedGen part i),
        (((pZ.relaxDrift part k₀).1 : ℝ) / 2 + ((pZ.relaxDrift part k₀).2 : ℝ) / 2)
          * toReal (pZ.G (part.right 0) i) - toReal (pZ.relaxGenMid part k₀ i),
        toReal (pZ.c i)
          + (((pZ.relaxDrift part k₀).2 : ℝ) / 2 - ((pZ.relaxDrift part k₀).1 : ℝ) / 2)
            * toReal (pZ.G (part.right 0) i) - toReal (pZ.relaxCentreMid part k₀ i)])
      (t := ![Real.PolyZonotope.monomial pZ.E a (part.right 1), t, 1]) ?_ ?_, ?_⟩
  -- the fresh independent coefficient is what the half-width asks of the column
  · refine Fin.addCases (fun j => ?_) fun _ => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right, ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn hmid
  · intro i
    rw [PolyZonotope.aux_sum_univ_relaxExpMid_h, PolyZonotope.aux_sum_univ_relaxExpMid_q]
    simp only [Fin.sum_univ_one, hmono, hlast]
    simp only [PolyZonotope.relaxExpMid, Fin.append_left, Fin.append_right]
  · refine fun i l => Fin.cases ?_ (fun l' => Fin.cases ?_ (fun l'' => ?_) l') l
    · exact PolyZonotope.mergedGen_gap pZ part i
    · exact PolyZonotope.aux_relaxGenMid_gap pZ part k₀ i
    · rw [Subsingleton.elim l'' 0]
      exact PolyZonotope.aux_relaxCentreMid_gap pZ part k₀ i
  · refine Fin.cases ?_ (fun l' => Fin.cases ?_ (fun l'' => ?_) l')
    · exact Real.PolyZonotope.abs_monomial_le_one pZ.E ha _
    · rw [ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn hmid
    · rw [Subsingleton.elim l'' 0]
      exact le_of_eq abs_one
  -- the three gaps and the split drift recombine into the exact sums
  · funext i
    show toReal (pZ.relaxCentreMid part k₀ i)
          + (∑ l : Fin d, toReal (pZ.G (part.left l) i)
              * Real.PolyZonotope.monomial pZ.E a (part.left l)
            + toReal (pZ.mergedGen part i) * Real.PolyZonotope.monomial pZ.E a (part.right 1))
          + (∑ j, toReal (pZ.GI j i) * β j + toReal (pZ.relaxGenMid part k₀ i) * t)
        + ∑ l, _ * _ = x i
    rw [hxi i, Fin.sum_univ_three,
      part.sum_split₂ fun l => toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination toReal (pZ.G (part.right 0) i) * hcoef


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging two generators whose exponent columns agree off `k₀`
over-approximates, with the drift's midpoint moved into the centre. -/
theorem PolyZonotope.relaxExpMid_outer (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p)
    (hsim : ∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1)) :
    pZ.construct ⊆ (pZ.relaxExpMid part k₀).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', g, hg, hsum⟩ := PolyZonotope.aux_relaxExpMid_nominal pZ part k₀ hsim hz
  refine ⟨z', hz', e + g, Interval.plus_outer _ _ ⟨e, he, g, hg, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + g = z := hsum
  show z' + (e + g) = z + e
  rw [← hsum', add_comm e g, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
