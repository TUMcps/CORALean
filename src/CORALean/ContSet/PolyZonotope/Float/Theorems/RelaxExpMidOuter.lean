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
theorem PolyZonotope.aux_sum_univ_relaxExpMid_h {PZ : PolyZonotope 𝕋 n}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin 2)} {k₀ : Fin PZ.p} (f : Fin (d + 1) → ℝ) :
    ∑ l : Fin (PZ.relaxExpMid part k₀).h, f l
      = ∑ l, f (Fin.castAdd 1 l) + ∑ l : Fin 1, f (Fin.natAdd d l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent count. -/
theorem PolyZonotope.aux_sum_univ_relaxExpMid_q {PZ : PolyZonotope 𝕋 n}
    {part : Split (Fin PZ.h) into (Fin d) and (Fin 2)} {k₀ : Fin PZ.p} (f : Fin (PZ.q + 1) → ℝ) :
    ∑ j : Fin (PZ.relaxExpMid part k₀).q, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j : Fin 1, f (Fin.natAdd PZ.q j) :=
  Fin.sum_univ_add f

/-- The halved column is stored downward and its upward twin lies above the
exact half-width, so the gap between them covers it. -/
theorem PolyZonotope.aux_relaxGenMid_gap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) (i : Fin n) :
    |(((PZ.relaxDrift part k₀).1 : ℝ) / 2 + ((PZ.relaxDrift part k₀).2 : ℝ) / 2)
        * toReal (PZ.G i (part.right 0)) - toReal (PZ.relaxGenMid part k₀ i)|
      ≤ toReal (PZ.relaxGapMid part k₀ i 1) := by
  -- the fold counts both reaches, so its bound casts to their sum
  have hcast : (((PZ.relaxDrift part k₀).1 + (PZ.relaxDrift part k₀).2 : ℕ) : ℝ)
      = ((PZ.relaxDrift part k₀).1 : ℝ) + ((PZ.relaxDrift part k₀).2 : ℝ) := Nat.cast_add _ _
  have hlo : toReal (PZ.relaxGenMid part k₀ i)
      ≤ (((PZ.relaxDrift part k₀).1 : ℝ) / 2 + ((PZ.relaxDrift part k₀).2 : ℝ) / 2)
        * toReal (PZ.G i (part.right 0)) := by
    rw [PolyZonotope.relaxGenMid, toReal_half]
    have h := nsmulDown_le ((PZ.relaxDrift part k₀).1 + (PZ.relaxDrift part k₀).2)
      (PZ.G i (part.right 0))
    rw [hcast] at h
    linarith
  -- the same fold upward, which the stored column's gap is measured against
  have hhi : (((PZ.relaxDrift part k₀).1 : ℝ) / 2 + ((PZ.relaxDrift part k₀).2 : ℝ) / 2)
      * toReal (PZ.G i (part.right 0)) ≤ toReal (PZ.relaxGenMidUp part k₀ i) := by
    rw [PolyZonotope.relaxGenMidUp, toReal_half]
    have h := le_nsmulUp ((PZ.relaxDrift part k₀).1 + (PZ.relaxDrift part k₀).2)
      (PZ.G i (part.right 0))
    rw [hcast] at h
    linarith
  have hgap : toReal (PZ.relaxGenMidUp part k₀ i) - toReal (PZ.relaxGenMid part k₀ i)
      ≤ toReal (PZ.relaxGapMid part k₀ i 1) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

/-- The shift is stored below the exact midpoint and its upward twin above it,
so the centre stored downward stays below the exact one and the gap covers it. -/
theorem PolyZonotope.aux_relaxCentreMid_gap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) (i : Fin n) :
    |toReal (PZ.c i)
        + (((PZ.relaxDrift part k₀).2 : ℝ) / 2 - ((PZ.relaxDrift part k₀).1 : ℝ) / 2)
          * toReal (PZ.G i (part.right 0)) - toReal (PZ.relaxCentreMid part k₀ i)|
      ≤ toReal (PZ.relaxGapMid part k₀ i 2) := by
  -- the shift is stored below the exact midpoint
  have hshiftlo : toReal (PZ.relaxShiftMid part k₀ i)
      ≤ (((PZ.relaxDrift part k₀).2 : ℝ) / 2 - ((PZ.relaxDrift part k₀).1 : ℝ) / 2)
        * toReal (PZ.G i (part.right 0)) := by
    rw [PolyZonotope.relaxShiftMid, toReal_half]
    have h1 := subDown_le_sub (nsmulDown (PZ.relaxDrift part k₀).2 (PZ.G i (part.right 0)))
      (nsmulUp (PZ.relaxDrift part k₀).1 (PZ.G i (part.right 0)))
    have h2 := nsmulDown_le (PZ.relaxDrift part k₀).2 (PZ.G i (part.right 0))
    have h3 := le_nsmulUp (PZ.relaxDrift part k₀).1 (PZ.G i (part.right 0))
    linarith
  -- and above it at the rounding that takes each fold the other way
  have hshifthi : (((PZ.relaxDrift part k₀).2 : ℝ) / 2 - ((PZ.relaxDrift part k₀).1 : ℝ) / 2)
      * toReal (PZ.G i (part.right 0)) ≤ toReal (PZ.relaxShiftMidUp part k₀ i) := by
    rw [PolyZonotope.relaxShiftMidUp, toReal_half]
    have h1 := sub_le_subUp (nsmulUp (PZ.relaxDrift part k₀).2 (PZ.G i (part.right 0)))
      (nsmulDown (PZ.relaxDrift part k₀).1 (PZ.G i (part.right 0)))
    have h2 := le_nsmulUp (PZ.relaxDrift part k₀).2 (PZ.G i (part.right 0))
    have h3 := nsmulDown_le (PZ.relaxDrift part k₀).1 (PZ.G i (part.right 0))
    linarith
  -- the stored centre is the shift added downward, so it stays below the exact one
  have hstore : toReal (PZ.relaxCentreMid part k₀ i)
      ≤ toReal (PZ.c i) + toReal (PZ.relaxShiftMid part k₀ i) := addDown_le_add _ _
  have hup : toReal (PZ.c i) + toReal (PZ.relaxShiftMidUp part k₀ i)
      ≤ toReal (addUp (PZ.c i) (PZ.relaxShiftMidUp part k₀ i)) := add_le_addUp _ _
  have hgap : toReal (addUp (PZ.c i) (PZ.relaxShiftMidUp part k₀ i))
      - toReal (PZ.relaxCentreMid part k₀ i)
      ≤ toReal (PZ.relaxGapMid part k₀ i 2) := sub_le_subUp _ _
  rw [abs_le]
  constructor <;> linarith

-- the three stored quantities and their three gaps, the drift split in two
theorem PolyZonotope.aux_relaxExpMid_nominal (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p)
    (hsim : ∀ k, k ≠ k₀ → PZ.E k (part.right 0) = PZ.E k (part.right 1)) :
    nominalSet PZ ⊆ nominalSet (PZ.relaxExpMid part k₀)
      + (PolyZonotope.generatorError (PZ.relaxGapMid part k₀)).construct := by
  intro x hx
  obtain ⟨a, β, ha, hβ, hxi⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  obtain ⟨hdlo, hdhi⟩ := Set.mem_Icc.mp
    (Real.PolyZonotope.sub_monomial_mem_eDrift (k₀ := k₀) PZ.E ha hsim)
  have hlo : -((PZ.relaxDrift part k₀).1 : ℝ)
      ≤ Real.PolyZonotope.monomial PZ.E a (part.right 0)
        - Real.PolyZonotope.monomial PZ.E a (part.right 1) := hdlo
  have hhi : Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1)
      ≤ ((PZ.relaxDrift part k₀).2 : ℝ) := hdhi
  have hfst : (0:ℝ) ≤ ((PZ.relaxDrift part k₀).1 : ℝ) := Nat.cast_nonneg _
  have hsnd : (0:ℝ) ≤ ((PZ.relaxDrift part k₀).2 : ℝ) := Nat.cast_nonneg _
  have hnn : (0:ℝ) ≤ ((PZ.relaxDrift part k₀).1 : ℝ) / 2
      + ((PZ.relaxDrift part k₀).2 : ℝ) / 2 := by linarith
  -- the bracket read as a midpoint and a half-width
  have hmid : |Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1)
      - (((PZ.relaxDrift part k₀).2 : ℝ) / 2 - ((PZ.relaxDrift part k₀).1 : ℝ) / 2)|
        ≤ ((PZ.relaxDrift part k₀).1 : ℝ) / 2 + ((PZ.relaxDrift part k₀).2 : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  set t := Real.Zonotope.coefficient
    (((PZ.relaxDrift part k₀).1 : ℝ) / 2 + ((PZ.relaxDrift part k₀).2 : ℝ) / 2)
    (Real.PolyZonotope.monomial PZ.E a (part.right 0)
      - Real.PolyZonotope.monomial PZ.E a (part.right 1)
      - (((PZ.relaxDrift part k₀).2 : ℝ) / 2 - ((PZ.relaxDrift part k₀).1 : ℝ) / 2)) with ht
  have hcoef : (((PZ.relaxDrift part k₀).1 : ℝ) / 2 + ((PZ.relaxDrift part k₀).2 : ℝ) / 2) * t
      = Real.PolyZonotope.monomial PZ.E a (part.right 0)
        - Real.PolyZonotope.monomial PZ.E a (part.right 1)
        - (((PZ.relaxDrift part k₀).2 : ℝ) / 2 - ((PZ.relaxDrift part k₀).1 : ℝ) / 2) := by
    rw [ht]
    exact Real.Zonotope.mul_coefficient hmid
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d,
      Real.PolyZonotope.monomial (PZ.relaxExpMid part k₀).E a (Fin.castAdd 1 l)
        = Real.PolyZonotope.monomial PZ.E a (part.left l) := fun l => by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpMid, Fin.append_left]
    rfl
  have hlast : Real.PolyZonotope.monomial (PZ.relaxExpMid part k₀).E a (Fin.natAdd d 0)
      = Real.PolyZonotope.monomial PZ.E a (part.right 1) := by
    simp only [Real.PolyZonotope.monomial, PolyZonotope.relaxExpMid, Fin.append_right]
    rfl
  -- the point at the stored fields, and what the three gaps still owe it
  refine ⟨fun i => toReal (PZ.relaxCentreMid part k₀ i)
      + (∑ l : Fin d, toReal (PZ.G i (part.left l))
            * Real.PolyZonotope.monomial PZ.E a (part.left l)
          + toReal (PZ.mergedGen part i) * Real.PolyZonotope.monomial PZ.E a (part.right 1))
      + (∑ j, toReal (PZ.GI i j) * β j + toReal (PZ.relaxGenMid part k₀ i) * t),
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩,
    _, PolyZonotope.mem_generatorError (G := PZ.relaxGapMid part k₀)
      (Δ := fun i => ![toReal (PZ.G i (part.right 1)) + toReal (PZ.G i (part.right 0))
          - toReal (PZ.mergedGen part i),
        (((PZ.relaxDrift part k₀).1 : ℝ) / 2 + ((PZ.relaxDrift part k₀).2 : ℝ) / 2)
          * toReal (PZ.G i (part.right 0)) - toReal (PZ.relaxGenMid part k₀ i),
        toReal (PZ.c i)
          + (((PZ.relaxDrift part k₀).2 : ℝ) / 2 - ((PZ.relaxDrift part k₀).1 : ℝ) / 2)
            * toReal (PZ.G i (part.right 0)) - toReal (PZ.relaxCentreMid part k₀ i)])
      (t := ![Real.PolyZonotope.monomial PZ.E a (part.right 1), t, 1]) ?_ ?_, ?_⟩
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
    · exact PolyZonotope.mergedGen_gap PZ part i
    · exact PolyZonotope.aux_relaxGenMid_gap PZ part k₀ i
    · rw [Subsingleton.elim l'' 0]
      exact PolyZonotope.aux_relaxCentreMid_gap PZ part k₀ i
  · refine Fin.cases ?_ (fun l' => Fin.cases ?_ (fun l'' => ?_) l')
    · exact Real.PolyZonotope.abs_monomial_le_one PZ.E ha _
    · rw [ht]
      exact Real.Zonotope.abs_coefficient_le_one hnn hmid
    · rw [Subsingleton.elim l'' 0]
      exact le_of_eq abs_one
  -- the three gaps and the split drift recombine into the exact sums
  · funext i
    show toReal (PZ.relaxCentreMid part k₀ i)
          + (∑ l : Fin d, toReal (PZ.G i (part.left l))
              * Real.PolyZonotope.monomial PZ.E a (part.left l)
            + toReal (PZ.mergedGen part i) * Real.PolyZonotope.monomial PZ.E a (part.right 1))
          + (∑ j, toReal (PZ.GI i j) * β j + toReal (PZ.relaxGenMid part k₀ i) * t)
        + ∑ l, _ * _ = x i
    rw [hxi i, Fin.sum_univ_three,
      part.sum_split₂ fun l => toReal (PZ.G i l) * Real.PolyZonotope.monomial PZ.E a l,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination toReal (PZ.G i (part.right 0)) * hcoef


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging two generators whose exponent columns agree off `k₀`
over-approximates, with the drift's midpoint moved into the centre. -/
theorem PolyZonotope.relaxExpMid_outer (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p)
    (hsim : ∀ k, k ≠ k₀ → PZ.E k (part.right 0) = PZ.E k (part.right 1)) :
    PZ.construct ⊆ (PZ.relaxExpMid part k₀).construct := by
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨z', hz', g, hg, hsum⟩ := PolyZonotope.aux_relaxExpMid_nominal PZ part k₀ hsim hz
  refine ⟨z', hz', e + g, Interval.plus_outer _ _ ⟨e, he, g, hg, rfl⟩, ?_⟩
  -- `Set.image2` leaves the sum a beta-redex, which `rw` will not match
  have hsum' : z' + g = z := hsum
  show z' + (e + g) = z + e
  rw [← hsum', add_comm e g, ← add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
