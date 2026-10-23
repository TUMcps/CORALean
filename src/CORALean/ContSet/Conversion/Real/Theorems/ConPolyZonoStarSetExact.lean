module

public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_StarSet
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Instances
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEqUnit
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.StarSet.Real.Instances
public import Mathlib.Algebra.Order.Ring.Abs
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemPadVarsIff

@[expose] public section

/-!
# A constrained polynomial zonotope is exactly its star set

The predicate's box and its two systems say what the coefficients `(α, β, z)` are: in the cube;
the constraint at `α`; and `z = μ_E(α)`, which lies in the cube with `α`. With `z` the monomials
the star set's linear point `c + Σ GIⱼ βⱼ + Σ Gₗ zₗ` is the constrained polynomial zonotope's at
`(α, β)`, so the two denote one set. The converse, a star set with a polynomial level set as its
predicate as a constrained polynomial zonotope, is no construction here: its rows may be `≤`.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* star set equals the constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The constraint rows say the constraint of the factors, the other two blocks in the unit box. -/
theorem ConPolyZono.aux_mem_starConsRows (cPZ : ConPolyZono (Vec ℝ n))
    (ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h)) : -- --- CONCL ---
    ζ ∈ cPZ.starConsRows.construct
      ↔ ((fun k => ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k))) ∈ cPZ.cons.construct
        ∧ (fun j => ζ (Fin.castAdd cPZ.h (Fin.natAdd cPZ.p j))) ∈ (Interval.unit cPZ.qI).construct)
        ∧ (fun l => ζ (Fin.natAdd (cPZ.p + cPZ.qI) l))
          ∈ (Interval.unit cPZ.h).construct := by -- --- PROOF ---
  exact (PolyLevelSet.mem_padVars_iff _ _ ζ).trans
    (and_congr_left' (PolyLevelSet.mem_padVars_iff _ _ _))

/-- The generator rows say each `z` is its generator's monomial at the factors, on the unit box. -/
theorem ConPolyZono.aux_mem_starGenRows (cPZ : ConPolyZono (Vec ℝ n))
    (ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h)) : -- --- CONCL ---
    ζ ∈ cPZ.starGenRows.construct ↔ ζ ∈ (Interval.unit _).construct
      ∧ ∀ l, ζ (Fin.natAdd (cPZ.p + cPZ.qI) l)
      = PolyZonotope.monomial cPZ.E (fun k => ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k)))
        l := by -- --- PROOF ---
  have hrow : ∀ l : Fin cPZ.h,
      (cPZ.starGenRows.A *ᵥ PolyZonotope.monomial cPZ.starGenRows.R ζ) l
      = ζ (Fin.natAdd (cPZ.p + cPZ.qI) l)
        - PolyZonotope.monomial cPZ.E
          (fun k => ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k))) l := by
    intro l
    show ∑ j : Fin (cPZ.h + cPZ.h), Fin.append (fun l' => if l' = l then (-1 : ℝ) else 0)
      (fun l' => if l' = l then 1 else 0) j * PolyZonotope.monomial (PolyZonotope.plusE
        (ConPolyZono.padE cPZ.E cPZ.qI) (PolyZonotope.identE cPZ.h)) ζ j = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, PolyZonotope.monomial_identE,
      ConPolyZono.monomial_padE, ite_mul, neg_one_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  show (_ ∧ ∀ l, CompOp.holds .eq ((cPZ.starGenRows.A *ᵥ PolyZonotope.monomial
    cPZ.starGenRows.R ζ - cPZ.starGenRows.b) l)) ↔ _
  refine and_congr Iff.rfl (forall_congr' fun l => ?_)
  rw [Pi.sub_apply, hrow l]
  simp only [CompOp.holds, ConPolyZono.starGenRows, sub_zero, sub_eq_zero]

/-- The star set's point at `(α, β, z)`, one coordinate: the generators on `z`, the independent
ones on `β`. -/
theorem ConPolyZono.aux_starSet_point (cPZ : ConPolyZono (Vec ℝ n))
    (ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h)) (i : Fin n) : -- --- CONCL ---
    ∑ k, cPZ.starSet.G i k * ζ k
      = (∑ l, cPZ.G l i * ζ (Fin.natAdd (cPZ.p + cPZ.qI) l))
        + ∑ j, cPZ.GI j i * ζ (Fin.castAdd cPZ.h (Fin.natAdd cPZ.p j)) := by -- --- PROOF ---
  show ∑ k : Fin (cPZ.p + cPZ.qI + cPZ.h), Fin.append (Fin.append (fun _ => (0 : ℝ))
    fun j => cPZ.GI j i) (fun l => cPZ.G l i) k * ζ k = _
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, zero_add]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The star set with the polynomial level set predicate denotes the constrained polynomial
zonotope. -/
theorem ConPolyZono.starSet_exact (cPZ : ConPolyZono (Vec ℝ n)) : -- --- CONCL ---
    cPZ.starSet.construct = cPZ.construct := by -- --- PROOF ---
  ext x
  rw [ConPolyZono.mem_construct_iff]
  show (∃ ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h),
    (ζ ∈ (Interval.unit _).construct ∧ ζ ∈ (cPZ.starConsRows.and_ cPZ.starGenRows).construct)
    ∧ ∀ i, x i = cPZ.c i + ∑ k, cPZ.starSet.G i k * ζ k) ↔ _
  constructor
  -- the factors and the independent coefficients, read off the coefficients
  · rintro ⟨ζ, ⟨-, hζ⟩, hx⟩
    rw [PolyLevelSet.and_exact] at hζ
    obtain ⟨hs, hz⟩ := hζ
    obtain ⟨⟨hs, hβ⟩, -⟩ := (ConPolyZono.aux_mem_starConsRows cPZ ζ).mp hs
    obtain ⟨-, hz⟩ := (ConPolyZono.aux_mem_starGenRows cPZ ζ).mp hz
    refine ⟨fun k => ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k)),
      fun j => ζ (Fin.castAdd cPZ.h (Fin.natAdd cPZ.p j)), (Interval.mem_unit_iff _).mp hβ, hs,
      fun i => ?_⟩
    rw [hx i, ConPolyZono.aux_starSet_point]
    simp only [hz]
    ring
  -- back: the factors, the independent coefficients and the monomials appended
  · rintro ⟨a, β, hβ, hs, hx⟩
    have ha := ((PolyLevelSet.mem_construct_iff_of_eq_unit cPZ.cons_eq cPZ.cons_dom).mp hs).1
    set ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h) :=
      Fin.append (Fin.append a β) (PolyZonotope.monomial cPZ.E a) with hζ
    have hleft : ∀ k, ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k)) = a k := fun k => by
      rw [hζ, Fin.append_left, Fin.append_left]
    have hmid : ∀ j, ζ (Fin.castAdd cPZ.h (Fin.natAdd cPZ.p j)) = β j := fun j => by
      rw [hζ, Fin.append_left, Fin.append_right]
    have hA : (fun k => ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k))) = a := funext hleft
    -- the monomials of the cube lie in it, so all of `ζ` does
    have hright : ∀ l, |ζ (Fin.natAdd (cPZ.p + cPZ.qI) l)| ≤ 1 := fun l => by
      rw [hζ, Fin.append_right]
      exact PolyZonotope.abs_monomial_le_one cPZ.E ha l
    have hbox : ζ ∈ (Interval.unit _).construct := (Interval.mem_unit_iff ζ).mpr
      (Fin.addCases (Fin.addCases (fun k => by rw [hleft]; exact ha k)
        (fun j => by rw [hmid]; exact hβ j)) hright)
    refine ⟨ζ, ⟨hbox, ?_⟩, fun i => ?_⟩
    · rw [PolyLevelSet.and_exact]
      refine ⟨(ConPolyZono.aux_mem_starConsRows cPZ ζ).mpr ⟨⟨by rw [hA]; exact hs,
          (Interval.mem_unit_iff _).mpr fun j => by rw [hmid]; exact hβ j⟩,
          (Interval.mem_unit_iff _).mpr hright⟩,
        (ConPolyZono.aux_mem_starGenRows cPZ ζ).mpr
          ⟨hbox, fun l => by rw [hA, hζ, Fin.append_right]⟩⟩
    · rw [hx i, ConPolyZono.aux_starSet_point]
      simp only [hζ, Fin.append_right]
      simp only [← hζ, hmid]
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
