module

public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_StarSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConstruct
public import CORALean.ContSet.PolyLevelSet.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.StarSet.Real.Instances
public import Mathlib.Algebra.Order.Ring.Abs
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemPadVarsIff

@[expose] public section

/-!
# A constrained polynomial zonotope is exactly its star set

Each of the predicate's three systems says one thing of the coefficients `(α, β, z)`: the cube,
`αₖ² ≤ 1` and `βⱼ² ≤ 1`; the constraint at `α`; and `z = μ_E(α)`. With `z` the monomials the
star set's linear point `c + Σ GIⱼ βⱼ + Σ Gₗ zₗ` is the constrained polynomial zonotope's at
`(α, β)`, so the two denote one set. The converse, a star set with a polynomial level set as its
predicate as a constrained polynomial zonotope, is not exact: the predicate may be unbounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The monomial with exponent `2` at `i` alone. -/
theorem ConPolyZono.aux_prod_sq {N : ℕ} (y : Fin N → ℝ) (i : Fin N) :
    (∏ k, y k ^ (if k = i then 2 else 0)) = y i ^ 2 :=
  (Finset.prod_eq_single i (fun k _ hk => by rw [if_neg hk, pow_zero])
    (fun h => absurd (Finset.mem_univ i) h)).trans (by rw [if_pos rfl])

/-- The cube rows say `|xₖ| ≤ 1` of the factors and the independent coefficients. -/
theorem ConPolyZono.aux_mem_starBoxRows (cPZ : ConPolyZono (Vec ℝ n))
    (ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h)) :
    ζ ∈ cPZ.starBoxRows.construct ↔ ∀ k, |ζ (Fin.castAdd cPZ.h k)| ≤ 1 := by -- --- PROOF ---
  have hrow : ∀ i : Fin (cPZ.p + cPZ.qI),
      (cPZ.starBoxRows.A *ᵥ PolyZonotope.monomial cPZ.starBoxRows.R ζ) i
        = ζ (Fin.castAdd cPZ.h i) ^ 2 := by
    intro i
    show ∑ j, (if i = j then (1 : ℝ) else 0) * PolyZonotope.monomial
      (ConPolyZono.padE (fun k j => if k = j then 2 else 0) cPZ.h) ζ j = _
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), if_pos rfl, one_mul, ConPolyZono.monomial_padE]
    exact ConPolyZono.aux_prod_sq (fun k => ζ (Fin.castAdd cPZ.h k)) i
  show (∀ i, CompOp.holds .le ((cPZ.starBoxRows.A *ᵥ PolyZonotope.monomial cPZ.starBoxRows.R ζ
    - cPZ.starBoxRows.b) i)) ↔ _
  refine forall_congr' fun i => ?_
  rw [Pi.sub_apply, hrow i]
  simp only [CompOp.holds, ConPolyZono.starBoxRows, sub_nonpos]
  exact sq_le_one_iff_abs_le_one _

/-- The constraint rows say the constraint of the factors. -/
theorem ConPolyZono.aux_mem_starConsRows (cPZ : ConPolyZono (Vec ℝ n))
    (ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h)) :
    ζ ∈ cPZ.starConsRows.construct
      ↔ (fun k => ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k))) ∈ cPZ.cons.construct :=
  (PolyLevelSet.mem_padVars_iff _ _ ζ).trans (PolyLevelSet.mem_padVars_iff _ _ _)

/-- The generator rows say each `z` is its generator's monomial at the factors. -/
theorem ConPolyZono.aux_mem_starGenRows (cPZ : ConPolyZono (Vec ℝ n))
    (ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h)) : -- --- STMT ---
    ζ ∈ cPZ.starGenRows.construct ↔ ∀ l, ζ (Fin.natAdd (cPZ.p + cPZ.qI) l)
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
  show (∀ l, CompOp.holds .eq ((cPZ.starGenRows.A *ᵥ PolyZonotope.monomial cPZ.starGenRows.R ζ
    - cPZ.starGenRows.b) l)) ↔ _
  refine forall_congr' fun l => ?_
  rw [Pi.sub_apply, hrow l]
  simp only [CompOp.holds, ConPolyZono.starGenRows, sub_zero, sub_eq_zero]

/-- The star set's point at `(α, β, z)`, one coordinate: the generators on `z`, the independent
ones on `β`. -/
theorem ConPolyZono.aux_starSet_point (cPZ : ConPolyZono (Vec ℝ n))
    (ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h)) (i : Fin n) : -- --- STMT ---
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
theorem ConPolyZono.starSet_exact (cPZ : ConPolyZono (Vec ℝ n)) :
    cPZ.starSet.construct = cPZ.construct := by -- --- PROOF ---
  ext x
  rw [ConPolyZono.mem_construct_iff]
  show (∃ ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h),
    ζ ∈ (cPZ.starBoxRows.and_ (cPZ.starConsRows.and_ cPZ.starGenRows)).construct
    ∧ ∀ i, x i = cPZ.c i + ∑ k, cPZ.starSet.G i k * ζ k) ↔ _
  constructor
  -- the factors and the independent coefficients, read off the coefficients
  · rintro ⟨ζ, hζ, hx⟩
    rw [PolyLevelSet.and_exact, PolyLevelSet.and_exact] at hζ
    obtain ⟨hbox, hs, hz⟩ := hζ
    rw [ConPolyZono.aux_mem_starBoxRows] at hbox
    rw [ConPolyZono.aux_mem_starConsRows] at hs
    rw [ConPolyZono.aux_mem_starGenRows] at hz
    refine ⟨fun k => ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k)),
      fun j => ζ (Fin.castAdd cPZ.h (Fin.natAdd cPZ.p j)), fun k => hbox _, fun j => hbox _, hs,
      fun i => ?_⟩
    rw [hx i, ConPolyZono.aux_starSet_point]
    simp only [hz]
    ring
  -- back: the factors, the independent coefficients and the monomials appended
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    set ζ : Vec ℝ (cPZ.p + cPZ.qI + cPZ.h) :=
      Fin.append (Fin.append a β) (PolyZonotope.monomial cPZ.E a) with hζ
    have hleft : ∀ k, ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k)) = a k := fun k => by
      rw [hζ, Fin.append_left, Fin.append_left]
    have hmid : ∀ j, ζ (Fin.castAdd cPZ.h (Fin.natAdd cPZ.p j)) = β j := fun j => by
      rw [hζ, Fin.append_left, Fin.append_right]
    have hA : (fun k => ζ (Fin.castAdd cPZ.h (Fin.castAdd cPZ.qI k))) = a := funext hleft
    refine ⟨ζ, ?_, fun i => ?_⟩
    · rw [PolyLevelSet.and_exact, PolyLevelSet.and_exact]
      refine ⟨(ConPolyZono.aux_mem_starBoxRows cPZ ζ).mpr
          (Fin.addCases (fun k => by rw [hleft]; exact ha k) (fun j => by rw [hmid]; exact hβ j)),
        (ConPolyZono.aux_mem_starConsRows cPZ ζ).mpr (by rw [hA]; exact hs),
        (ConPolyZono.aux_mem_starGenRows cPZ ζ).mpr fun l => by rw [hA, hζ, Fin.append_right]⟩
    · rw [hx i, ConPolyZono.aux_starSet_point]
      simp only [hζ, Fin.append_right]
      simp only [← hζ, hmid]
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
