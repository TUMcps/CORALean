module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionSatisfies
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Real.Operations.SumUnionE
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombNominalAt

@[expose] public section

/-!
# A point of the exact union lies in the stored one

A point of the exact union of the two read-back operands, moved by a vector of the two operand
boxes' hull, lies in the stored union. Its factors are the exact union's own, so the stored
constraints hold there (`union_satisfies_of_real`). What differs is the center and the sliding
generator, which are stored rounded down: their shortfalls are the midpoint residual and, over
the selector `t` in `[-1,1]`, the symmetric half-difference box, both of which the stored box holds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored generator sum at a factor vector, split into the selector's own and the two
operands'. -/
theorem ConPolyZono.aux_sum_union (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ₁.p + cPZ₂.p + 2) → ℝ) (i : Fin n) :
    (∑ l, toReal ((cPZ₁.union cPZ₂).G l i)
        * Real.PolyZonotope.monomial (cPZ₁.union cPZ₂).E a l)
      = a (Real.ConPolyZono.unionSel cPZ₁.p cPZ₂.p)
          * toReal (PolyZonotope.halfDiff cPZ₁.c cPZ₂.c i)
        + ((∑ l, Real.PolyZonotope.monomial cPZ₁.E
              (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) l * toReal (cPZ₁.G l i))
          + ∑ l, Real.PolyZonotope.monomial cPZ₂.E
              (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) l
                * toReal (cPZ₂.G l i)) := by -- --- PROOF ---
  -- the exact layer's sum, at the generators the stored ones read back as
  have h := Real.ConPolyZono.sum_unionE (2 * toReal (PolyZonotope.halfDiff cPZ₁.c cPZ₂.c i))
    (0 : ℝ) (fun l => toReal (cPZ₁.G l i)) (fun l => toReal (cPZ₂.G l i)) cPZ₁.E cPZ₂.E a
  simp only [smul_eq_mul] at h
  have key : (∑ l, toReal ((cPZ₁.union cPZ₂).G l i)
        * Real.PolyZonotope.monomial (cPZ₁.union cPZ₂).E a l)
      = ∑ x, Real.PolyZonotope.monomial (Real.ConPolyZono.unionE cPZ₁.E cPZ₂.E) a x
        * Real.ConPolyZono.unionG (2 * toReal (PolyZonotope.halfDiff cPZ₁.c cPZ₂.c i)) 0
          (fun l => toReal (cPZ₁.G l i)) (fun l => toReal (cPZ₂.G l i)) x := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
    congr 1
    refine Fin.addCases (fun _ => ?_) (fun l => ?_) l
    · simp only [ConPolyZono.union, Real.ConPolyZono.unionG, Fin.append_left]
      ring
    · simp only [ConPolyZono.union, Real.ConPolyZono.unionG, Fin.append_right]
      refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
        simp only [Fin.append_left, Fin.append_right]
  rw [key, h]
  ring


/-- The two directed midpoints bracket the exact one, halving being exact. -/
theorem ConPolyZono.aux_midpoint_mem (a b : Vec 𝕋 n) :
    (fun i => (toReal (a i) + toReal (b i)) / 2 - toReal (PolyZonotope.midpoint a b i))
      ∈ (PolyZonotope.midpointResidual a b).construct :=
  Interval.sub_mem_residual fun i => by
    refine ⟨?_, ?_⟩
    · rw [toReal_half]
      have := addDown_le_add (a i) (b i)
      linarith
    · rw [toReal_half]
      have := add_le_addUp (a i) (b i)
      linarith

/-- The sliding generator rounds down, so its shortfall is non-negative and at most the gap
between the two directed halvings; the selector spreads it over `[-1,1]`. -/
theorem ConPolyZono.aux_halfDiff_mem (a b : Vec 𝕋 n) {t : ℝ} (ht : |t| ≤ 1) :
    (fun i => ((toReal (a i) - toReal (b i)) / 2 - toReal (PolyZonotope.halfDiff a b i)) * t)
      ∈ (PolyZonotope.halfDiffError a b).construct := by -- --- PROOF ---
  intro i
  have hdown : toReal (PolyZonotope.halfDiff a b i) = toReal (subDown (a i) (b i)) / 2 :=
    toReal_half _
  -- the shortfall is non-negative
  have hq0 : 0 ≤ (toReal (a i) - toReal (b i)) / 2
      - toReal (PolyZonotope.halfDiff a b i) := by
    rw [hdown]
    have := subDown_le_sub (a i) (b i)
    linarith
  -- and at most the gap between the two directed halvings
  have hqR : (toReal (a i) - toReal (b i)) / 2 - toReal (PolyZonotope.halfDiff a b i)
      ≤ toReal (subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))) := by
    have h1 := sub_le_subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))
    rw [toReal_half, toReal_half] at h1
    have h2 := sub_le_subUp (a i) (b i)
    rw [hdown]
    linarith
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  have hbox : -toReal (subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i))))
        ≤ ((toReal (a i) - toReal (b i)) / 2 - toReal (PolyZonotope.halfDiff a b i)) * t
      ∧ ((toReal (a i) - toReal (b i)) / 2 - toReal (PolyZonotope.halfDiff a b i)) * t
        ≤ toReal (subUp (half (subUp (a i) (b i))) (half (subDown (a i) (b i)))) :=
    ⟨by nlinarith, by nlinarith⟩
  refine ⟨?_, hbox.2⟩
  show toReal (neg _) ≤ _
  rw [toReal_neg]
  exact hbox.1

/-- The stored nominal point at factors the exact union satisfies, which the stored union
satisfies too. -/
theorem ConPolyZono.aux_union_mem_nominal (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ₁.p + cPZ₂.p + 2) → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (hsat : (Real.ConPolyZono.union (nominal cPZ₁) (nominal cPZ₂)).satisfies a) :
    (fun i => toReal ((cPZ₁.union cPZ₂).c i)
      + ∑ l, toReal ((cPZ₁.union cPZ₂).G l i)
        * Real.PolyZonotope.monomial (cPZ₁.union cPZ₂).E a l)
      ∈ nominalSet (cPZ₁.union cPZ₂) := by -- --- PROOF ---
  refine ConPolyZono.mem_nominalSet_iff.mpr ⟨a, fun j => j.elim0, ha, fun j => j.elim0,
    ConPolyZono.union_satisfies_of_real cPZ₁ cPZ₂ a ha hsat, fun i => ?_⟩
  -- no independent generators
  have h0 : ∀ f : Fin (cPZ₁.union cPZ₂).qI → ℝ, ∑ j, f j = 0 := fun f =>
    Finset.sum_eq_zero fun j _ => Fin.elim0 (show Fin 0 from j)
  rw [h0, add_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.union_point_mem (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) {y e : Vec ℝ n}
    (hy : y ∈ (Real.ConPolyZono.union (nominal cPZ₁) (nominal cPZ₂)).construct)
    (he : e ∈ (cPZ₁.I_error.or cPZ₂.I_error).construct) :
    y + e ∈ (cPZ₁.union cPZ₂).construct := by -- --- PROOF ---
  obtain ⟨a, β, ha, hβ, hsat, hy⟩ := hy
  set t := a (Real.ConPolyZono.unionSel cPZ₁.p cPZ₂.p) with ht
  have hz := ConPolyZono.aux_union_mem_nominal cPZ₁ cPZ₂ a ha hsat
  have hd₁ := ConPolyZono.aux_midpoint_mem cPZ₁.c cPZ₂.c
  have hd₂ := ConPolyZono.aux_halfDiff_mem cPZ₁.c cPZ₂.c
    (ha (Real.ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
  -- the stored point, moved by the operand box's vector and the two rounding shortfalls
  refine ⟨_, hz, e + ((fun i => (toReal (cPZ₁.c i) + toReal (cPZ₂.c i)) / 2
      - toReal (PolyZonotope.midpoint cPZ₁.c cPZ₂.c i))
    + (fun i => ((toReal (cPZ₁.c i) - toReal (cPZ₂.c i)) / 2
        - toReal (PolyZonotope.halfDiff cPZ₁.c cPZ₂.c i)) * t)),
    Interval.plus_outer _ _ ⟨e, he, _, Interval.plus_outer _ _ ⟨_, hd₁, _, hd₂, rfl⟩, rfl⟩, ?_⟩
  funext i
  -- the exact union's point, coordinate `i`, against the stored sums
  have hyi := congrFun hy i
  -- the exact layer's generator sum, read at coordinate `i`
  have hG := Real.ConPolyZono.sum_unionE (toRealVec cPZ₁.c) (toRealVec cPZ₂.c)
    (fun l i => toReal (cPZ₁.G l i)) (fun l i => toReal (cPZ₂.G l i)) cPZ₁.E cPZ₂.E a
  have hGi := congrFun hG i
  -- the stored generator sum, and the exact one
  have hS := ConPolyZono.aux_sum_union cPZ₁ cPZ₂ a i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    at hGi
  -- the exact union has no independent generators
  have h0 : (∑ j, β j • ((nominal cPZ₁).union (nominal cPZ₂)).GI j) = 0 :=
    Finset.sum_eq_zero fun j _ => Fin.elim0 (show Fin 0 from j)
  have hyi' : y i = 2⁻¹ * (toReal (cPZ₁.c i) + toReal (cPZ₂.c i))
      + ∑ x, Real.PolyZonotope.monomial (Real.ConPolyZono.unionE cPZ₁.E cPZ₂.E) a x
        * Real.ConPolyZono.unionG (toRealVec cPZ₁.c) (toRealVec cPZ₂.c)
          (fun l i => toReal (cPZ₁.G l i)) (fun l i => toReal (cPZ₂.G l i)) x i := by
    rw [hyi, h0, add_zero]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hc : (cPZ₁.union cPZ₂).c i = PolyZonotope.midpoint cPZ₁.c cPZ₂.c i := rfl
  simp only [Pi.add_apply, hc]
  simp only [toRealVec] at hGi hyi'
  linarith [hyi', hGi, hS]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
