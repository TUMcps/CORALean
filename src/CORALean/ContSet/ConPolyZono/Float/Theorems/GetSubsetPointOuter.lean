import CORALean.ContSet.ConPolyZono.Float.Theorems.GetSubsetSatisfies
import CORALean.ContSet.ConPolyZono.Real.Theorems.GetSubsetSatisfies
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint

/-!
# `ConPolyZono.getSubset`, one factor vector at a time

`getSubset_outer` says the exact `getSubset` of the stored set, plus the error box, lies in the
float one, and leaves the factor vector that reaches a point unnamed. A fold of `getSubset`
steps needs it named: here the float `getSubset` is read at the same factor vector `a` as the
exact one, which by `getSubset_point` is the stored set at `a` with factor `k` sent to
`cen + rad·aₖ`. Its constraint holds at `a` whenever the stored set's holds there, and its
generator sum at `a`, plus a point of its error box, is the stored set's at the re-parametrized
vector plus the given point of the old error box: the rounding of the generators, scaled by
monomials in `[-1, 1]`, is what the box grew by.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.getSubset_point_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.p)
    (cen rad : 𝕋) (a : Fin cPZ.p → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (hsat : cPZ.satisfies (Function.update a k (toReal cen + toReal rad * a k))) :
    (cPZ.getSubset k cen rad).satisfies a ∧ ∀ e ∈ cPZ.err.construct,
      ∃ e' ∈ (cPZ.getSubset k cen rad).err.construct, ∀ i,
        (∑ l, toReal ((cPZ.getSubset k cen rad).G l i)
          * Real.PolyZonotope.monomial (cPZ.getSubset k cen rad).E a l) + e' i
        = (∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.E
            (Function.update a k (toReal cen + toReal rad * a k)) l) + e i := by -- --- PROOF ---
  refine ⟨ConPolyZono.getSubset_satisfies cPZ k cen rad a ha
    ((Real.ConPolyZono.getSubset_satisfies (nominal cPZ) k (toReal cen) (toReal rad) a).mpr
      hsat), fun e he => ?_⟩
  -- the rounding of the generators, scaled by the monomials, lies in the added box
  have hbox : (fun i => ∑ l, (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k
        (toReal cen) (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
          * Real.PolyZonotope.monomial
            (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
      ∈ (PolyZonotope.generatorError (cPZ.toPolyZonotope.getSubsetGDiff k cen rad)).construct :=
    PolyZonotope.mem_generatorError_monomial
      (PolyZonotope.getSubsetG_close cPZ.toPolyZonotope k cen rad) ha
  -- the new error point: the old one plus the generators' rounding at `a`
  refine ⟨fun i => (∑ l, (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k
      (toReal cen) (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
      * Real.PolyZonotope.monomial
        (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l) + e i, ?_, ?_⟩
  · -- the sum of the two boxes' points is a point of the interval sum
    intro i
    have h₁ : toReal (cPZ.toPolyZonotope.err.inf i) ≤ e i := (he i).1
    have h₂ : e i ≤ toReal (cPZ.toPolyZonotope.err.sup i) := (he i).2
    -- the generator rounding's point, within its own box
    have h₃ : toReal ((PolyZonotope.generatorError
          (cPZ.toPolyZonotope.getSubsetGDiff k cen rad)).inf i) ≤
          (∑ l, (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
            (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l) ∧
        (∑ l, (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
            (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l) ≤
          toReal ((PolyZonotope.generatorError
            (cPZ.toPolyZonotope.getSubsetGDiff k cen rad)).sup i) := hbox i
    refine ⟨le_trans (addDown_le_add _ _) ?_, le_trans ?_ (add_le_addUp _ _)⟩
    · simp only [Entrywise.entry]
      linarith [h₃.1]
    · simp only [Entrywise.entry]
      linarith [h₃.2]
  · intro i
    -- the exact `getSubset` at `a` is the stored set at the re-parametrized vector
    have hpt := congrFun (Real.PolyZonotope.getSubset_point (nominal cPZ.toPolyZonotope) k
      (toReal cen) (toReal rad) a) i
    simp only [Real.PolyZonotope.point, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hpt
    have hpt' : ∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen) (toReal rad)
            l i * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l
        = ∑ l, toReal (cPZ.G l i) * Real.PolyZonotope.monomial cPZ.E
            (Function.update a k (toReal cen + toReal rad * a k)) l := by
      have h2 : ∀ (s t : ℝ), toReal (cPZ.c i) + s = toReal (cPZ.c i) + t → s = t :=
        fun s t h => by linarith
      refine (Finset.sum_congr rfl fun l _ => mul_comm _ _).trans
        ((h2 _ _ hpt).trans (Finset.sum_congr rfl fun l _ => mul_comm _ _))
    -- the stored and the exact generator sums differ by exactly the box's point
    have hsum : (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l)
          * Real.PolyZonotope.monomial
            (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
        + (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
            (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
        = ∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen) (toReal rad) l i
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    -- spelt out, the new sum and error point are the exact sum plus the old error point
    show (∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l)
          * Real.PolyZonotope.monomial
            (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l)
        + ((∑ l : Fin (cPZ.toPolyZonotope.h * (cPZ.toPolyZonotope.maxExp k + 1)),
          (Real.PolyZonotope.getSubsetG (nominal cPZ.toPolyZonotope) k (toReal cen)
            (toReal rad) l i - toReal (cPZ.toPolyZonotope.getSubsetGDown k cen rad i l))
            * Real.PolyZonotope.monomial
              (Real.PolyZonotope.getSubsetE (nominal cPZ.toPolyZonotope) k) a l) + e i)
        = _
    linarith [hsum, hpt']

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
