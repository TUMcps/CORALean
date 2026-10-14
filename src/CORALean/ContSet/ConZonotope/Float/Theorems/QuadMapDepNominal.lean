module

public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapDep
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapCBetween
public import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapGClose
public import CORALean.ContSet.ConZonotope.Real.Theorems.QuadMapOuter
public import CORALean.ContSet.HPolytope.Float.Operations.MemPadLeftIff
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError

@[expose] public section

/-!
# The quadratic image of the nominal set, on the factors of `quadMapDep`

The exact layer's enclosure (`Real.ConZonotope.quadMap_outer`) on the read-back operand gives
coefficients `β'`, the point's own followed by the squares and the products, that meet the operand's
constraints on their first block. At those same coefficients the stored zonotope's nominal point
differs from the exact one by the shortfall of the stored centre and, per coefficient in `[-1,1]`,
that of the stored generators, which the box `quadMapDep` returns holds. The constraints are the
operand's padded by the two new blocks, so they hold at `β'` exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.quadMapDep_nominal (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    (fun x : Vec ℝ n => fun i => x ⬝ᵥ (toRealMat (Q i) *ᵥ x)) '' nominalSet cZ
      ⊆ nominalSet (ConZonotope.quadMapDep Q cZ)
        + (I_error (ConZonotope.quadMapDep Q cZ)).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, rfl⟩
  -- the exact layer's enclosure, on the read-back operand
  obtain ⟨β, hβ, hP, hx⟩ := Real.ConZonotope.quadMap_outer (fun k => toRealMat (Q k))
    (nominal cZ) ⟨z, hz, rfl⟩
  -- the same coefficients, spelt at this layer's index type
  obtain ⟨β', hβ', hP', hx'⟩ : ∃ β' : Fin (cZ.h + cZ.h + cZ.h * cZ.h) → ℝ, (∀ j, |β' j| ≤ 1)
      ∧ β' ∈ (ConZonotope.quadMapDep Q cZ).P.construct
      ∧ ∀ i, (fun x : Vec ℝ n => fun i => x ⬝ᵥ (toRealMat (Q i) *ᵥ x)) z i
        = (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
          + ∑ l, β' l
            * (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).G l i := by
    refine ⟨β, hβ, ?_, fun i => ?_⟩
    -- the constraints of the exact form are the operand's, pulled back through two blocks
    · exact HPolytope.mem_padLeft_iff.mpr (HPolytope.mem_padLeft_iff.mpr hP)
    · have := congrFun hx i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this
  -- the two shortfalls, in the box the stored zonotope carries
  have hd₁ : (fun i => (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
        - toReal (ConZonotope.quadMapCDown Q cZ i))
      ∈ (Interval.residual (ConZonotope.quadMapCDown Q cZ) (ConZonotope.quadMapCUp Q cZ)
        (ConZonotope.quadMapCDown Q cZ)).construct :=
    Interval.sub_mem_residual fun i => ConZonotope.quadMapC_between Q cZ i
  have hd₂ : (fun i => ∑ l, ((Real.ConZonotope.quadMap (fun k => toRealMat (Q k))
        (nominal cZ)).G l i - toReal (ConZonotope.quadMapGDown Q cZ i l)) * β' l)
      ∈ (Zonotope.generatorError (ConZonotope.quadMapGDiff Q cZ)).construct :=
    Zonotope.mem_generatorError (fun i l => ConZonotope.quadMapG_close Q cZ i l) hβ'
  -- the stored nominal point at `β'`
  refine ⟨_, ConZonotope.mem_nominalSet_iff.mpr ⟨β', hβ', hP', fun _ => rfl⟩, _,
    Interval.plus_outer _ _ ⟨_, hd₁, _, hd₂, rfl⟩, ?_⟩
  funext i
  -- the stored point and the two shortfalls, coordinate `i`
  show toReal (ConZonotope.quadMapCDown Q cZ i)
      + ∑ l, toReal (ConZonotope.quadMapGDown Q cZ i l) * β' l
      + ((Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
          - toReal (ConZonotope.quadMapCDown Q cZ i)
        + ∑ l, ((Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).G l i
          - toReal (ConZonotope.quadMapGDown Q cZ i l)) * β' l)
      = z ⬝ᵥ (toRealMat (Q i) *ᵥ z)
  have hsplit : ∑ l, ((Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).G l i
        - toReal (ConZonotope.quadMapGDown Q cZ i l)) * β' l
      = ∑ l, β' l * (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).G l i
        - ∑ l, toReal (ConZonotope.quadMapGDown Q cZ i l) * β' l := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hsplit]
  have e := hx' i
  simp only at e
  linarith [e]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
