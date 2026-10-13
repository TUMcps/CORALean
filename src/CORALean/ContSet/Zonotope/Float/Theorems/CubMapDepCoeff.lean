import CORALean.ContSet.Zonotope.Float.Operations.CubMapDep
import CORALean.ContSet.Zonotope.Float.Theorems.CubMapCBetween
import CORALean.ContSet.Zonotope.Float.Theorems.CubMapGClose
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Real.Theorems.CubMapCoeff
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual

/-!
# The cubic image of a point of `cubMapDep`'s operand, coefficient by coefficient

The exact layer's coefficients (`Real.Zonotope.cubMap_coeff`) on the read-back operand give, at the
point `c + Σ pⱼ gⱼ`, coefficients `γ` in `[-1, 1]` whose linear block `(0, 0, j)` is the `pⱼ`. At
those coefficients the stored zonotope's nominal point differs from the exact one by the shortfall
of the stored centre and, per coefficient, that of the stored generators, which the box
`cubMapDep` returns holds. The linear block is stated for `ConZonotope.cubMap`, which ties it to
the constraints.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cubMapDep_coeff (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n))
    (p : Fin Z.h → ℝ) (hp : ∀ j, |p j| ≤ 1) :
    ∃ γ : Fin (Zonotope.cubMapDep T Z).h → ℝ, (∀ l, |γ l| ≤ 1)
      ∧ (∀ j : Fin Z.h,
          γ ((Real.Zonotope.cubIdx (Z.h + 1) (Z.h + 1) (Z.h + 1)).symm ((0, 0), j.succ)) = p j)
      ∧ ∃ e ∈ (Zonotope.cubMapDep T Z).E.construct,
          Real.PolyZonotope.cubEval (fun i k => toRealMat (T i k))
              (toRealVec Z.c + ∑ j, p j • toRealVec (Z.G j))
            = fun i => toReal ((Zonotope.cubMapDep T Z).c i)
              + ∑ l, toReal ((Zonotope.cubMapDep T Z).G l i) * γ l + e i := by -- --- PROOF ---
  -- the exact layer's enclosure, on the read-back operand
  obtain ⟨γ, hγ, hlin, hx⟩ := Real.Zonotope.cubMap_coeff (fun i k => toRealMat (T i k))
    (nominal Z : Real.Zonotope (Vec ℝ n)) p hp
  -- the two shortfalls, in the box the stored zonotope carries
  have hd₁ : (fun i => (Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
        (nominal Z : Real.Zonotope (Vec ℝ n))).c i - toReal (Zonotope.cubMapCDown T Z i))
      ∈ (Interval.residual (Zonotope.cubMapCDown T Z) (Zonotope.cubMapCUp T Z)
        (Zonotope.cubMapCDown T Z)).construct :=
    Interval.sub_mem_residual fun i => Zonotope.cubMapC_between T Z i
  have hd₂ : (fun i => ∑ l, ((Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
        (nominal Z : Real.Zonotope (Vec ℝ n))).G l i
          - toReal (Zonotope.cubMapGDown T Z i l)) * γ l)
      ∈ (Zonotope.generatorError (Zonotope.cubMapGDiff T Z)).construct :=
    Zonotope.mem_generatorError (fun i l => Zonotope.cubMapG_close T Z i l) hγ
  -- the stored nominal point at `γ`, and the two shortfalls
  refine ⟨γ, hγ, hlin, _, Interval.plus_outer _ _ ⟨_, hd₁, _, hd₂, rfl⟩, ?_⟩
  funext i
  have e : Real.PolyZonotope.cubEval (fun i k => toRealMat (T i k))
      (toRealVec Z.c + ∑ j, p j • toRealVec (Z.G j)) i = _ := congrFun hx i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e
  show _ = toReal (Zonotope.cubMapCDown T Z i)
      + ∑ l, toReal (Zonotope.cubMapGDown T Z i l) * γ l
      + ((Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n))).c i - toReal (Zonotope.cubMapCDown T Z i)
        + ∑ l, ((Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
          (nominal Z : Real.Zonotope (Vec ℝ n))).G l i
          - toReal (Zonotope.cubMapGDown T Z i l)) * γ l)
  -- the generator shortfalls split into the exact and the stored sum
  have hsplit : ∑ l, ((Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
        (nominal Z : Real.Zonotope (Vec ℝ n))).G l i - toReal (Zonotope.cubMapGDown T Z i l)) * γ l
      = ∑ l, γ l * (Real.Zonotope.cubMap (fun i k => toRealMat (T i k))
        (nominal Z : Real.Zonotope (Vec ℝ n))).G l i
        - ∑ l, toReal (Zonotope.cubMapGDown T Z i l) * γ l := by
    refine (Finset.sum_congr rfl fun l _ => ?_).trans (Finset.sum_sub_distrib _ _)
    ring
  rw [hsplit]
  linarith [e]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
