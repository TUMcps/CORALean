module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Jacobian
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.Jacobian

@[expose] public section

/-!
# The float `jacobian` encloses the exact one

The exact layer's `jacobian` of what the stored floats denote lies in the float one: its generator
columns are `E k i` times the stored ones, which the stored lower multiple is off from by at most
`jacobianGap`, and the monomials lie in `[-1, 1]`, so the box holds the difference. The exact
layer's `jacobian_hasDerivAt` says what the exact set is, the derivative of the point along `k`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A column's exact multiple is off from the stored one by at most the gap. -/
theorem PolyZonotope.aux_jacobianGap (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (r : Fin n)
    (i : Fin pZ.h) :
    |(pZ.E k i : ℝ) * toReal (pZ.G i r) - toReal ((pZ.jacobian k).G i r)|
      ≤ toReal (pZ.jacobianGap k r i) := by -- --- PROOF ---
  have hlo := sumDown_le_sum (fun _ : Fin (pZ.E k i) => pZ.G i r)
  have hhi := sum_le_sumUp (fun _ : Fin (pZ.E k i) => pZ.G i r)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hhi
  have hgap := sub_le_subUp (sumUp fun _ : Fin (pZ.E k i) => pZ.G i r)
    (sumDown fun _ : Fin (pZ.E k i) => pZ.G i r)
  have hG : toReal ((pZ.jacobian k).G i r) = toReal (sumDown fun _ : Fin (pZ.E k i) => pZ.G i r) :=
    rfl
  rw [abs_le]
  simp only [PolyZonotope.jacobianGap]
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.jacobian_outer (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) :
    (Real.PolyZonotope.jacobian (nominal pZ) k).construct ⊆
      (pZ.jacobian k).construct := by -- --- PROOF ---
  rintro _ ⟨a, β, ha, hβ, rfl⟩
  -- the stored multiples are off by `Δ`, which the box holds
  have hbox := PolyZonotope.mem_generatorError_monomial (E := (pZ.jacobian k).E) (a := a)
    (Δ := fun r l => (pZ.E k l : ℝ) * toReal (pZ.G l r) - toReal ((pZ.jacobian k).G l r))
    (pZ.aux_jacobianGap k) ha
  refine ⟨fun i => toReal ((pZ.jacobian k).c i)
      + (∑ l, toReal ((pZ.jacobian k).G l i) * Real.PolyZonotope.monomial (pZ.jacobian k).E a l)
      + ∑ j, toReal ((pZ.jacobian k).GI j i) * β j,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩, _, hbox, ?_⟩
  funext i
  -- no independent generators on either side
  have h0 : ∑ j, β j • ((nominal pZ).jacobian k).GI j = (0 : Vec ℝ n) :=
    Finset.sum_eq_zero fun j _ => (j : Fin 0).elim0
  have h1 : ∑ j, toReal ((pZ.jacobian k).GI j i) * β j = 0 :=
    Finset.sum_eq_zero fun j _ => (j : Fin 0).elim0
  have hc : toReal ((pZ.jacobian k).c i) = 0 := toReal_zero
  have hE : (pZ.jacobian k).E = ((nominal pZ).jacobian k).E := rfl
  rw [h0]
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [h1, hc, hE]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- the stored multiples plus their errors are the exact multiples
  have hG : ∀ x, ((nominal pZ).jacobian k).G x i = (pZ.E k x : ℝ) * toReal (pZ.G x i) :=
    fun x => rfl
  have hc0 : ((nominal pZ).jacobian k).c i = 0 := rfl
  have hsum : (∑ l, toReal ((pZ.jacobian k).G l i)
        * Real.PolyZonotope.monomial ((nominal pZ).jacobian k).E a l)
      + (∑ l, ((pZ.E k l : ℝ) * toReal (pZ.G l i) - toReal ((pZ.jacobian k).G l i))
        * Real.PolyZonotope.monomial ((nominal pZ).jacobian k).E a l)
      = ∑ l, Real.PolyZonotope.monomial ((nominal pZ).jacobian k).E a l
        * ((pZ.E k l : ℝ) * toReal (pZ.G l i)) := by
    exact Finset.sum_add_distrib.symm.trans (Finset.sum_congr rfl fun l _ => by ring)
  rw [hc0]
  simp only [hG]
  simp only [zero_add, add_zero]
  exact hsum

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
