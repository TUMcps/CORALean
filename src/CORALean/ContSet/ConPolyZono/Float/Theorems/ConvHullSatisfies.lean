module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullSingle
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemCartProdIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemCopiesIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemLinearIff
public import CORALean.ContSet.ConPolyZono.Float.Theorems.AbsSubLeSubUp
public import CORALean.Global.Float.IntRound

@[expose] public section

/-!
# The stored hull's constraints hold wherever the copies' and the weights' do

The stored constraint is the operand's copies beside the weight row
(`PolyLevelSet.mem_cartProd_iff`): a copy's rows are the operand's at that copy's factors, held
to the operand's right-hand side and slack (`PolyLevelSet.mem_copies_iff`), and the weight row is
the weights' sum (`PolyLevelSet.mem_linear_iff`), held to `1 - a` stored from below with the gap
to the upward rounding as its slack.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.convHullSingle_satisfies_of_real (a : ℕ) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (v : Fin (a * cPZ.p + a) → ℝ)
    (hcopy : ∀ j, (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) ∈ cPZ.cons.construct)
    (hw : ∑ j, v (Fin.natAdd (a * cPZ.p) j) = 1 - (a : ℝ)) : -- --- STMT ---
    v ∈ (cPZ.convHullSingle a).cons.construct := by -- --- PROOF ---
  refine (PolyLevelSet.mem_cartProd_iff _ _ v).mpr
    ⟨(PolyLevelSet.mem_copies_iff _ _ _).mpr hcopy, (PolyLevelSet.mem_linear_iff _ _ _ _ _).mpr ?_⟩
  -- the weight row: the weights' sum, `1 - a` exactly, stored between its two roundings
  intro _
  show |(∑ j, toReal (one : 𝕋) * v (Fin.natAdd (a * cPZ.p) j)) - toReal (intDown (1 - (a : ℤ)) : 𝕋)|
    ≤ |toReal (subUp (intUp (1 - (a : ℤ))) (intDown (1 - (a : ℤ))) : 𝕋)|
  simp only [toReal_one, one_mul]
  rw [hw]
  obtain ⟨h₁, h₂⟩ := intDown_le_intUp (𝕋 := 𝕋) (1 - (a : ℤ))
  push_cast at h₁ h₂
  exact ConPolyZono.abs_sub_le_subUp h₁ h₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
