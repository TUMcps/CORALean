module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Union
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionUpperHolds
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLower
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.EvalNominalCoreCartProd
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.EvalNominalCoreSwitch
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemAndRowsIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalPadVars
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalSwitch
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalAnd
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic
public import CORALean.Global.Float.GenBlockDiag
public import CORALean.ContSet.ConPolyZono.Real.Operations.Union

@[expose] public section

/-!
# The stored union's constraints hold wherever the exact union's do

At a factor vector in the cube where the exact union of the two read-back operands (`nominalCore`)
meets its selector rows exactly and its operand rows within the operands' slacks, the stored union
meets its own rows within theirs. Both constraints are the selector rows stacked on the operand
rows (`PolyLevelSet.eval_and_`, `PolyLevelSet.and_exact`): the selector rows by
`holds_unionUpper_of_real`, the operand rows being the exact ones
(`aux_eval_nominalCore_unionLower`) with the same slacks.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored operand rows, read back, are the exact layer's at the read-back operands. -/
theorem ConPolyZono.aux_eval_nominalCore_unionLower {p₁ p₂ : ℕ} (P₁ : PolyLevelSet 𝕋 p₁)
    (P₂ : PolyLevelSet 𝕋 p₂) (a : Fin (p₁ + p₂ + 2) → ℝ) :
    (ConPolyZono.unionLower P₁ P₂).nominalCore.eval a
      = (Real.ConPolyZono.unionLower P₁.nominalCore P₂.nominalCore).eval a := by -- --- PROOF ---
  funext i
  unfold ConPolyZono.unionLower Real.ConPolyZono.unionLower
  rw [PolyLevelSet.eval_nominalCore_switch, Real.PolyLevelSet.eval_switch,
    Real.PolyLevelSet.eval_switch]
  have hv : ((P₁.cartProd P₂).padVars (Interval.unit 2)).nominalCore.eval a
      = ((P₁.nominalCore.cartProd P₂.nominalCore).padVars (Real.Interval.unit 2)).eval a := by
    rw [Real.PolyLevelSet.eval_padVars]
    exact (Real.PolyLevelSet.eval_padVars _ (Real.Interval.unit 2) a).trans
      (PolyLevelSet.eval_nominalCore_cartProd P₁ P₂ _)
  have hb : ((P₁.cartProd P₂).padVars (Interval.unit 2)).nominalCore.b i
      = ((P₁.nominalCore.cartProd P₂.nominalCore).padVars (Real.Interval.unit 2)).b i :=
    congrFun (toRealVec_append P₁.b P₂.b) i
  rw [hv, hb]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.union_satisfies_of_real (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ₁.p + cPZ₂.p + 2) → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (h : ∀ i, |((Real.ConPolyZono.union cPZ₁.nominalCore cPZ₂.nominalCore).cons.A
        *ᵥ Real.PolyZonotope.monomial
          (Real.ConPolyZono.union cPZ₁.nominalCore cPZ₂.nominalCore).cons.R a) i
      - (Real.ConPolyZono.union cPZ₁.nominalCore cPZ₂.nominalCore).cons.b i|
      ≤ |Fin.append (0 : Vec ℝ (1 + 1))
          (Fin.append (toRealVec cPZ₁.cons.b_error)
            (toRealVec cPZ₂.cons.b_error)) i|) : -- --- STMT ---
    a ∈ (cPZ₁.union cPZ₂).cons.construct := by -- --- PROOF ---
  -- the exact operand rows, named once
  set L := Real.ConPolyZono.unionLower cPZ₁.nominalCore.cons cPZ₂.nominalCore.cons with hLdef
  -- the exact rows, split into the selector block and the operands' block
  have hv := Real.PolyLevelSet.eval_and_ (Real.ConPolyZono.unionUpper cPZ₁.p cPZ₂.p) L a
  replace h : ∀ i : Fin (1 + 1 + (cPZ₁.cons.m + cPZ₂.cons.m)),
      |Fin.append ((Real.ConPolyZono.unionUpper cPZ₁.p cPZ₂.p).eval a) (L.eval a) i|
      ≤ |Fin.append (0 : Vec ℝ (1 + 1))
          (Fin.append (toRealVec cPZ₁.cons.b_error) (toRealVec cPZ₂.cons.b_error)) i| :=
    fun i => by
      rw [← hv]
      exact h i
  -- the selector rows have no slack, so they hold exactly
  have hUmem : a ∈ (Real.ConPolyZono.unionUpper cPZ₁.p cPZ₂.p).construct :=
    (Real.PolyLevelSet.mem_construct_iff_of_eq
      (Real.LevelSet.append_op_eq (fun _ => rfl) fun _ => rfl)).mpr
        ⟨(Real.Interval.mem_unit_iff a).mpr ha, fun i => by
        have h0 := h (Fin.castAdd _ i)
        erw [Fin.append_left, Fin.append_left, Pi.zero_apply, abs_zero] at h0
        exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)⟩
  have hL : ∀ j, |L.eval a j|
      ≤ |Fin.append (toRealVec cPZ₁.cons.b_error) (toRealVec cPZ₂.cons.b_error) j| := fun j => by
    have h1 := h (Fin.natAdd (1 + 1) j)
    erw [Fin.append_right, Fin.append_right] at h1
    exact h1
  -- the stored union: selector rows by `holds_unionUpper_of_real`, operand rows read back
  show a ∈ ((ConPolyZono.unionUpper cPZ₁.p cPZ₂.p).andRows
    (ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons)).construct
  rw [PolyLevelSet.mem_andRows_iff]
  refine ⟨ConPolyZono.holds_unionUpper_of_real cPZ₁.p cPZ₂.p a ha hUmem, fun i => ?_⟩
  rw [show (ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons).op i = .eq from
    Real.LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq i]
  -- the operand rows, the exact ones at the read-back entries, with the same slacks
  show |(ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons).nominalCore.eval a i|
    ≤ |toReal (Fin.append cPZ₁.cons.b_error cPZ₂.cons.b_error i)|
  rw [ConPolyZono.aux_eval_nominalCore_unionLower]
  exact (hL i).trans_eq (congrArg abs (congrFun (toRealVec_append _ _) i).symm)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
