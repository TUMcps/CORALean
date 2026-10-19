module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Union
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionUpperHolds
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatUnionLowerA
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecUnionLowerB
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalAnd
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.AndExact
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
`holds_unionUpper_of_real`, the operand rows being the exact ones (`toRealMat_unionLowerA`,
`toRealVec_unionLowerB`) with the same slacks.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


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
      (Real.LevelSet.append_op_eq (fun _ => rfl) fun _ => rfl)).mpr fun i => by
        have h0 := h (Fin.castAdd _ i)
        erw [Fin.append_left, Fin.append_left, Pi.zero_apply, abs_zero] at h0
        exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
  have hL : ∀ j, |L.eval a j|
      ≤ |Fin.append (toRealVec cPZ₁.cons.b_error) (toRealVec cPZ₂.cons.b_error) j| := fun j => by
    have h1 := h (Fin.natAdd (1 + 1) j)
    erw [Fin.append_right, Fin.append_right] at h1
    exact h1
  -- the stored union: selector rows by `holds_unionUpper_of_real`, operand rows read back
  show a ∈ ((ConPolyZono.unionUpper cPZ₁.p cPZ₂.p).and_
    (ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons)).construct
  rw [PolyLevelSet.and_exact]
  refine ⟨ConPolyZono.holds_unionUpper_of_real cPZ₁.p cPZ₂.p a ha hUmem,
    (PolyLevelSet.mem_construct_iff_of_eq fun _ => rfl).mpr fun i => ?_⟩
  -- the operand rows, the exact ones at the read-back entries, with the same slacks
  have hL' : |(Real.ConPolyZono.unionLowerA (toRealMat cPZ₁.cons.A) (toRealVec cPZ₁.cons.b)
        (toRealMat cPZ₂.cons.A) (toRealVec cPZ₂.cons.b) *ᵥ Real.PolyZonotope.monomial
          (Real.ConPolyZono.unionLowerR cPZ₁.cons.R cPZ₂.cons.R) a) i
      - Real.ConPolyZono.unionLowerB (toRealVec cPZ₁.cons.b) (toRealVec cPZ₂.cons.b) i|
      ≤ |Fin.append (toRealVec cPZ₁.cons.b_error) (toRealVec cPZ₂.cons.b_error) i| := hL i
  show |(toRealMat (ConPolyZono.unionLowerA cPZ₁.cons.A cPZ₁.cons.b cPZ₂.cons.A cPZ₂.cons.b)
      *ᵥ Real.PolyZonotope.monomial (Real.ConPolyZono.unionLowerR cPZ₁.cons.R cPZ₂.cons.R) a) i
    - toReal (ConPolyZono.unionLowerB cPZ₁.cons.b cPZ₂.cons.b i)|
    ≤ |toReal (ConPolyZono.plusB cPZ₁.cons.b_error cPZ₂.cons.b_error i)|
  rw [ConPolyZono.toRealMat_unionLowerA,
      show toReal (ConPolyZono.unionLowerB cPZ₁.cons.b cPZ₂.cons.b i)
      = Real.ConPolyZono.unionLowerB (toRealVec cPZ₁.cons.b) (toRealVec cPZ₂.cons.b) i from
    congrFun (ConPolyZono.toRealVec_unionLowerB _ _) i,
    show toReal (ConPolyZono.plusB cPZ₁.cons.b_error cPZ₂.cons.b_error i)
      = Fin.append (toRealVec cPZ₁.cons.b_error) (toRealVec cPZ₂.cons.b_error) i from
    congrFun (toRealVec_append _ _) i]
  exact hL'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
