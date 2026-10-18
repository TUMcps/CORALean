module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Union
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionUpperHolds
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatUnionLowerA
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecUnionLowerB
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsSharedIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.Union

@[expose] public section

/-!
# The stored union's constraints hold wherever the exact union's do

At a factor vector in the cube where the exact union of the two read-back operands (`nominalCore`)
meets its selector rows exactly and its operand rows within the operands' slacks, the stored union
meets its own rows within theirs: the selector rows by `holds_unionUpper_of_real`, the operand rows
being the exact ones (`toRealMat_unionLowerA`, `toRealVec_unionLowerB`) with the same slacks.
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
    (h : ∀ i, |((Real.ConPolyZono.union cPZ₁.nominalCore cPZ₂.nominalCore).A
        *ᵥ Real.PolyZonotope.monomial
          (Real.ConPolyZono.union cPZ₁.nominalCore cPZ₂.nominalCore).R a) i
      - (Real.ConPolyZono.union cPZ₁.nominalCore cPZ₂.nominalCore).b i|
      ≤ |Fin.append (0 : Vec ℝ (1 + 1))
          (Fin.append (toRealVec cPZ₁.b_error) (toRealVec cPZ₂.b_error)) i|) : -- --- STMT ---
    (cPZ₁.union cPZ₂).satisfies a := by -- --- PROOF ---
  have hb : ∀ {m₁ m₂ : ℕ} (u : Vec 𝕋 m₁) (v : Vec 𝕋 m₂) (i : Fin (m₁ + m₂)),
      toReal (ConPolyZono.plusB u v i) = Fin.append (toRealVec u) (toRealVec v) i :=
    fun u v i => congrFun (ConPolyZono.toRealVec_plusB u v) i
  -- the exact rows, split into the selector block and the operands' block
  have hv := Real.ConPolyZono.mulVec_plusA_appendE (Real.ConPolyZono.unionUpperA cPZ₁.p cPZ₂.p)
    (Real.ConPolyZono.unionLowerA (toRealMat cPZ₁.A) (toRealVec cPZ₁.b) (toRealMat cPZ₂.A)
      (toRealVec cPZ₂.b)) (Real.ConPolyZono.unionUpperR cPZ₁.p cPZ₂.p)
    (Real.ConPolyZono.unionLowerR cPZ₁.R cPZ₂.R) a
  replace h : ∀ i : Fin (1 + 1 + (cPZ₁.m + cPZ₂.m)), |Fin.append
      (Real.ConPolyZono.unionUpperA cPZ₁.p cPZ₂.p
        *ᵥ Real.PolyZonotope.monomial (Real.ConPolyZono.unionUpperR cPZ₁.p cPZ₂.p) a)
      (Real.ConPolyZono.unionLowerA (toRealMat cPZ₁.A) (toRealVec cPZ₁.b) (toRealMat cPZ₂.A)
        (toRealVec cPZ₂.b) *ᵥ Real.PolyZonotope.monomial
          (Real.ConPolyZono.unionLowerR cPZ₁.R cPZ₂.R) a) i
      - Fin.append Real.ConPolyZono.unionUpperB
        (Real.ConPolyZono.unionLowerB (toRealVec cPZ₁.b) (toRealVec cPZ₂.b)) i|
      ≤ |Fin.append (0 : Vec ℝ (1 + 1))
          (Fin.append (toRealVec cPZ₁.b_error) (toRealVec cPZ₂.b_error)) i| := fun i => by
    rw [← hv]
    exact h i
  obtain ⟨hU, hL⟩ := (Real.ConPolyZono.forall_abs_sub_append_iff _ _ _ _ _ _).mp h
  -- the selector rows have no slack, so they hold exactly
  have hUholds : Real.ConPolyZono.holds (Real.ConPolyZono.unionUpperA cPZ₁.p cPZ₂.p)
      Real.ConPolyZono.unionUpperB (Real.ConPolyZono.unionUpperR cPZ₁.p cPZ₂.p) a := fun i => by
    have h0 := hU i
    rw [Pi.zero_apply, abs_zero] at h0
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
  -- the stored rows, split the same way
  intro i
  show |(toRealMat (ConPolyZono.plusA (ConPolyZono.unionUpperA cPZ₁.p cPZ₂.p)
      (ConPolyZono.unionLowerA cPZ₁.A cPZ₁.b cPZ₂.A cPZ₂.b)) *ᵥ Real.PolyZonotope.monomial
        (Real.ConPolyZono.appendE (Real.ConPolyZono.unionUpperR cPZ₁.p cPZ₂.p)
          (Real.ConPolyZono.unionLowerR cPZ₁.R cPZ₂.R)) a) i
    - toReal (ConPolyZono.plusB ConPolyZono.unionUpperB (ConPolyZono.unionLowerB cPZ₁.b cPZ₂.b) i)|
    ≤ |toReal (ConPolyZono.plusB (ConPolyZono.plusB (fun _ => (zero : 𝕋))
      (fun _ => ConPolyZono.unionConErr cPZ₁.p cPZ₂.p))
        (ConPolyZono.plusB cPZ₁.b_error cPZ₂.b_error) i)|
  rw [ConPolyZono.toRealMat_plusA, Real.ConPolyZono.mulVec_plusA_appendE, hb, hb,
    ConPolyZono.toRealVec_plusB, ConPolyZono.toRealVec_plusB, ConPolyZono.toRealMat_unionLowerA,
    ConPolyZono.toRealVec_unionLowerB]
  revert i
  refine (Real.ConPolyZono.forall_abs_sub_append_iff _ _ _ _ _ _).mpr ⟨fun i => ?_, hL⟩
  have hup := ConPolyZono.holds_unionUpper_of_real (𝕋 := 𝕋) cPZ₁.p cPZ₂.p a ha hUholds i
  rw [hb] at hup
  exact hup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
