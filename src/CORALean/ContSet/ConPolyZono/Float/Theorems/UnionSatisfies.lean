module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Union
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionUpper
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConInt
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpper
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemAndRowsIff
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
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
`aux_holds_unionUpper_of_real`, the operand rows being the exact ones
(`aux_eval_nominalCore_unionLower`) with the same slacks.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand
* `a` – factor vector

## Hypotheses
* `ha` – factors are within the unit interval
* `h` – exact union constraint holds up to the slack

## Conclusion
* the factor vector satisfies the result's constraint
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

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The integer selector row is the exact one, scaled. -/
private theorem ConPolyZono.aux_unionConInt_eq (p₁ p₂ : ℕ)
    (l : Fin (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂))))) : -- --- CONCL ---
    (4 * ((max 1 p₁ : ℕ) : ℝ) * ((max 1 p₂ : ℕ) : ℝ)) * Real.ConPolyZono.unionConCoef p₁ p₂ l
      = (ConPolyZono.unionConInt p₁ p₂ l : ℝ) := by -- --- PROOF ---
  -- the cases `max` resolves to the count itself, which a column's existence forces
  have h1 : ∀ _ : Fin p₁, ((max 1 p₁ : ℕ) : ℝ) = p₁ := fun j => by
    rw [max_eq_right (by have := j.pos; omega)]
  have h2 : ∀ _ : Fin p₂, ((max 1 p₂ : ℕ) : ℝ) = p₂ := fun j => by
    rw [max_eq_right (by have := j.pos; omega)]
  -- the two leading columns, then the four groups in turn
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · fin_cases l <;> simp [ConPolyZono.unionConInt, Real.ConPolyZono.unionConCoef]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · -- the groups over the first operand's factors
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      have hp : (0 : ℝ) < p₁ := by exact_mod_cast j.pos
      simp only [ConPolyZono.unionConInt, Real.ConPolyZono.unionConCoef, Fin.append_left,
        Fin.append_right, h1 j]
      push_cast
      field_simp
      ring
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      have hp : (0 : ℝ) < p₂ := by exact_mod_cast j.pos
      simp only [ConPolyZono.unionConInt, Real.ConPolyZono.unionConCoef, Fin.append_left,
        Fin.append_right, h2 j]
      push_cast
      field_simp
      ring
  · -- the cross group: both counts positive, as the column indexes a product
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      have hpq : 0 < p₁ * p₂ := j.pos
      have hp1 : 0 < p₁ := Nat.pos_of_mul_pos_right hpq
      have hq1 : 0 < p₂ := Nat.pos_of_mul_pos_left hpq
      have hp : (0 : ℝ) < p₁ := by exact_mod_cast hp1
      have hq : (0 : ℝ) < p₂ := by exact_mod_cast hq1
      rw [max_eq_right (by omega : 1 ≤ p₁), max_eq_right (by omega : 1 ≤ p₂)]
      simp only [ConPolyZono.unionConInt, Real.ConPolyZono.unionConCoef, Fin.append_left,
        Fin.append_right]
      push_cast
      field_simp


/-- The stored row's value is within the summed gaps of the integer row's. -/
private theorem ConPolyZono.aux_unionCon_close (p₁ p₂ : ℕ) (a : Fin (p₁ + p₂ + 2) → ℝ)
    (ha : ∀ k, |a k| ≤ 1) : -- --- CONCL ---
    |(∑ l, toReal (ConPolyZono.unionConCoef p₁ p₂ l : 𝕋)
          * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k)
      - ∑ l, (ConPolyZono.unionConInt p₁ p₂ l : ℝ)
          * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k|
      ≤ toReal (ConPolyZono.unionConErr p₁ p₂ : 𝕋) := by -- --- PROOF ---
  have hgap : ∀ l, |(toReal (ConPolyZono.unionConCoef p₁ p₂ l : 𝕋)
        - (ConPolyZono.unionConInt p₁ p₂ l : ℝ))|
      ≤ toReal (subUp (intUp (ConPolyZono.unionConInt p₁ p₂ l))
        (intDown (ConPolyZono.unionConInt p₁ p₂ l)) : 𝕋) := fun l => by
    obtain ⟨h1, h2⟩ := intDown_le_intUp (𝕋 := 𝕋) (ConPolyZono.unionConInt p₁ p₂ l)
    have h3 := sub_le_subUp (intUp (ConPolyZono.unionConInt p₁ p₂ l) : 𝕋)
      (intDown (ConPolyZono.unionConInt p₁ p₂ l))
    rw [abs_le]
    constructor <;> simp only [ConPolyZono.unionConCoef] <;> linarith
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun l _ => ?_)
    (sum_le_sumUp _))
  rw [← sub_mul, abs_mul]
  exact le_trans (mul_le_of_le_one_right (abs_nonneg _)
    (Real.PolyZonotope.abs_monomial_le_one
      (fun k l => Real.ConPolyZono.unionConCol p₁ p₂ l k) ha l))
    (hgap l)


/-- The stored selector rows hold wherever the exact ones do. -/
private theorem ConPolyZono.aux_holds_unionUpper_of_real (p₁ p₂ : ℕ) (a : Fin (p₁ + p₂ + 2) → ℝ)
    (ha : ∀ k, |a k| ≤ 1) (h : a ∈ (Real.ConPolyZono.unionUpper p₁ p₂).construct) : -- --- CONCL ---
    a ∈ (ConPolyZono.unionUpper (𝕋 := 𝕋) p₁ p₂).construct := by -- --- PROOF ---
  -- both stacks split into their two rows, each an equation
  rw [Real.ConPolyZono.unionUpper, Real.PolyLevelSet.mem_andRows_iff,
    Real.PolyLevelSet.mem_construct_iff_of_eq fun _ => rfl] at h
  obtain ⟨⟨-, h₁⟩, h₂⟩ := h
  rw [ConPolyZono.unionUpper, PolyLevelSet.mem_andRows_iff]
  refine ⟨(PolyLevelSet.mem_construct_iff_of_eq fun _ => rfl).mpr
      ⟨(Interval.mem_unit_iff a).mpr ha, fun i => ?_⟩,
    fun i => ((PolyLevelSet.mem_construct_iff_of_eq (P := ConPolyZono.unionConRow (𝕋 := 𝕋) p₁ p₂)
      fun _ => rfl).mpr ⟨(Interval.mem_unit_iff a).mpr ha, fun i => ?_⟩).2 i⟩
  · -- the `α₁α₂ = 1` row is copied, its entry `one` reading back as `1`, and holds exactly
    have hA : toRealMat (fun (_ : Fin 1) (_ : Fin 1) => (one : 𝕋)) = fun _ _ => 1 :=
      funext fun _ => funext fun _ => toReal_one
    have h1 : ((fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) *ᵥ
        Real.PolyZonotope.monomial (Real.ConPolyZono.unionSelRow p₁ p₂).R a) i = 1 := h₁ i
    show |(toRealMat (fun (_ : Fin 1) (_ : Fin 1) => (one : 𝕋)) *ᵥ
      Real.PolyZonotope.monomial (Real.ConPolyZono.unionSelRow p₁ p₂).R a) i - toReal (one : 𝕋)|
      ≤ |toReal (zero : 𝕋)|
    rw [hA, h1]
    simp [toReal_one, toReal_zero]
  · -- the selector row: the integer row's value is zero, the stored one within `unionConErr`
    have h0 : (∑ l, Real.ConPolyZono.unionConCoef p₁ p₂ l
        * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k) = 0 := by
      have h := h₂ i
      change ((fun _ l => Real.ConPolyZono.unionConCoef p₁ p₂ l) *ᵥ Real.PolyZonotope.monomial
        (fun k l => Real.ConPolyZono.unionConCol p₁ p₂ l k) a - 0) i = 0 at h
      rw [Pi.sub_apply, Pi.zero_apply, sub_zero] at h
      exact h
    -- the integer row's value is the exact row's, scaled, hence zero
    have hz : (∑ l, (ConPolyZono.unionConInt p₁ p₂ l : ℝ)
        * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k) = 0 := by
      have hs : (∑ l, (ConPolyZono.unionConInt p₁ p₂ l : ℝ)
          * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k)
          = (4 * ((max 1 p₁ : ℕ) : ℝ) * ((max 1 p₂ : ℕ) : ℝ))
            * ∑ l, Real.ConPolyZono.unionConCoef p₁ p₂ l
              * ∏ k, a k ^ Real.ConPolyZono.unionConCol p₁ p₂ l k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by
          rw [← ConPolyZono.aux_unionConInt_eq, mul_assoc]
      rw [hs, h0, mul_zero]
    -- the stored row is within `unionConErr` of it
    have hc := ConPolyZono.aux_unionCon_close (𝕋 := 𝕋) p₁ p₂ a ha
    rw [hz, sub_zero] at hc
    simp only [ConPolyZono.unionConRow, toReal_zero, sub_zero,
      Matrix.mulVec, dotProduct, Real.PolyZonotope.monomial, toRealMat]
    exact hc.trans (le_abs_self _)

end


/-- The stored operand rows, read back, are the exact layer's at the read-back operands. -/
private theorem ConPolyZono.aux_eval_nominalCore_unionLower {p₁ p₂ : ℕ} (P₁ : PolyLevelSet 𝕋 p₁)
    (P₂ : PolyLevelSet 𝕋 p₂) (a : Fin (p₁ + p₂ + 2) → ℝ) : -- --- CONCL ---
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
            (toRealVec cPZ₂.cons.b_error)) i|) : -- --- CONCL ---
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
  -- the stored union: selector rows by `aux_holds_unionUpper_of_real`, operand rows read back
  show a ∈ ((ConPolyZono.unionUpper cPZ₁.p cPZ₂.p).andRows
    (ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons)).construct
  rw [PolyLevelSet.mem_andRows_iff]
  refine ⟨ConPolyZono.aux_holds_unionUpper_of_real cPZ₁.p cPZ₂.p a ha hUmem, fun i => ?_⟩
  rw [show (ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons).op i = .eq from
    Real.LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq i]
  -- the operand rows, the exact ones at the read-back entries, with the same slacks
  show |(ConPolyZono.unionLower cPZ₁.cons cPZ₂.cons).nominalCore.eval a i|
    ≤ |toReal (Fin.append cPZ₁.cons.b_error cPZ₂.cons.b_error i)|
  rw [ConPolyZono.aux_eval_nominalCore_unionLower]
  exact (hL i).trans_eq (congrArg abs (congrFun (toRealVec_append _ _) i).symm)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
