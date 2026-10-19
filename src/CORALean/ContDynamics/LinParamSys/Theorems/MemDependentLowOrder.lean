module

public import CORALean.ContDynamics.LinParamSys.Operations.DependentLowOrder
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The corrected `R_lowOrder` holds the dependent low orders

`LinParamSys.mem_dependentLowOrder`: at `A = A_c + G`, `G = Σ pᵢ A_g⁽ⁱ⁾`, `u = U_c + w`,
`w = Σ pᵢ U_G⁽ⁱ⁾`, the orders `(I + A r + A² r²/2) c + (I r + A r²/2 + A² r³/6) u` split by
degree in `(G, w)` (`aux_lowOrder_split`); each degree is a sum over the parameters' indices
(`aux_lowOrder_first`, `…_second`, `…_third`), the pairs folded into their diagonal and their
`i < j` halves (`aux_lowOrder_diag_add`), the squares into a center and a generator
(`aux_lowOrder_sq_split`). The coefficients are the monomials `pᵢ`, `2pᵢ² - 1`, `pᵢpⱼ`,
`pᵢpⱼpₗ`, all in `[-1, 1]`.

What `dependentHomSolLowOrder_counterexample` shows CORA's `R_lowOrder` misses is exactly
what the second and third degree here hold.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Σᵢ Σⱼ` of a pair function, its diagonal and its `i < j` pairs. -/
theorem aux_lowOrder_diag_add {V : Type} [AddCommGroup V] (f : Fin k → Fin k → V) :
    ∑ i, ∑ j, f i j = ∑ i, f i i
      + ∑ ij : Fin k × Fin k,
          (if ij.1 < ij.2 then f ij.1 ij.2 + f ij.2 ij.1 else 0) := by -- --- PROOF ---
  -- each pair below, on or above the diagonal
  have hsplit : ∀ i j, f i j = (if i < j then f i j else 0) + (if i = j then f i j else 0)
      + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hdiag : ∑ i, ∑ j, (if i = j then f i j else 0) = ∑ i, f i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]; simp
  have hlow : ∑ i, ∑ j, (if j < i then f i j else 0)
      = ∑ i, ∑ j, (if i < j then f j i else 0) := Finset.sum_comm
  -- the pairs below the diagonal, swapped, join those above
  rw [Fintype.sum_prod_type]
  simp only [ite_add_zero] at *
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if i = j then f i j else 0)
          + (if j < i then f i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = _ := by
        simp only [Finset.sum_add_distrib, hdiag, hlow]
        rw [add_comm (∑ i, ∑ j, if i < j then f i j else 0) (∑ i, f i i), add_assoc]


/-- The flow's orders up to `A²`, at `A = A_c + G` and `u = U_c + w`, split by degree in
`(G, w)`. -/
theorem aux_lowOrder_split (Ac G : Mat ℝ n n) (c Uc w : Vec ℝ n) (r : ℝ) : -- --- CONCL ---
    c + r • ((Ac + G) *ᵥ c) + (r ^ 2 / 2) • ((Ac + G) *ᵥ ((Ac + G) *ᵥ c))
      + (r • (Uc + w) + (r ^ 2 / 2) • ((Ac + G) *ᵥ (Uc + w))
        + (r ^ 3 / 6) • ((Ac + G) *ᵥ ((Ac + G) *ᵥ (Uc + w))))
    = (c + r • (Ac *ᵥ c) + (r ^ 2 / 2) • (Ac *ᵥ (Ac *ᵥ c)) + r • Uc + (r ^ 2 / 2) • (Ac *ᵥ Uc)
        + (r ^ 3 / 6) • (Ac *ᵥ (Ac *ᵥ Uc)))
      + (r • (G *ᵥ c) + (r ^ 2 / 2) • (Ac *ᵥ (G *ᵥ c) + G *ᵥ (Ac *ᵥ c))
        + (r ^ 2 / 2) • (G *ᵥ Uc) + (r ^ 3 / 6) • (Ac *ᵥ (G *ᵥ Uc) + G *ᵥ (Ac *ᵥ Uc))
        + r • w + (r ^ 2 / 2) • (Ac *ᵥ w) + (r ^ 3 / 6) • (Ac *ᵥ (Ac *ᵥ w)))
      + ((r ^ 2 / 2) • (G *ᵥ (G *ᵥ c)) + (r ^ 3 / 6) • (G *ᵥ (G *ᵥ Uc))
        + (r ^ 2 / 2) • (G *ᵥ w) + (r ^ 3 / 6) • (Ac *ᵥ (G *ᵥ w) + G *ᵥ (Ac *ᵥ w)))
      + (r ^ 3 / 6) • (G *ᵥ (G *ᵥ w)) := by -- --- PROOF ---
  simp only [Matrix.add_mulVec, Matrix.mulVec_add]
  module

/-- The first-degree part, generator by generator. -/
theorem aux_lowOrder_first (Ac : Mat ℝ n n) (Ag : Fin k → Mat ℝ n n) (c Uc : Vec ℝ n)
    (UG : Fin k → Vec ℝ n) (r : ℝ) (p : Fin k → ℝ) {G : Mat ℝ n n} {w : Vec ℝ n}
    (hG : ∀ v, G *ᵥ v = ∑ i, p i • (Ag i *ᵥ v)) (hw : w = ∑ i, p i • UG i) : -- --- CONCL ---
    r • (G *ᵥ c) + (r ^ 2 / 2) • (Ac *ᵥ (G *ᵥ c) + G *ᵥ (Ac *ᵥ c))
        + (r ^ 2 / 2) • (G *ᵥ Uc) + (r ^ 3 / 6) • (Ac *ᵥ (G *ᵥ Uc) + G *ᵥ (Ac *ᵥ Uc))
        + r • w + (r ^ 2 / 2) • (Ac *ᵥ w) + (r ^ 3 / 6) • (Ac *ᵥ (Ac *ᵥ w))
      = ∑ i, p i • ((r • Ag i + (r ^ 2 / 2) • (Ac * Ag i) + (r ^ 2 / 2) • (Ag i * Ac)) *ᵥ c
          + ((r ^ 2 / 2) • Ag i + (r ^ 3 / 6) • (Ac * Ag i) + (r ^ 3 / 6) • (Ag i * Ac)) *ᵥ Uc
          + (r • 1 + (r ^ 2 / 2) • Ac + (r ^ 3 / 6) • (Ac * Ac)) *ᵥ UG i) := by -- --- PROOF ---
  simp only [hG, hw, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  module

/-- The second-degree part, over all ordered pairs. -/
theorem aux_lowOrder_second (Ac : Mat ℝ n n) (Ag : Fin k → Mat ℝ n n) (c Uc : Vec ℝ n)
    (UG : Fin k → Vec ℝ n) (r : ℝ) (p : Fin k → ℝ) {G : Mat ℝ n n} {w : Vec ℝ n}
    (hG : ∀ v, G *ᵥ v = ∑ i, p i • (Ag i *ᵥ v)) (hw : w = ∑ i, p i • UG i) : -- --- CONCL ---
    (r ^ 2 / 2) • (G *ᵥ (G *ᵥ c)) + (r ^ 3 / 6) • (G *ᵥ (G *ᵥ Uc))
        + (r ^ 2 / 2) • (G *ᵥ w) + (r ^ 3 / 6) • (Ac *ᵥ (G *ᵥ w) + G *ᵥ (Ac *ᵥ w))
      = ∑ i, ∑ j, (p i * p j) • ((r ^ 2 / 2) • (Ag i *ᵥ (Ag j *ᵥ c))
          + (r ^ 3 / 6) • (Ag i *ᵥ (Ag j *ᵥ Uc)) + (r ^ 2 / 2) • (Ag i *ᵥ UG j)
          + (r ^ 3 / 6) • (Ac *ᵥ (Ag i *ᵥ UG j) + Ag i *ᵥ (Ac *ᵥ UG j))) := by -- --- PROOF ---
  simp only [hG, hw, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Finset.smul_sum, ← Finset.sum_add_distrib, smul_add, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

/-- The third-degree part, over all ordered triples. -/
theorem aux_lowOrder_third (Ag : Fin k → Mat ℝ n n) (UG : Fin k → Vec ℝ n) (r : ℝ)
    (p : Fin k → ℝ) {G : Mat ℝ n n} {w : Vec ℝ n}
    (hG : ∀ v, G *ᵥ v = ∑ i, p i • (Ag i *ᵥ v)) (hw : w = ∑ i, p i • UG i) : -- --- CONCL ---
    (r ^ 3 / 6) • (G *ᵥ (G *ᵥ w))
      = ∑ t : Fin k × Fin k × Fin k,
          (p t.1 * p t.2.1 * p t.2.2) •
            ((r ^ 3 / 6) • (Ag t.1 *ᵥ (Ag t.2.1 *ᵥ UG t.2.2))) := by -- --- PROOF ---
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp only [hG, hw, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  congr 1; ring


/-- `pᵢ² f = f/2 + (2pᵢ² - 1) f/2`, the square's range `[0, 1]` as a center and a generator. -/
theorem aux_lowOrder_sq_split {V : Type} [AddCommGroup V] [Module ℝ V] (p : Fin k → ℝ)
    (f : Fin k → V) :
    ∑ i, (p i * p i) • f i
      = ∑ i, (1 / 2 : ℝ) • f i + ∑ i, (2 * p i ^ 2 - 1) • (1 / 2 : ℝ) • f i := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← add_smul]
  congr 1; ring

/-- Four groups of a sum, the second's halves moved. -/
theorem aux_lowOrder_regroup {V : Type} [AddCommGroup V] (a b c d e f : V) :
    a + b + ((c + d) + e) + f = (a + c) + (((b + d) + e) + f) := by abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- The flow's time orders up to `A²` from `c`, at every parameter `p ∈ [-1, 1]ᵏ` of
the system matrix and the input, lie in the corrected `R_lowOrder`. -/
theorem LinParamSys.mem_dependentLowOrder (Ac : Mat ℝ n n) (Ag : Fin k → Mat ℝ n n)
    (c Uc : Vec ℝ n) (UG : Fin k → Vec ℝ n) (r : ℝ) {p : Fin k → ℝ}
    (hp : ∀ i, |p i| ≤ 1) : -- --- CONCL ---
    let A := Ac + ∑ i, p i • Ag i
    let u := Uc + ∑ i, p i • UG i
    c + r • (A *ᵥ c) + (r ^ 2 / 2) • (A *ᵥ (A *ᵥ c))
      + (r • u + (r ^ 2 / 2) • (A *ᵥ u) + (r ^ 3 / 6) • (A *ᵥ (A *ᵥ u)))
      ∈ (LinParamSys.dependentLowOrder Ac Ag c Uc UG r).construct := by -- --- PROOF ---
  intro A u
  set G := ∑ i, p i • Ag i with hGdef
  set w := ∑ i, p i • UG i with hwdef
  have hG : ∀ v, G *ᵥ v = ∑ i, p i • (Ag i *ᵥ v) := fun v => by
    simp only [hGdef, Matrix.sum_mulVec, Matrix.smul_mulVec]
  rw [aux_lowOrder_split, aux_lowOrder_first Ac Ag c Uc UG r p hG hwdef,
    aux_lowOrder_second Ac Ag c Uc UG r p hG hwdef, aux_lowOrder_third Ag UG r p hG hwdef,
    aux_lowOrder_diag_add]
  -- the monomials' values, each in `[-1, 1]`
  have hp2 : ∀ i, |2 * p i ^ 2 - 1| ≤ 1 := fun i => by
    have h := abs_le.mp (hp i)
    rw [abs_le]; constructor <;> nlinarith
  have hpp : ∀ i j, |p i * p j| ≤ 1 := fun i j => by
    rw [abs_mul]; exact mul_le_one₀ (hp i) (abs_nonneg _) (hp j)
  have hppp : ∀ i j l, |p i * p j * p l| ≤ 1 := fun i j l => by
    rw [abs_mul]; exact mul_le_one₀ (hpp i j) (abs_nonneg _) (hp l)
  let e3 : Fin (k * (k * k)) ≃ Fin k × Fin k × Fin k :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)
  refine ⟨Fin.append (Fin.append (Fin.append p (fun i => 2 * p i ^ 2 - 1))
      (fun l => p (finProdFinEquiv.symm l).1 * p (finProdFinEquiv.symm l).2))
      (fun l => p (e3 l).1 * p (e3 l).2.1 * p (e3 l).2.2), ?_, ?_⟩
  · refine Fin.addCases (Fin.addCases (Fin.addCases ?_ ?_) ?_) ?_ <;> intro l <;>
      simp only [Fin.append_left, Fin.append_right] <;>
      first | exact hp l | exact hp2 l | exact hpp _ _ | exact hppp _ _ _
  -- the point, generator block by generator block
  · show _ = (LinParamSys.dependentLowOrder Ac Ag c Uc UG r).c
      + ∑ j, _ • (LinParamSys.dependentLowOrder Ac Ag c Uc UG r).G j
    unfold LinParamSys.dependentLowOrder
    dsimp only
    rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    -- the squares split, the pairs and triples reindexed as the generators are
    rw [aux_lowOrder_sq_split, ← Equiv.sum_comp finProdFinEquiv.symm, ← Equiv.sum_comp e3]
    conv_lhs => rw [aux_lowOrder_regroup]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_)
      (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_) ?_)
    -- order zero, CORA's `R_c` before the squares' halves
    · simp only [Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.mulVec_smul,
        ← Matrix.mulVec_mulVec]
      module
    -- the squares' halves, in the center and as generators
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    -- the pairs `i < j`, both orders in one generator
    · refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs
      · simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
        module
      · simp
    -- the triples
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
      rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
