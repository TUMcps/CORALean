module

public import CORALean.ContSet.SpectraShadow.Real.Operations.ArrowMat
public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportBound
public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ContainsPointZeroIff
public import CORALean.Global.LinProg.LinProg

@[expose] public section

/-!
# `ContSet/SpectraShadow/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==================================  `arrowMat_isHermitian`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {N : ℕ}

/-- `arrowMat s t w` has `w` in its first row and first column alike, so it is Hermitian. -/
theorem arrowMat_isHermitian (s t : ℝ) (w : Vec ℝ N) : (arrowMat s t w).IsHermitian := by
  -- each of the four cases of an entry
  ext p q
  refine Fin.cases ?_ (fun i => ?_) p <;> refine Fin.cases ?_ (fun j => ?_) q <;>
    simp [arrowMat, conjTranspose_apply, eq_comm]

end CORALean.Real


-- ==============================  `SpectraShadow.A₀_add_sum_eq`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- With every `Aᵢ` zero, the inequality does not depend on the coefficients. -/
theorem SpectraShadow.A₀_add_sum_eq {α : Type} [AddCommGroup α] [Module ℝ α] (S : SpectraShadow α)
    (β : Fin S.m → ℝ) (h : ∀ i, S.A i = 0) : S.A₀ + ∑ i, β i • S.A i = S.A₀ := by
  simp [h]

end CORALean.Real


-- ===========================  `SpectraShadow.containsPoint_of_mem`  =========================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- At any tolerance `tol ≥ 0` the point test never rejects a member of the set. -/
theorem SpectraShadow.containsPoint_of_mem (S : SpectraShadow α) {p : α}
    (hp : p ∈ S.construct) {tol : ℝ} (htol : 0 ≤ tol) : S.containsPoint p tol := by
  obtain ⟨β, s, h1, h2, h3⟩ := (S.containsPoint_zero_iff p).mpr hp
  exact ⟨β, s, h1, fun i => (h2 i).trans htol, h3⟩

end CORALean.Real


-- ==========================  `SpectraShadow.le_supportFunc_of_mem`  =========================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- Every point of the set is below the support function: it is a supremum. -/
theorem SpectraShadow.le_supportFunc_of_mem (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) {x : α}
    (hx : x ∈ S.construct) : ((c x : ℝ) : EReal) ≤ S.supportFunc c :=
  le_iSup₂ (f := fun x (_ : x ∈ S.construct) => ((c x : ℝ) : EReal)) x hx

end CORALean.Real


-- ==============================  `SpectraShadow.lmi_of_A_zero`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

omit [AddCommGroup α] [Module ℝ α] in
/-- Variables on zero coefficient matrices do not enter the inequality. -/
theorem SpectraShadow.lmi_of_A_zero (S : SpectraShadow α) (β : Fin S.m → ℝ)
    (h : ∀ i, β i = 0 ∨ S.A i = 0) : S.A₀ + ∑ i, β i • S.A i = S.A₀ := by
  rw [Finset.sum_eq_zero fun i _ => by rcases h i with h | h <;> simp [h], add_zero]

end CORALean.Real


-- =========================  `SpectraShadow.supportFunc_le_of_bound`  ========================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- A certified bound (`SupportBound`) is above the support function. -/
theorem SpectraShadow.supportFunc_le_of_bound (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ)
    (u : SupportBound S.construct c) : S.supportFunc c ≤ (u.val : EReal) :=
  iSup₂_le fun x hx => EReal.coe_le_coe_iff.mpr (u.le x hx)

end CORALean.Real


-- =======================  `SpectraShadow.supportFunc_le_supportBound`  ======================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- Weak duality: a dual certificate `Y` bounds the support function by `c(c₀) + tr(A₀ Y)`. -/
theorem SpectraShadow.supportFunc_le_supportBound (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ)
    (Y : Mat ℝ S.k S.k) (hY : Y.PosSemidef) (hc : ∀ i, (S.A i * Y).trace = - c (S.G i)) :
    S.supportFunc c ≤ ((c S.c + (S.A₀ * Y).trace : ℝ) : EReal) :=
  S.supportFunc_le_of_bound c (S.supportBound c Y hY hc)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
