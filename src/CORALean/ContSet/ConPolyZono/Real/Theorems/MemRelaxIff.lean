module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecRelax
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-!
# What `ConPolyZono.relax` denotes

The points of `cPZ` with each constraint row met to within `|sᵢ|`. A row of the result reads
`(A μ_R(α))ᵢ + sᵢ γᵢ = bᵢ`, the fresh factor's monomial being `γᵢ` itself and no other row or
generator reading it; `γᵢ = (bᵢ - (A μ_R(α))ᵢ) / sᵢ` is a slack in `[-1, 1]` exactly when the
row is met to within `|sᵢ|`, and `0` where `sᵢ = 0` and the row is an equation.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generator monomials ignore the slack factors. -/
theorem ConPolyZono.aux_monomial_relax (cPZ : ConPolyZono α) (s : Vec ℝ cPZ.m)
    (a : Fin (cPZ.p + cPZ.m) → ℝ) :
    PolyZonotope.monomial (cPZ.relax s).E a
      = PolyZonotope.monomial cPZ.E (fun k => a (Fin.castAdd cPZ.m k)) :=
  funext fun l => ConPolyZono.monomial_padE cPZ.E cPZ.m a l


-- =======================================  MAIN THEOREM  ======================================= --

/-- The relaxed set's points are the original's with every row met to within `|sᵢ|`. -/
theorem ConPolyZono.mem_relax_iff [AddCommGroup α] [Module ℝ α] (cPZ : ConPolyZono α)
    (s : Vec ℝ cPZ.m) {x : α} : -- --- STMT ---
    x ∈ (cPZ.relax s).construct ↔
      ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ (∀ i, |(cPZ.A *ᵥ PolyZonotope.monomial cPZ.R a) i - cPZ.b i| ≤ |s i|)
        ∧ x = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i
          + ∑ j, β j • cPZ.GI j := by -- --- PROOF ---
  constructor
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    refine ⟨fun k => a (Fin.castAdd cPZ.m k), β, fun k => ha _, hβ, fun i => ?_, ?_⟩
    · -- the row is off by `sᵢ γᵢ`, and `|γᵢ| ≤ 1`
      have h := hs i
      rw [ConPolyZono.mulVec_relax] at h
      have hrow : (cPZ.A *ᵥ PolyZonotope.monomial cPZ.R (fun k => a (Fin.castAdd cPZ.m k))) i
          - cPZ.b i = -(s i * a (Fin.natAdd cPZ.p i)) := by
        have hb : (cPZ.relax s).b i = cPZ.b i := rfl
        linarith
      rw [hrow, abs_neg, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (ha _)
    · rw [hx, ConPolyZono.aux_monomial_relax]
      rfl
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    -- the slack each row needs, `0` on a row with no room
    set γ : Fin cPZ.m → ℝ := fun i =>
      if s i = 0 then 0 else (cPZ.b i - (cPZ.A *ᵥ PolyZonotope.monomial cPZ.R a) i) / s i
    have hleft : (fun k => Fin.append a γ (Fin.castAdd cPZ.m k)) = a :=
      funext fun k => Fin.append_left a γ k
    have hbox : ∀ k, |Fin.append a γ k| ≤ 1 := by
      refine Fin.addCases (fun k => ?_) (fun i => ?_)
      · rw [Fin.append_left]
        exact ha k
      · rw [Fin.append_right]
        by_cases h0 : s i = 0
        · simp [γ, h0]
        · simp only [γ, if_neg h0, abs_div]
          rw [div_le_one (abs_pos.mpr h0), abs_sub_comm]
          exact hs i
    -- each row, its slack factor making up exactly what the row is off by
    have hrows : (cPZ.relax s).satisfies (Fin.append a γ) := by
      intro i
      rw [ConPolyZono.mulVec_relax, hleft, Fin.append_right]
      show _ = cPZ.b i
      by_cases h0 : s i = 0
      · have h := hs i
        rw [h0, abs_zero] at h
        have h' := abs_nonpos_iff.mp h
        simp only [γ, if_pos h0, mul_zero, add_zero]
        linarith
      · simp only [γ, if_neg h0]
        rw [mul_div_cancel₀ _ h0]
        linarith
    refine ⟨Fin.append a γ, β, hbox, hβ, hrows, ?_⟩
    rw [hx]
    show _ = cPZ.c + ∑ i, PolyZonotope.monomial (cPZ.relax s).E (Fin.append a γ) i • cPZ.G i
      + ∑ j, β j • cPZ.GI j
    rw [ConPolyZono.aux_monomial_relax, hleft]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
