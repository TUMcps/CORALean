module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.CartProdExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemRelaxIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalCartProd
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Relaxing a product is the product of the relaxed

`relax` of `cartProd`, at the two slack vectors side by side, denotes the product of the two
relaxed operands: the product's rows are each operand's at its own factors
(`PolyLevelSet.eval_cartProd`), so each block meets its rows within its own slack, and the point
splits as
in `cartProd_exact`. What a float product's nominal set is read through.

## Inputs
* `cPZ₁` – first factor
* `cPZ₂` – second factor
* `s₁` – slack of first
* `s₂` – slack of second

## Hypotheses
* none

## Conclusion
* relaxing the product gives the product of the relaxed sets
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Two blocks of rows side by side are each within their slack exactly when both blocks are. -/
theorem ConPolyZono.aux_forall_abs_sub_append_iff {m₁ m₂ : ℕ} (u₁ c₁ s₁ : Fin m₁ → ℝ)
    (u₂ c₂ s₂ : Fin m₂ → ℝ) :
    (∀ i, |Fin.append u₁ u₂ i - Fin.append c₁ c₂ i| ≤ |Fin.append s₁ s₂ i|)
      ↔ (∀ i, |u₁ i - c₁ i| ≤ |s₁ i|) ∧ ∀ i, |u₂ i - c₂ i| ≤ |s₂ i| :=
  ⟨fun h => ⟨fun i => by simpa using h (Fin.castAdd m₂ i),
      fun i => by simpa using h (Fin.natAdd m₁ i)⟩,
    fun ⟨h₁, h₂⟩ => Fin.addCases (fun i => by simpa using h₁ i) fun i => by simpa using h₂ i⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The product relaxed by the two slacks side by side is the product of the relaxed operands. -/
theorem ConPolyZono.relax_cartProd (cPZ₁ : ConPolyZono α) (cPZ₂ : ConPolyZono β)
    (s₁ : Vec ℝ cPZ₁.cons.m) (s₂ : Vec ℝ cPZ₂.cons.m) :
    ((cPZ₁.cartProd cPZ₂).relax (Fin.append s₁ s₂)).construct
      = (cPZ₁.relax s₁).construct ×ˢ (cPZ₂.relax s₂).construct := by -- --- PROOF ---
  -- `Fin.sum_univ_add` at the product's generator counts, through the projections
  have hh : ∀ f : Fin (cPZ₁.h + cPZ₂.h) → α × β, ∑ i : Fin (cPZ₁.cartProd cPZ₂).h, f i
      = ∑ i, f (Fin.castAdd cPZ₂.h i) + ∑ i, f (Fin.natAdd cPZ₁.h i) := fun f => Fin.sum_univ_add f
  have hq : ∀ f : Fin (cPZ₁.qI + cPZ₂.qI) → α × β, ∑ j : Fin (cPZ₁.cartProd cPZ₂).qI, f j
      = ∑ j, f (Fin.castAdd cPZ₂.qI j) + ∑ j, f (Fin.natAdd cPZ₁.qI j) :=
    fun f => Fin.sum_univ_add f
  ext ⟨x₁, x₂⟩
  rw [ConPolyZono.mem_relax_iff, Set.mem_prod, ConPolyZono.mem_relax_iff,
    ConPolyZono.mem_relax_iff]
  -- the product's rows, each block at its own factors
  have hrows : ∀ a : Fin (cPZ₁.p + cPZ₂.p) → ℝ,
      (cPZ₁.cartProd cPZ₂).cons.A *ᵥ PolyZonotope.monomial (cPZ₁.cartProd cPZ₂).cons.R a
        - (cPZ₁.cartProd cPZ₂).cons.b
      = Fin.append (cPZ₁.cons.A
          *ᵥ PolyZonotope.monomial cPZ₁.cons.R (fun k => a (Fin.castAdd cPZ₂.p k))
          - cPZ₁.cons.b) (cPZ₂.cons.A
              *ᵥ PolyZonotope.monomial cPZ₂.cons.R (fun k => a (Fin.natAdd cPZ₁.p k))
          - cPZ₂.cons.b) := fun a => PolyLevelSet.eval_cartProd cPZ₁.cons cPZ₂.cons a
  -- so the rows are within the two slacks exactly when each block is within its own
  have hsplit : ∀ a : Fin (cPZ₁.p + cPZ₂.p) → ℝ,
      (∀ i, |((cPZ₁.cartProd cPZ₂).cons.A *ᵥ PolyZonotope.monomial (cPZ₁.cartProd cPZ₂).cons.R a) i
        - (cPZ₁.cartProd cPZ₂).cons.b i| ≤ |Fin.append s₁ s₂ i|)
      ↔ (∀ i, |(cPZ₁.cons.A
          *ᵥ PolyZonotope.monomial cPZ₁.cons.R (fun k => a (Fin.castAdd cPZ₂.p k))) i
          - cPZ₁.cons.b i| ≤ |s₁ i|)
        ∧ ∀ i, |(cPZ₂.cons.A
            *ᵥ PolyZonotope.monomial cPZ₂.cons.R (fun k => a (Fin.natAdd cPZ₁.p k))) i
          - cPZ₂.cons.b i| ≤ |s₂ i| := fun a => by
    have h := ConPolyZono.aux_forall_abs_sub_append_iff
      (cPZ₁.cons.A *ᵥ PolyZonotope.monomial cPZ₁.cons.R (fun k => a (Fin.castAdd cPZ₂.p k))
          - cPZ₁.cons.b) 0 s₁
      (cPZ₂.cons.A *ᵥ PolyZonotope.monomial cPZ₂.cons.R (fun k => a (Fin.natAdd cPZ₁.p k))
          - cPZ₂.cons.b) 0 s₂
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero] at h
    rw [← h]
    refine forall_congr' fun i => ?_
    rw [← Pi.sub_apply, hrows a]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  constructor
  -- a point of the relaxed product splits into a point of each relaxed operand
  · rintro ⟨a, β, ha, hβ, hs, hxy⟩
    obtain ⟨hs₁, hs₂⟩ := (hsplit a).mp hs
    have hx₁ : x₁ = cPZ₁.c + ∑ i, PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) i
              • cPZ₁.G i + ∑ j, β (Fin.castAdd cPZ₂.qI j) • cPZ₁.GI j := by
      have h1 := congrArg Prod.fst hxy
      rw [hh, hq] at h1
      simpa only [ConPolyZono.cartProd, PolyZonotope.monomial_plusE_left,
        PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right, Prod.fst_add,
        Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero, add_zero] using h1
    have hx₂ : x₂ = cPZ₂.c + ∑ i, PolyZonotope.monomial cPZ₂.E (fun k => a (Fin.natAdd cPZ₁.p k)) i
              • cPZ₂.G i + ∑ j, β (Fin.natAdd cPZ₁.qI j) • cPZ₂.GI j := by
      have h2 := congrArg Prod.snd hxy
      rw [hh, hq] at h2
      simpa only [ConPolyZono.cartProd, PolyZonotope.monomial_plusE_left,
        PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right, Prod.snd_add,
        Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add] using h2
    exact ⟨⟨fun k => a (Fin.castAdd cPZ₂.p k), fun j => β (Fin.castAdd cPZ₂.qI j),
              fun k => ha _, fun j => hβ _, hs₁, hx₁⟩,
           ⟨fun k => a (Fin.natAdd cPZ₁.p k), fun j => β (Fin.natAdd cPZ₁.qI j),
              fun k => ha _, fun j => hβ _, hs₂, hx₂⟩⟩
  -- back: appended factors and appended coefficients, each read on its own half
  · rintro ⟨⟨a₁, β₁, ha₁, hβ₁, hs₁, hx₁⟩, ⟨a₂, β₂, ha₂, hβ₂, hs₂, hx₂⟩⟩
    have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd cPZ₂.p k)) = a₁ :=
      funext fun k => Fin.append_left a₁ a₂ k
    have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd cPZ₁.p k)) = a₂ :=
      funext fun k => Fin.append_right a₁ a₂ k
    refine ⟨Fin.append a₁ a₂, Fin.append β₁ β₂,
      Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
      Fin.addCases (fun j => by simpa using hβ₁ j) (fun j => by simpa using hβ₂ j),
      (hsplit _).mpr ⟨by rw [hA₁]; exact hs₁, by rw [hA₂]; exact hs₂⟩, ?_⟩
    rw [hh, hq]
    simp only [ConPolyZono.cartProd, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
    refine Prod.ext ?_ ?_
    · simpa only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
        add_zero] using hx₁
    · simpa only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
        zero_add] using hx₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
