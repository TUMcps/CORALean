module

public import CORALean.HybridDynamics.Definitions.HitEnclosure
public import CORALean.HybridDynamics.Definitions.HitSet
public import CORALean.HybridDynamics.Theorems.HitHessianNumEqHitHessianMatZono
public import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapMatZonoOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.UnitIntervalMulOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.HybridDynamics.Theorems.HitPointAddEq
public import CORALean.HybridDynamics.Theorems.HitFactorMemIcc

@[expose] public section

/-!
# `R_g` encloses every `R_h(x₀)`, with `Θ/Λ` enclosed as a vector

[1, Sec. 5.4]: `R_g = y_h(ξ) ⊕ L ⊗ (R(0) ⊕ (−ξ)) ⊕ ½[φ̲, φ̄] ⊗ R_quad ⊕ R_{h,E}(R(0))` holds the
set `R_h(x₀)` of eq. (15) for every `x₀ ∈ R(0)`, given `Λ ≠ 0` on `R(0)`, `ξ ∈ R(0)`, `[φ̲, φ̄]`
holding `1/Λ(x₀)²`, and `ψ_c`, `ψ_g` enclosing `Θ(x₀)/Λ(x₀)` as vectors (one factor for all
coordinates). The paper's route, `Prop. 3` per coordinate, puts each remainder at its own Lagrange
point, which `R_quad` and the single `[φ̲, φ̄]` do not hold together. The proof goes another way:
with `ν = x₀ − ξ` the remainder is exact and shared (`hitPoint_add_eq`), `Q⁽ⁱ⁾(ξ)` is one point of
all the matrix zonotopes (`hitHessianNum_eq_hitHessianMatZono`), and `φ` is the geometric mean of
`1/Λ(ξ)²` and `1/Λ(x₀)²`.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `E` – flow error set
* `R₀` – initial zonotope
* `ξ` – expansion point
* `ψc` – center of the coefficient enclosure
* `ψg` – generator of the coefficient enclosure
* `φlo` – lower bound of the factor
* `φhi` – upper bound of the factor
* `x₀` – state

## Hypotheses
* `hΛ` – flow does not run parallel to the guard on the set
* `hφ` – the bounds hold on the set
* `hψ` – the coefficient enclosure holds on the set
* `hξ` – expansion point lies in the set
* `hx₀` – state lies in the set

## Conclusion
* the hit set lies in the hit enclosure

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.4]: `R_h(x₀) ⊆ R_g` for every `x₀ ∈ R(0)`, with `Θ/Λ ∈ ψ_c ⊕ [-1, 1]ψ_g` as a
vector on `R(0)`. -/
theorem GuardMap.hitSet_subset_hitEnclosure (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ)
    (E : Set (Vec ℝ n)) (R₀ : Real.Zonotope (Vec ℝ n)) (ξ ψc ψg : Vec ℝ n) (φlo φhi : ℝ)
    (hΛ : ∀ x ∈ R₀.construct, nv ⬝ᵥ (A *ᵥ x + b) ≠ 0)
    (hφ : ∀ x ∈ R₀.construct, φlo ≤ 1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ∧
      1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ≤ φhi)
    (hψ : ∀ x ∈ R₀.construct, ∃ κ : ℝ, |κ| ≤ 1 ∧ (nv ⬝ᵥ (A *ᵥ x + b))⁻¹ •
      (-((nv ⬝ᵥ (A *ᵥ x + b)) • nv) - (d - nv ⬝ᵥ x) • (nv ᵥ* A)) = ψc + κ • ψg)
    (hξ : ξ ∈ R₀.construct) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ R₀.construct) : -- --- CONCL ---
    GuardMap.hitSet A b nv d E x₀
      ⊆ GuardMap.hitEnclosure A b nv d E R₀ ξ ψc ψg φlo φhi := by -- --- PROOF ---
  rintro _ ⟨_, rfl, w, ⟨_, ⟨e, he, rfl⟩, e', he', rfl⟩, rfl⟩
  have hΛξ := hΛ ξ hξ
  have hΛx := hΛ x₀ hx₀
  obtain ⟨κ, hκ, hψξ⟩ := hψ ξ hξ
  obtain ⟨βξ, hβξ, hξeq⟩ := hξ
  obtain ⟨βx, hβx, hxeq⟩ := hx₀
  set ν : Vec ℝ n := x₀ - ξ with hν
  have hx₀ν : x₀ = ξ + ν := by rw [hν]; abel
  set Q := GuardMap.hitHessianMatZono A b nv d R₀ ψc ψg with hQdef
  set φ : ℝ := 1 / ((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ x₀ + b))) with hφdef
  set q : Vec ℝ n := fun i => ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν) with hqdef
  -- the exact expansion of `y_h(x₀)` around `ξ`
  have hexp := GuardMap.hitPoint_add_eq A b nv d ξ ν hΛξ (by rw [← hx₀ν]; exact hΛx)
  rw [← hx₀ν] at hexp
  -- `ν ∈ R(0) ⊕ (−ξ)`
  have hνmem : ν ∈ (⟨R₀.h, R₀.c - ξ, R₀.G⟩ : Real.Zonotope (Vec ℝ n)).construct := by
    refine ⟨βx, hβx, ?_⟩
    show x₀ - ξ = (R₀.c - ξ) + ∑ j, βx j • R₀.G j
    rw [hxeq]; abel
  -- `Q⁽ⁱ⁾(ξ)` with the factors of `ξ`, shared by every `i`, so `q ∈ R_quad` by Thm. 1
  set fac : Fin (1 + R₀.h + R₀.h) → ℝ := Fin.append (Fin.append ![κ] βξ) fun α => κ * βξ α
    with hfac
  have hfac1 : ∀ j, |fac j| ≤ 1 := fun j => by
    refine Fin.addCases (fun j => ?_) (fun α => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun α => ?_) j
      · rw [hfac, Fin.append_left, Fin.append_left, Fin.fin_one_eq_zero j]; simpa using hκ
      · rw [hfac, Fin.append_left, Fin.append_right]; exact hβξ α
    · rw [hfac, Fin.append_right, abs_mul]
      exact mul_le_one₀ hκ (abs_nonneg _) (hβξ α)
  have hQξ : ∀ i, GuardMap.hitHessianNum A b nv d ξ i = (Q i).c + ∑ j, fac j • (Q i).G j :=
    fun i => by
      have h := GuardMap.hitHessianNum_eq_hitHessianMatZono A b nv d R₀ ψc ψg i βξ κ
        (by rw [← hξeq]; exact hψξ)
      rw [← hξeq] at h
      exact h
  have hqmem : q ∈ (Real.Zonotope.quadMapMatZono (fun i => (Q i).c)
      (fun (j : Fin (1 + R₀.h + R₀.h)) i => (Q i).G j)
      ⟨R₀.h, R₀.c - ξ, R₀.G⟩).construct :=
    Real.Zonotope.quadMapMatZono_outer _ _ _ ⟨ν, hνmem, fac, hfac1, fun i => by
      rw [hqdef]; dsimp only; rw [hQξ i]⟩
  -- `φ ∈ [φ̲, φ̄]`, written as `0.5(φ̲ + φ̄) + 0.5(φ̄ − φ̲)s`, `|s| ≤ 1`
  obtain ⟨hlo, hhi⟩ := GuardMap.hitFactor_mem_Icc A b nv
    (Real.Zonotope.convex_construct R₀) hΛ hφ ⟨βξ, hβξ, hξeq⟩ ⟨βx, hβx, hxeq⟩
  rw [← hφdef] at hlo hhi
  obtain ⟨s, hs, hφs⟩ : ∃ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 ∧
      φ = (φlo + φhi) / 2 + (φhi - φlo) / 2 * s := by
    rcases eq_or_lt_of_le (hlo.trans hhi) with heq | hlt
    · exact ⟨0, ⟨by norm_num, by norm_num⟩, by rw [← heq] at hhi ⊢; linarith⟩
    · refine ⟨(φ - (φlo + φhi) / 2) / ((φhi - φlo) / 2), ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ (by linarith)]; linarith
      · rw [div_le_iff₀ (by linarith)]; linarith
      · field_simp; ring
  -- assemble `y_h(x₀) + R_{h,E}(x₀)`
  simp only [GuardMap.hitEnclosure]
  have hyh : x₀ + ((d - nv ⬝ᵥ x₀) / (nv ⬝ᵥ (A *ᵥ x₀ + b))) • (A *ᵥ x₀ + b)
      = GuardMap.hitPoint A b nv d x₀ := rfl
  rw [hyh, hexp, ← hqdef, ← hφdef]
  refine Set.add_mem_add (Set.add_mem_add (Set.add_mem_add (Set.mem_singleton _)
    ⟨ν, hνmem, rfl⟩) (Set.smul_mem_smul_set ?_)) (Set.add_mem_add ?_ he')
  · rw [hφs, add_smul, mul_smul]
    exact Set.add_mem_add (Set.smul_mem_smul_set hqmem) (Set.smul_mem_smul_set
      (Real.Zonotope.unitIntervalMul_outer _ ⟨(s, q), ⟨hs, hqmem⟩, rfl⟩))
  · exact ⟨x₀, ⟨βx, hβx, hxeq⟩, e, he, _, ⟨x₀, ⟨βx, hβx, hxeq⟩, rfl⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
