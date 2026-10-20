module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialMemEDrift
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# The recentered relaxation over-approximates, at any parity

`[1, Thm. 1]` with one hypothesis, the similarity of `[1, Def. 4]`, and none of the evenness
`relaxExpEven_outer` asks for. `sub_monomial_mem_eDrift` brackets the drift on both sides, and
a bracket has a midpoint and a half-width whatever its ends are, so the center shift is sound
at every exponent pair and only its size depends on parity. Here the operation goes past `[1]`
and CORA, which shift only when every exponent of column `i` is even: `dc + [-d, d] = [dl, du]`
is an identity. An edge of `[1, Def. 5]` with `E_{k₀,j} = 0` is the case they leave.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `k₀` – factor index

## Hypotheses
* `hsim` – generators agree outside that factor

## Conclusion
* the set is contained in the result

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging two generators whose exponent columns agree off `k₀`
over-approximates, with the drift's midpoint moved into the center. -/
theorem PolyZonotope.relaxExpMid_outer (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p)
    (hsim : ∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1)) : -- --- CONCL ---
    pZ.construct ⊆ (pZ.relaxExpMid part k₀).construct := by -- --- PROOF ---
  rintro x ⟨a, β, ha, hβ, rfl⟩
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp
    (PolyZonotope.sub_monomial_mem_eDrift (k₀ := k₀) pZ.E ha hsim)
  -- the drift of the two merged columns, as the exact layer counts it
  set ed := PolyZonotope.eDrift pZ.E k₀ (part.right 0) (part.right 1)
  -- the two ends are counts of the relaxed generator, so neither is negative
  have hfst : (0:ℝ) ≤ (ed.1 : ℝ) := Nat.cast_nonneg _
  have hsnd : (0:ℝ) ≤ (ed.2 : ℝ) := Nat.cast_nonneg _
  have hmidval : (pZ.relaxDrift part k₀).1 = ((ed.2 : ℝ) - (ed.1 : ℝ)) / 2 := rfl
  have hradval : (pZ.relaxDrift part k₀).2 = ((ed.2 : ℝ) + (ed.1 : ℝ)) / 2 := rfl
  have hnn : (0:ℝ) ≤ (pZ.relaxDrift part k₀).2 := by
    rw [hradval]
    linarith
  -- the bracket read as a midpoint and a half-width
  have hmid : |PolyZonotope.monomial pZ.E a (part.right 0)
      - PolyZonotope.monomial pZ.E a (part.right 1) - (pZ.relaxDrift part k₀).1|
        ≤ (pZ.relaxDrift part k₀).2 := by
    rw [abs_le, hmidval, hradval]
    constructor <;> linarith
  set t := Zonotope.coefficient (pZ.relaxDrift part k₀).2
    (PolyZonotope.monomial pZ.E a (part.right 0)
      - PolyZonotope.monomial pZ.E a (part.right 1) - (pZ.relaxDrift part k₀).1) with ht
  have hcoef : t * (pZ.relaxDrift part k₀).2
      = PolyZonotope.monomial pZ.E a (part.right 0)
        - PolyZonotope.monomial pZ.E a (part.right 1) - (pZ.relaxDrift part k₀).1 := by
    rw [ht, mul_comm]
    exact Zonotope.mul_coefficient hmid
  -- the kept columns keep their monomials, and the merged one takes the second's
  have hmono : ∀ l : Fin d, PolyZonotope.monomial (pZ.relaxExpMid part k₀).E a (Fin.castAdd 1 l)
      = PolyZonotope.monomial pZ.E a (part.left l) := fun l => by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExpMid, Fin.append_left]
    rfl
  have hlast : PolyZonotope.monomial (pZ.relaxExpMid part k₀).E a (Fin.natAdd d 0)
      = PolyZonotope.monomial pZ.E a (part.right 1) := by
    simp only [PolyZonotope.monomial, PolyZonotope.relaxExpMid, Fin.append_right]
    rfl
  -- the same factors read both sides, with one coefficient appended
  refine ⟨a, Fin.append β fun _ => t, ha, ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) fun _ => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one hnn hmid
  show pZ.c + ∑ l, PolyZonotope.monomial pZ.E a l • pZ.G l + ∑ j, β j • pZ.GI j
      = pZ.c + (pZ.relaxDrift part k₀).1 • pZ.G (part.right 0)
          + (∑ l : Fin (d + 1), PolyZonotope.monomial (pZ.relaxExpMid part k₀).E a l
              • (pZ.relaxExpMid part k₀).G l)
        + ∑ j : Fin (pZ.q + 1), Fin.append β (fun _ => t) j • (pZ.relaxExpMid part k₀).GI j
  rw [part.sum_split₂ fun l => PolyZonotope.monomial pZ.E a l • pZ.G l,
    Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_two]
  simp only [Fin.sum_univ_one, hmono, hlast]
  simp only [PolyZonotope.relaxExpMid, Fin.append_left, Fin.append_right]
  -- the midpoint sits in the center and the rest of the drift in the new generator
  rw [smul_add, smul_smul, hcoef]
  simp only [sub_smul]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
