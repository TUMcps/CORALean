module

public import CORALean.ContSet.Taylm.Float.Operations.ReexpandAt
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# One variable's re-expansion is exact

The exact coefficients `a · C(eₖ, j) mᵉᵏ⁻ʲ rʲ` at the expanded exponents give, at `s`, the original
polynomial at `s` with `sₖ` replaced by `m + r sₖ`: a term's monomial splits into the factor of
`sₖ` and the rest, and the factor of `sₖ` is the binomial theorem.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A monomial split at one variable. -/
theorem Taylm.aux_monomial_split (e : Fin n → ℕ) (t : Vec ℝ n) (k : Fin n) :
    Real.Taylm.monomial e t = t k ^ e k * ∏ i ∈ Finset.univ.erase k, t i ^ e i :=
  (Finset.mul_prod_erase Finset.univ (fun i => t i ^ e i) (Finset.mem_univ k)).symm

/-- One term, expanded: the binomial theorem in the exponent of the variable. -/
theorem Taylm.aux_term_expand (a : ℝ) (e : Fin n → ℕ) (s : Vec ℝ n) (k : Fin n) (m r : ℝ) :
    a * Real.Taylm.monomial e (Function.update s k (m + r * s k)) =
      ∑ j ∈ Finset.range (e k + 1),
        (a * ((e k).choose j * m ^ (e k - j) * r ^ j)) *
          Real.Taylm.monomial (Function.update e k j) s := by -- --- PROOF ---
  have hL : Real.Taylm.monomial e (Function.update s k (m + r * s k))
      = (m + r * s k) ^ e k * ∏ i ∈ Finset.univ.erase k, s i ^ e i := by
    rw [Taylm.aux_monomial_split e _ k, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hR : ∀ j, Real.Taylm.monomial (Function.update e k j) s
      = s k ^ j * ∏ i ∈ Finset.univ.erase k, s i ^ e i := fun j => by
    rw [Taylm.aux_monomial_split _ s k, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hb : (m + r * s k) ^ e k = ∑ j ∈ Finset.range (e k + 1),
      ((e k).choose j : ℝ) * m ^ (e k - j) * r ^ j * s k ^ j := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring
  rw [hL, hb, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hR]; ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_reexpPairs (L : List (𝕋 × (Fin n → ℕ))) (k : Fin n) (m r : 𝕋) (s : Vec ℝ n) :
    Real.Taylm.polyOf ((L.flatMap fun a => (List.range (a.2 k + 1)).map fun j => (a, j)).map
        fun q => (toReal q.1.1 * (((q.1.2 k).choose q.2 : ℝ) * toReal m ^ (q.1.2 k - q.2)
          * toReal r ^ q.2), Function.update q.1.2 k q.2)) s =
      Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2))
        (Function.update s k (toReal m + toReal r * s k)) := by -- --- PROOF ---
  induction L with
  | nil => simp [Real.Taylm.polyOf]
  | cons a L ih =>
    rw [List.flatMap_cons, List.map_append, Real.Taylm.polyOf_append, ih, List.map_cons,
      Real.Taylm.polyOf_cons]
    congr 1
    simp only [Real.Taylm.polyOf, List.map_map, Function.comp_def]
    rw [Taylm.aux_term_expand]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
