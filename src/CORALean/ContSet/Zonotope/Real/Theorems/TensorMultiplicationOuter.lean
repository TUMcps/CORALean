module

public import CORALean.ContSet.Zonotope.Real.Operations.TensorMultiplication
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# `tensorMultiplication` encloses the tensor images

Outer: for a zonotope `Z` centered at the origin and a tensor `M`,
`{ Mᵢⱼₖₗ xⱼ xₖ xₗ | x ∈ Z } ⊆ Z.tensorMultiplication M L`, when the lists `L` are what CORA's
reachability code makes them: `perm` runs over every ordered triple of generator indices exactly
once (permutations with replacement), and two permutations sent to one column by `map` are
reorderings of one another. Then `xₐ x_b x_c = Σ_{i,j,l} βᵢ βⱼ β_l Gᵢₐ Gⱼ_b G_l_c` groups into one
monomial `βᵢ βⱼ β_l ∈ [-1, 1]` per column. The enclosure is not exact: the monomials of different
columns are not independent. Without the two conditions on the lists the statement is false (a
triple listed twice is counted twice).
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Finset

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A trilinear form of three sums, with the sums pulled out. -/
theorem Zonotope.aux_trilinear_expand {k : ℕ} (M : Fin n → Fin n → Fin n → ℝ)
    (A B C : Fin k → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, M a b c * (∑ i, A i a) * (∑ j, B j b) * (∑ l, C l c)
      = ∑ i, ∑ j, ∑ l, ∑ a, ∑ b, ∑ c, M a b c * A i a * B j b * C l c := by -- --- PROOF ---
  simp only [mul_sum, sum_mul]
  -- `a b c l j i` to `i j l a b c`
  conv_lhs =>
    enter [2]; intro a; enter [2]; intro b; enter [2]; intro c; enter [2]; intro l
    rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro a; enter [2]; intro b; enter [2]; intro c; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro a; enter [2]; intro b; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro i; enter [2]; intro a; enter [2]; intro b; enter [2]; intro c
    rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; enter [2]; intro a; enter [2]; intro b; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; enter [2]; intro a; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro i; enter [2]; intro j; enter [2]; intro a; enter [2]; intro b
    rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; enter [2]; intro j; enter [2]; intro a; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; enter [2]; intro j; rw [Finset.sum_comm]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.tensorMultiplication_outer (Z : Zonotope (Vec ℝ n)) (M : Zonotope.Tensor3 n)
    (L : Zonotope.TensorLists Z.h) (hc : Z.c = 0)
    (hperm : Function.Bijective fun p : Fin L.P => (L.perm p 0, L.perm p 1, L.perm p 2))
    (hmap : ∀ p q, L.map p = L.map q →
      ({L.perm p 0, L.perm p 1, L.perm p 2} : Multiset (Fin Z.h)) =
        {L.perm q 0, L.perm q 1, L.perm q 2})
    {x : Vec ℝ n} (hx : x ∈ Z.construct) : -- --- STMT ---
    Zonotope.tensorEval M x ∈ (Z.tensorMultiplication M L).construct := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx
  -- coordinates of `x`
  have hxa : ∀ a, (Z.c + ∑ j, β j • Z.G j) a = ∑ j, β j * Z.G j a := fun a => by
    simp [hc, Finset.sum_apply]
  -- the tensor product expanded over triples of generators
  set T : Fin Z.h → Fin Z.h → Fin Z.h → Fin n → ℝ := fun i j l iDim =>
    ∑ a, ∑ b, ∑ c, M iDim a b c * Z.G i a * Z.G j b * Z.G l c with hT
  have hexp : ∀ iDim, Zonotope.tensorEval M (Z.c + ∑ j, β j • Z.G j) iDim
      = ∑ i, ∑ j, ∑ l, (β i * β j * β l) * T i j l iDim := by
    intro iDim
    unfold Zonotope.tensorEval
    simp only [hxa]
    rw [Zonotope.aux_trilinear_expand (M iDim) (fun i a => β i * Z.G i a)
      (fun j b => β j * Z.G j b) (fun l c => β l * Z.G l c)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    rw [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  -- the triples are the permutations
  set w : Fin L.P → ℝ := fun p => β (L.perm p 0) * β (L.perm p 1) * β (L.perm p 2) with hw
  have hperm_sum : ∀ iDim, ∑ i, ∑ j, ∑ l, (β i * β j * β l) * T i j l iDim
      = ∑ p, w p * T (L.perm p 0) (L.perm p 1) (L.perm p 2) iDim := by
    intro iDim
    have h1 : ∑ i, ∑ j, ∑ l, (β i * β j * β l) * T i j l iDim
        = ∑ t : Fin Z.h × Fin Z.h × Fin Z.h,
            (β t.1 * β t.2.1 * β t.2.2) * T t.1 t.2.1 t.2.2 iDim := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
    rw [h1]
    exact (Fintype.sum_equiv (Equiv.ofBijective _ hperm) _ _ (fun p => rfl)).symm
  -- the monomial of a column
  have hwabs : ∀ p, |w p| ≤ 1 := fun p => by
    simp only [hw, abs_mul]
    exact mul_le_one₀ (mul_le_one₀ (hβ _) (abs_nonneg _) (hβ _)) (abs_nonneg _) (hβ _)
  have hwms : ∀ p, w p = (Multiset.map β
      ({L.perm p 0, L.perm p 1, L.perm p 2} : Multiset (Fin Z.h))).prod := fun p => by
    simp [hw, mul_assoc]
  -- one monomial `γ m` per column, the common value of `w` on its permutations
  classical
  let γ : Fin L.C → ℝ := fun m => if h : ∃ p, L.map p = m then w h.choose else 0
  have hγ : ∀ p, w p = γ (L.map p) := fun p => by
    have h : ∃ q, L.map q = L.map p := ⟨p, rfl⟩
    simp only [γ, dif_pos h]
    rw [hwms, hwms]
    rw [hmap p h.choose h.choose_spec.symm]
  -- the coefficients `γ` are in `[-1, 1]`, and group the permutations by column
  refine ⟨γ, fun m => ?_, ?_⟩
  · by_cases h : ∃ p, L.map p = m
    · simp only [γ, dif_pos h]; exact hwabs _
    · simp [γ, h]
  · funext iDim
    rw [hexp, hperm_sum]
    simp only [Zonotope.tensorMultiplication, Pi.add_apply, Pi.zero_apply, zero_add,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin L.P)) L.map]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hγ p, (Finset.mem_filter.mp hp).2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
