module

public import CORALean.ContSet.Zonotope.Real.Operations.TensorMultiplicationZono
public import CORALean.ContSet.Zonotope.Real.Operations.TensorEvalLin
public import CORALean.ContSet.Zonotope.Real.Theorems.TensorMultiplicationOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `tensorMultiplication_zono` encloses the images under a tensor zonotope

Outer: for a zonotope `Z` centered at the origin, every tensor `M'` of the matrix zonotope `M`
and every `x ∈ Z`, `Mᵢⱼₖₗ' xⱼ xₖ xₗ` lies in `Z.tensorMultiplication_zono M L`, under the
conditions of `tensorMultiplication_outer` on the lists. The tensor product is linear in the
tensor, so it splits into the center and the generators, each scaled by `γᵢ ∈ [-1, 1]`, which a
zonotope centered at the origin absorbs. Not exact: `x` is taken independently for the center and
for each generator.

## Inputs
* `Z` – zonotope
* `M` – tensor zonotope
* `L` – term lists
* `M'` – tensor in `M`
* `x` – point

## Hypotheses
* `hc` – center at the origin
* `hperm` – term lists enumerate all triples
* `hmap` – equal map entries have equal multisets
* `hM` – `M'` lies in `M`
* `hx` – `x` lies in `Z`

## Conclusion
* the tensor evaluation lies in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A zonotope centered at the origin is closed under scaling by `[-1, 1]`. -/
theorem Zonotope.aux_smul_mem {Z : Zonotope (Vec ℝ n)} (hc : Z.c = 0) {z : Vec ℝ n}
    (hz : z ∈ Z.construct) {γ : ℝ} (hγ : |γ| ≤ 1) : γ • z ∈ Z.construct := by
  obtain ⟨β, hβ, rfl⟩ := hz
  refine ⟨fun j => γ * β j, fun j => ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_one₀ hγ (abs_nonneg _) (hβ j)
  · simp only [hc, zero_add, Finset.smul_sum, smul_smul]

/-- The fold of Minkowski sums holds the sum of one point from each summand. -/
theorem Zonotope.aux_foldl_plus_mem {ι : Type} (l : List ι) (Zs : ι → Zonotope (Vec ℝ n))
    (ys : ι → Vec ℝ n) (hys : ∀ i ∈ l, ys i ∈ (Zs i).construct) : -- --- CONCL ---
    ∀ (acc : Zonotope (Vec ℝ n)) (y : Vec ℝ n), y ∈ acc.construct →
      y + (l.map ys).sum ∈ (l.foldl (fun A i => A.plus (Zs i)) acc).construct := by -- --- PROOF ---
  induction l with
  | nil => intro acc y hy; simpa using hy
  | cons i l ih =>
    intro acc y hy
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have h1 : y + ys i ∈ (acc.plus (Zs i)).construct := by
      rw [← Zonotope.plus_exact]
      exact ⟨y, hy, ys i, hys i List.mem_cons_self, rfl⟩
    have := ih (fun j hj => hys j (List.mem_cons_of_mem _ hj)) _ _ h1
    rwa [add_assoc] at this


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.tensorMultiplication_zono_outer (Z : Zonotope (Vec ℝ n))
    (M : Zonotope (Tensor3 ℝ n)) (L : Zonotope.TensorLists Z.h) (hc : Z.c = 0)
    (hperm : Function.Bijective fun p : Fin L.P => (L.perm p 0, L.perm p 1, L.perm p 2))
    (hmap : ∀ p q, L.map p = L.map q →
      ({L.perm p 0, L.perm p 1, L.perm p 2} : Multiset (Fin Z.h)) =
        {L.perm q 0, L.perm q 1, L.perm q 2})
    {M' : Tensor3 ℝ n} (hM : M' ∈ M.construct) {x : Vec ℝ n}
    (hx : x ∈ Z.construct) : -- --- CONCL ---
    Zonotope.tensorEval M' x ∈ (Z.tensorMultiplication_zono M L).construct := by -- --- PROOF ---
  obtain ⟨γ, hγ, rfl⟩ := hM
  have hlin : Zonotope.tensorEval (M.c + ∑ j, γ j • M.G j) x
      = Zonotope.tensorEval M.c x + ∑ j, γ j • Zonotope.tensorEval (M.G j) x := by
    have := (Zonotope.tensorEvalLin x).map_add M.c (∑ j, γ j • M.G j)
    simp only [Zonotope.tensorEvalLin, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
      map_smul] at this
    exact this
  rw [hlin]
  have hout : ∀ N, (Z.tensorMultiplication N L).c = 0 := fun N => rfl
  have hsum : (∑ j, γ j • Zonotope.tensorEval (M.G j) x)
      = ((List.finRange M.h).map fun j => γ j • Zonotope.tensorEval (M.G j) x).sum := by
    rw [Fin.sum_univ_def]
  rw [hsum]
  unfold Zonotope.tensorMultiplication_zono
  refine Zonotope.aux_foldl_plus_mem (List.finRange M.h)
    (fun j => Z.tensorMultiplication (M.G j) L) (fun j => γ j • Zonotope.tensorEval (M.G j) x)
    (fun j _ => Zonotope.aux_smul_mem (hout _)
      (Zonotope.tensorMultiplication_outer Z _ L hc hperm hmap hx) (hγ j)) _ _
    (Zonotope.tensorMultiplication_outer Z _ L hc hperm hmap hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
