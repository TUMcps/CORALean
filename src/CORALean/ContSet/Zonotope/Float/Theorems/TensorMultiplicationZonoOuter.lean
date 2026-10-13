import CORALean.ContSet.Zonotope.Float.Operations.TensorMultiplicationZono
import CORALean.ContSet.Zonotope.Float.Theorems.TensorMultiplicationSmulOuter
import CORALean.ContSet.Zonotope.Float.Theorems.TensorMultiplicationOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Real.Operations.TensorEvalLin

/-!
# `Zonotope.tensorMultiplication_zono` encloses the tensor images, over a floating-point scalar

For every tensor `M' = M.c + Σᵢ γᵢ M.G i` of the matrix zonotope and `x ∈ Z`, `Mᵢⱼₖₗ xⱼ xₖ xₗ`
lies in the result, under the conditions of `tensorMultiplication_outer`: the product is linear in
the tensor, the centre's term is in `tensorMultiplication M.c`, each generator's term scaled by
`γᵢ` in that of `M.G i` (`tensorMultiplication_smul_outer`), and the fold of Minkowski sums holds
the sum of one point from each summand (`Zonotope.plus_outer`).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fold of Minkowski sums holds the sum of one point from each summand. -/
theorem Zonotope.aux_foldl_plus_mem {ι : Type} (l : List ι) (Zs : ι → Zonotope (Vec 𝕋 n))
    (ys : ι → Vec ℝ n) (hys : ∀ i ∈ l, ys i ∈ (Zs i).construct) :
    ∀ (acc : Zonotope (Vec 𝕋 n)) (y : Vec ℝ n), y ∈ acc.construct →
      y + (l.map ys).sum ∈ (l.foldl (fun A i => A.plus (Zs i)) acc).construct := by -- --- PROOF ---
  induction l with
  | nil => intro acc y hy; simpa using hy
  | cons i l ih =>
    intro acc y hy
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    -- one step of the fold, then the rest
    have h1 : y + ys i ∈ (acc.plus (Zs i)).construct :=
      Zonotope.plus_outer acc (Zs i) (Set.add_mem_add hy (hys i List.mem_cons_self))
    have := ih (fun j hj => hys j (List.mem_cons_of_mem _ hj)) _ _ h1
    rwa [add_assoc] at this


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.tensorMultiplication_zono_outer (Z : Zonotope (Vec 𝕋 n))
    (M : Zonotope (Zonotope.Tensor3 𝕋 n)) (L : Real.Zonotope.TensorLists Z.dependent.h)
    (hc : ∀ i, toReal (Z.c i) = 0)
    (hperm : Function.Bijective fun p : Fin L.P => (L.perm p 0, L.perm p 1, L.perm p 2))
    (hmap : ∀ p q, L.map p = L.map q →
      ({L.perm p 0, L.perm p 1, L.perm p 2} : Multiset (Fin Z.dependent.h)) =
        {L.perm q 0, L.perm q 1, L.perm q 2})
    {β : Fin M.h → ℝ} (hβ : ∀ j, |β j| ≤ 1) {x : Vec ℝ n} (hx : x ∈ Z.construct) :
    Real.Zonotope.tensorEval (fun i a b c => toReal (M.c i a b c)
        + ∑ j, β j * toReal (M.G j i a b c)) x
      ∈ (Z.tensorMultiplication_zono M L).construct := by -- --- PROOF ---
  -- the product is linear in the tensor
  have hlin : Real.Zonotope.tensorEval (fun i a b c => toReal (M.c i a b c)
        + ∑ j, β j * toReal (M.G j i a b c)) x
      = Real.Zonotope.tensorEval (fun i a b c => toReal (M.c i a b c)) x
        + ∑ j, β j • Real.Zonotope.tensorEval (fun i a b c => toReal (M.G j i a b c)) x := by
    have := (Real.Zonotope.tensorEvalLin x).map_add (fun i a b c => toReal (M.c i a b c))
      (∑ j, β j • fun i a b c => toReal (M.G j i a b c))
    simp only [Real.Zonotope.tensorEvalLin, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
      map_smul] at this
    have hM : (fun i a b c => toReal (M.c i a b c) + ∑ j, β j * toReal (M.G j i a b c))
        = (fun i a b c => toReal (M.c i a b c))
          + ∑ j, β j • fun i a b c => toReal (M.G j i a b c) := by
      funext i a b c
      simp [Finset.sum_apply]
    rw [hM]
    exact this
  rw [hlin]
  -- the sum over the generators as the sum over the list the fold runs through
  have hsum : (∑ j, β j • Real.Zonotope.tensorEval (fun i a b c => toReal (M.G j i a b c)) x)
      = ((List.finRange M.h).map fun j =>
          β j • Real.Zonotope.tensorEval (fun i a b c => toReal (M.G j i a b c)) x).sum := by
    rw [Fin.sum_univ_def]
  rw [hsum]
  unfold Zonotope.tensorMultiplication_zono
  exact Zonotope.aux_foldl_plus_mem (List.finRange M.h)
    (fun j => Z.tensorMultiplication (M.G j) L)
    (fun j => β j • Real.Zonotope.tensorEval (fun i a b c => toReal (M.G j i a b c)) x)
    (fun j _ => Zonotope.tensorMultiplication_smul_outer Z _ L hc hperm hmap hx (hβ j)) _ _
    (Zonotope.tensorMultiplication_outer Z _ L hc hperm hmap hx)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
