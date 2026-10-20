module

public import CORALean.ContDynamics.Conform.Theorems.GloSetTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.MemTemplateZonoIff

@[expose] public section

/-!
# [1, Lemma 3]: containment in `Ȳ` as halfspace constraints

`y ∈ Ȳ` iff `N (y - ȳ) ≤ P_α α + P_c c_Δ` (18), row by row, for `α ≥ 0`:
`P_α = [|N C̄ G_x|, ∑ᵢ |N D̄ᵢ G_u|]`, `P_c = [N C̄, N ∑ᵢ D̄ᵢ]`. The maximum over the executions
`s` there is the conjunction over them. `N` is any family carrying both signs of every
cross-product normal of the template `[C̄ G_x, D̄₀ G_u, …, D̄ₖ G_u]` — so fixed before `α`,
as a linear program needs — and the template must span the output space; [1] takes `N`
from [1, Def. 2]'s halfspace representation of `Ȳ`, whose normals these are for `α > 0`.

## Inputs
* `ιx` – index type of the initial generators
* `ιu` – index type of the input generators
* `κ` – normal index type
* `yb` – reference output
* `Cb` – state-to-output matrix
* `Db` – input-to-output matrices
* `cx` – nominal initial state
* `dx` – initial center offset
* `Gx` – initial generators
* `αx` – initial stretch factors
* `cu` – nominal input
* `du` – input center offset
* `Gu` – input generators
* `αu` – input stretch factors
* `N` – normal vectors
* `y` – output point

## Hypotheses
* `hαx` – initial factors nonnegative
* `hαu` – input factors nonnegative
* `hspan` – generators span the output space
* `hN` – `N` carries all generator normals

## Conclusion
* the point is in the set iff the halfspace inequalities hold row by row

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 3]: `y ∈ Ȳ` iff (18) holds row by row. -/
theorem Conform.mem_gloSet_iff_hRep {ιx ιu κ : Type} [Fintype ιx] [Fintype ιu]
    (yb : Vec ℝ (q + 1)) (Cb : Mat ℝ (q + 1) n) (Db : Fin (k + 1) → Mat ℝ (q + 1) p)
    (cx dx : Vec ℝ n) (Gx : ιx → Vec ℝ n) (αx : ιx → ℝ) (cu du : Vec ℝ p) (Gu : ιu → Vec ℝ p)
    (αu : ιu → ℝ) (hαx : ∀ j, 0 ≤ αx j) (hαu : ∀ l, 0 ≤ αu l) (N : κ → Vec ℝ (q + 1))
    (hspan : Submodule.span ℝ (Set.range
      (Sum.elim (fun j => Cb *ᵥ Gx j) fun r : Fin (k + 1) × ιu => Db r.1 *ᵥ Gu r.2)) = ⊤)
    (hN : Conform.HasNormals
      (Sum.elim (fun j => Cb *ᵥ Gx j) fun r : Fin (k + 1) × ιu => Db r.1 *ᵥ Gu r.2) N)
    (y : Vec ℝ (q + 1)) : -- --- CONCL ---
    y ∈ Conform.gloSet yb Cb Db cx (Conform.templateZono (cx + dx) Gx αx) cu
        (fun _ => Conform.templateZono (cu + du) Gu αu) ↔
      ∀ i, N i ⬝ᵥ (y - yb) ≤ ∑ j, |N i ⬝ᵥ (Cb *ᵥ Gx j)| * αx j
        + ∑ l, (∑ t : Fin (k + 1), |N i ⬝ᵥ (Db t *ᵥ Gu l)|) * αu l
        + N i ⬝ᵥ (Cb *ᵥ dx) + ∑ t : Fin (k + 1), N i ⬝ᵥ (Db t *ᵥ du) := by -- --- PROOF ---
  rw [Conform.gloSet_templateZono, Conform.mem_templateZono_iff _ _ hspan N hN _
    fun j => by rcases j with x | r <;> simp [hαx, hαu]]
  refine forall_congr' fun i => ?_
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    Finset.sum_mul, dotProduct_sub, dotProduct_add, dotProduct_sum]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin (k + 1)))]
  constructor <;> intro h <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
