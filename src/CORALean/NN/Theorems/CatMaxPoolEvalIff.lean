module

public import CORALean.NN.Operations.CatMaxPool
public import CORALean.NN.Theorems.CatMaxSegmentsEvalIff

@[expose] public section

/-!
# The CAT form of max pooling is max pooling

[1, Sec. II (MaxPool to CAT)]: `MaxPool' = f_{mn r/(pq)} ∘ … ∘ f₁ ∘ f^MP` maps `x` to the vector
of window maxima, output `j` the largest of `x (tap j q)`, and to nothing else; the function
`Layer.maxPool_encloses` encloses. `f^MP` puts coordinate `q` of window `j` at `j (k + 1) + q`, and
`Cat.maxSegments` from `a = 0` reads window `j` back there.

## Inputs
* `tap` – input index of every window position
* `x` – input point
* `y` – output point

## Hypotheses
* none

## Conclusion
* the CAT function maps the point to the output iff the output is the window maxima

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.maxPool_eval_iff (tap : Fin m → Fin (k + 1) → Fin n) (x : Vec ℝ n)
    (y : Vec ℝ m) : -- --- CONCL ---
    (Cat.maxPool (𝕋 := 𝕋) tap).Eval x y ↔
      y = fun j => Real.windowMax fun q => x (tap j q) := by -- --- PROOF ---
  simp only [Cat.maxPool]
  -- window `j` comes back from position `j (k + 1) + q` to `(j, q)`
  have hdiv : ∀ (j : Fin m) (q : Fin (k + 1)), ((k + 1) * j.val + q.val) / (k + 1) = j.val :=
    fun j q => by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.succ_pos k),
        Nat.div_eq_of_lt q.isLt, zero_add]
  have hmod : ∀ (j : Fin m) (q : Fin (k + 1)), ((k + 1) * j.val + q.val) % (k + 1) = q.val :=
    fun j q => by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt q.isLt]
  -- the chain has a value, and only the window maxima
  have key : (∃ y, (Cat.comp (.affine (selectMat fun i : Fin m =>
          (⟨i.val, by omega⟩ : Fin (0 + m))) fun _ => (zero : 𝕋))
        (.comp (Cat.maxSegments k 0 m) (.affine (selectMat fun i : Fin (0 + (k + 1) * m) =>
          tap ⟨i.val / (k + 1), Nat.div_lt_of_lt_mul (by have := i.isLt; omega)⟩
            ⟨i.val % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩) fun _ => zero))).Eval x y) ∧
      ∀ y, (Cat.comp (.affine (selectMat fun i : Fin m =>
          (⟨i.val, by omega⟩ : Fin (0 + m))) fun _ => (zero : 𝕋))
        (.comp (Cat.maxSegments k 0 m) (.affine (selectMat fun i : Fin (0 + (k + 1) * m) =>
          tap ⟨i.val / (k + 1), Nat.div_lt_of_lt_mul (by have := i.isLt; omega)⟩
            ⟨i.val % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩) fun _ => zero))).Eval x y →
        y = fun j => Real.windowMax fun q => x (tap j q) := by
    refine ⟨⟨_, Cat.Eval.comp _ _ _ (Cat.Eval.comp _ _ _ (Cat.Eval.affine _ _ x)
      ((Cat.maxSegments_eval_iff _ _ _ _ _).mpr rfl)) (Cat.Eval.affine _ _ _)⟩,
      fun y hy => ?_⟩
    -- the reorder, the pooling from `a = 0`, the rename
    obtain ⟨z₂, hz₂, hy⟩ := (Cat.eval_comp_iff _ _ _ _).mp hy
    obtain ⟨z₁, hz₁, hz₂⟩ := (Cat.eval_comp_iff _ _ _ _).mp hz₂
    rw [Cat.eval_affine_iff] at hz₁ hy
    replace hz₂ := (Cat.maxSegments_eval_iff _ _ _ _ _).mp hz₂
    subst hz₁ hz₂ hy
    funext j
    rw [selectMat_mulVec_add_zero]
    simp only [Nat.not_lt_zero, dite_false, Nat.sub_zero, zero_add]
    congr 1
    funext q
    rw [selectMat_mulVec_add_zero]
    exact congrArg₂ (fun (a : Fin m) (b : Fin (k + 1)) => x (tap a b))
      (Fin.ext (hdiv j q)) (Fin.ext (hmod j q))
  -- a value exists, and every value is that one
  constructor
  · exact key.2 y
  · rintro rfl
    obtain ⟨y', hy'⟩ := key.1
    rw [← key.2 y' hy']
    exact hy'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
