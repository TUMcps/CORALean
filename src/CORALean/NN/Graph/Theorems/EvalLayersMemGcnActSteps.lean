module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import CORALean.NN.Graph.Operations.EvalLayers
public import CORALean.NN.Graph.Operations.GcnActSteps
public import CORALean.NN.Graph.Theorems.GcnSharedPoint

@[expose] public section

/-!
# The graph part of `Alg. 1` contains the iteration it abstracts

[1, Thm. 1]: whatever the graph, the iteration `H ↦ σ (P H W)` that *that* graph runs, from a
point of the feature set, is a point of `gcnActSteps`. The invariant carried through the steps is
one factor vector `a` reaching `P` and `H` together, which is what keeps an edge identified across
steps: a convolution is the product at `a` (`gcnShared_point`), an activation enclosure adds
coefficients `β` for its new independent generators (`ActLayer.IsSound`), and `dependent` makes them
the factors after the old ones (`aux_dependent_point`) while `P` is padded by as many, so it
still reads `a`. Induction on the number of steps, the widths and weights generalized.

## Inputs
* `L` – number of steps

## Hypotheses
* none

## Conclusion
* the exact layered iteration from a point lies in the polynomial zonotope of the steps

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The point of `dependent` at `(a, b)` is the old point at `a` plus the weighted independent
generators. -/
theorem PolyZonotope.aux_dependent_point (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ)
    (b : Fin pZ.q → ℝ) : -- --- CONCL ---
    pZ.dependent.point (Fin.append a b) = pZ.point a + ∑ j, b j • pZ.GI j := by -- --- PROOF ---
  show pZ.c + ∑ i : Fin (pZ.h + pZ.q), PolyZonotope.monomial
      (PolyZonotope.plusE pZ.E (PolyZonotope.identE pZ.q)) (Fin.append a b) i
        • Fin.append pZ.G pZ.GI i = pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
          + ∑ j, b j • pZ.GI j
  rw [Fin.sum_univ_add, add_assoc]
  congr 2
  · exact Finset.sum_congr rfl fun i _ => by
      rw [PolyZonotope.monomial_plusE_left, Fin.append_left]
      simp only [Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by
      rw [PolyZonotope.monomial_plusE_right, Fin.append_right, PolyZonotope.monomial_identE]
      simp only [Fin.append_right]

end


/-- Appending after a cast of the first block is casting the append. -/
theorem aux_append_cast {m m' n : ℕ} (e : m' = m) (a : Fin m → ℝ) (β : Fin n → ℝ)
    (e' : m' + n = m + n) :
    (fun k : Fin (m' + n) => (Fin.append a β : Fin (m + n) → ℝ) (Fin.cast e' k))
      = Fin.append (fun k : Fin m' => a (Fin.cast e k)) β := by
  subst e
  funext k
  simp only [Fin.cast_eq_self]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: the exact layered iteration from a point is a point of `gcnActSteps`. -/
theorem GNN.evalLayers_mem_gcnActSteps (L : ℕ) : -- --- CONCL ---
    ∀ (c : ℕ → ℕ) (σ : ℕ → ℝ → ℝ) (W : ∀ s, Mat ℝ (c s) (c (s + 1)))
      (acts : ∀ s, GNN.ActLayer N (c (s + 1))) (_ : ∀ s, (acts s).IsSound (σ s))
      (P : PolyZonotope (Mat ℝ N N)) (H : PolyZonotope (Mat ℝ N (c 0))) (hp : P.p = H.p)
      (Pstar : Mat ℝ N N) (state : Mat ℝ N (c 0)) (a : Fin P.p → ℝ), (∀ k, |a k| ≤ 1) →
      P.point a = Pstar → H.point (fun k => a (Fin.cast hp.symm k)) = state →
        GNN.evalLayers Pstar L c σ W state
          ∈ (GNN.gcnActSteps L c W acts P H hp).construct := by -- --- PROOF ---
  induction L with
  | zero =>
    intro c σ W acts hσ P H hp Pstar state a ha hP hH
    exact hH ▸ H.point_mem_construct (fun k => ha _)
  | succ L ih =>
    intro c σ W acts hσ P H hp Pstar state a ha hP hH
    -- the convolution at `a` is the product, which the activation enclosure then encloses
    have hconv : (GNN.gcnShared (W 0) P H hp).point a = Pstar * state * W 0 := by
      rw [GNN.gcnShared_point, hP, hH]
    obtain ⟨β, hβ, hact⟩ := hσ 0 (GNN.gcnShared (W 0) P H hp) rfl a ha
    rw [hconv] at hact
    -- the new factor vector appends the coefficients of the independent generators
    refine ih (fun s => c (s + 1)) (fun s => σ (s + 1)) (fun s => W (s + 1))
      (fun s => acts (s + 1)) (fun s => hσ (s + 1)) _ _ _ Pstar _ (Fin.append a β)
      (fun k => ?_) ?_ ?_
    · refine Fin.addCases (fun e => ?_) (fun t => ?_) k
      · rw [Fin.append_left]; exact ha e
      · rw [Fin.append_right]; exact hβ t
    · rw [PolyZonotope.padBack_point]
      simp only [Function.comp_def, Fin.append_left]
      exact hP
    · -- the dependent set at the appended vector is the enclosure's point plus its generators
      have hpe : ((acts 0).act (GNN.gcnShared (W 0) P H hp)).p = P.p :=
        (acts 0).p_eq (GNN.gcnShared (W 0) P H hp)
      have hpt : (((acts 0).act (GNN.gcnShared (W 0) P H hp)).dependent).point
          (fun k => (Fin.append a β : Fin (P.p + ((acts 0).act (GNN.gcnShared (W 0) P H hp)).q)
            → ℝ) (Fin.cast (by
              show ((acts 0).act (GNN.gcnShared (W 0) P H hp)).p + _ = _
              rw [hpe]) k)) = (Pstar * state * W 0).map (σ 0) := by
        refine Eq.trans (congrArg (fun f => (((acts 0).act (GNN.gcnShared (W 0) P H hp)).dependent
          ).point f) (aux_append_cast hpe a β _)) ?_
        rw [PolyZonotope.aux_dependent_point]
        exact hact.symm
      exact hpt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
