module

public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# The nearest point of a closed convex set separates

A point `a` outside a nonempty closed convex `K ⊆ ℝⁿ` has a nearest point `p ∈ K` in the Euclidean
norm, at distance `d > 0`, and `K` lies on one side of the hyperplane through `p` normal to
`a - p`: `(a - p)ᵀ x ≤ (a - p)ᵀ p`. That turns a distance into the largest value of
`lᵀ a - ρ(l | K)` over unit `l`, attained at `l = (a - p)/d`, which is how [1, Sec. II (distances)]
writes the distances to an ellipsoid. Hilbert's projection theorem, carried through `toEuclidean`.

## Inputs
* `K` – set of vectors
* `a` – point outside the set

## Hypotheses
* `hK` – the set is closed
* `hc` – the set is convex
* `hne` – the set is nonempty
* `ha` – the point is not in the set

## Conclusion
* a nearest point exists and the set lies on one side of the hyperplane through it

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". Proceedings of the 45th IEEE
      Conference on Decision and Control, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_inner_toEuclidean (x y : Vec ℝ n) :
    inner ℝ (toEuclidean x) (toEuclidean y) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [toEuclidean, dotProduct_comm]


-- =======================================  MAIN THEOREM  ======================================= --

theorem nearest_point_separates (K : Set (Vec ℝ n)) (hK : IsClosed K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (a : Vec ℝ n) (ha : a ∉ K) : -- --- CONCL ---
    ∃ p ∈ K, 0 < ‖a - p‖₂ ∧ IsLeast ((fun x => ‖a - x‖₂) '' K) ‖a - p‖₂ ∧
      ∀ x ∈ K, (a - p) ⬝ᵥ x ≤ (a - p) ⬝ᵥ p := by -- --- PROOF ---
  set e := (toEuclidean : Vec ℝ n ≃L[ℝ] _)
  have hF : IsClosed (e '' K) := (e.toHomeomorph.isClosed_image).mpr hK
  have hFc : Convex ℝ (e '' K) := hc.linear_image e.toLinearMap
  obtain ⟨v, hvF, hv⟩ := exists_norm_eq_iInf_of_complete_convex (hne.image e) hF.isComplete hFc
    (e a)
  have hineq := (norm_eq_iInf_iff_real_inner_le_zero hFc hvF).mp hv
  obtain ⟨p, hp, rfl⟩ := hvF
  -- distances and inner products, read back in `Vec`
  have hd : ∀ x, ‖e a - e x‖ = ‖a - x‖₂ := fun x => by rw [← map_sub, norm_toEuclidean]
  refine ⟨p, hp, ?_, ⟨⟨p, hp, rfl⟩, ?_⟩, fun x hx => ?_⟩
  · rw [← hd]
    refine norm_pos_iff.mpr fun h => ha ?_
    rw [sub_eq_zero] at h
    exact e.injective h ▸ hp
  · rintro _ ⟨x, hx, rfl⟩
    show ‖a - p‖₂ ≤ ‖a - x‖₂
    rw [← hd, ← hd, hv]
    have hbdd : BddBelow (Set.range fun w : (e '' K) => ‖e a - (w : EuclideanSpace ℝ (Fin n))‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hbdd (⟨e x, x, hx, rfl⟩ : (e '' K))
  · have := hineq (e x) ⟨x, hx, rfl⟩
    rw [← map_sub, ← map_sub, aux_inner_toEuclidean, dotProduct_sub] at this
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
