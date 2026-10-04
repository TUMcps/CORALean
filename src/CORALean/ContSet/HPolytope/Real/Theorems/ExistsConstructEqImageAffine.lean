import CORALean.ContSet.HPolytope.Real.Theorems.ExistsConstructEqImageFst
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# An affine image of a polyhedron is a polyhedron

[1, Sec. IV-A (Aff)]: the polyhedra domain supports `Aff`, `x ↦ W x + b`, exactly. The graph
`{(y, x) | x ∈ P, y = W x + b}` is cut out by `P`'s rows on `x` and one equality per
coordinate of `y`, and the image is its shadow on `y`, a polyhedron by Fourier–Motzkin
(`exists_construct_eq_image_fst`). The polyhedra are possibly unbounded, as the paper's are:
`HPolytope` asks for no bound. An existence theorem, as elimination is.

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.exists_construct_eq_image_affine (W : Mat ℝ m n) (b : Vec ℝ m)
    (P : HPolytope (Vec ℝ n)) :
    ∃ Q : HPolytope (Vec ℝ m),
      Q.construct = (fun x => W *ᵥ x + b) '' P.construct := by -- --- PROOF ---
  -- the graph: `P`'s rows on the second factor, and `yᵣ - (W x)ᵣ = bᵣ` for every `r`
  let snd := LinearMap.snd ℝ (Vec ℝ m) (Vec ℝ n)
  let G : HPolytope (Vec ℝ m × Vec ℝ n) :=
    { m := P.m, A := fun i => (P.A i).comp snd, b := P.b, me := P.me + m
      Ae := Fin.append (fun i => (P.Ae i).comp snd) fun r =>
        (LinearMap.proj r).comp (LinearMap.fst ℝ (Vec ℝ m) (Vec ℝ n))
          - (LinearMap.proj r).comp ((Matrix.mulVecLin W).comp snd)
      be := Fin.append P.be b }
  obtain ⟨Q, hQ⟩ := HPolytope.exists_construct_eq_image_fst G
  refine ⟨Q, hQ.trans (Set.ext fun y => ⟨?_, ?_⟩)⟩
  -- a point of the graph is an image point, read off its equality rows
  · rintro ⟨⟨y', x⟩, ⟨hA, hAe⟩, rfl⟩
    refine ⟨x, ⟨hA, fun i => by simpa [G, snd] using hAe (Fin.castAdd m i)⟩, ?_⟩
    funext r
    have h := hAe (Fin.natAdd P.me r)
    simp only [G, snd, Fin.append_right, LinearMap.sub_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.coe_proj,
      Function.eval, Matrix.mulVecLin_apply] at h
    show (W *ᵥ x + b) r = y' r
    rw [Pi.add_apply]
    linarith
  -- an image point lifts to the graph, `P`'s rows and then the new ones
  · rintro ⟨x, ⟨hA, hAe⟩, rfl⟩
    refine ⟨(W *ᵥ x + b, x), ⟨hA, fun i => ?_⟩, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun r => ?_) i
    · simpa [G, snd] using hAe i
    · simp [G, snd, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
