module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A polytope that is no zonotope

A zonotope is a polytope (`Zonotope.vPolytope_exact`), and the inclusion is strict: the triangle
with vertices `(0, 0)`, `(1, 0)` and `(0, 1)` is a halfspace description, and no zonotope has it as
its set. A zonotope is symmetric about its center `c`, so it contains `2c - p` with every point `p`,
and the reflections of the two vertices `(1, 0)` and `(0, 1)` already put `c` beyond the hypotenuse.

This is the arrow from zonotopes to polytopes of [1, Fig. 1 (Zonotopes → Polytopes)].

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.

-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.exists_not_zonotope :
    ∃ P : HPolytope (Vec ℝ 2),
      ¬ ∃ Z : Zonotope (Vec ℝ 2), Z.construct = P.construct := by -- --- PROOF ---
  -- the triangle `x₀ ≥ 0`, `x₁ ≥ 0`, `x₀ + x₁ ≤ 1`
  let p : Fin 2 → (Vec ℝ 2 →ₗ[ℝ] ℝ) := fun i => LinearMap.proj i
  refine ⟨{ m := 3
            A := ![-p 0, -p 1, p 0 + p 1]
            b := ![0, 0, 1]
            me := 0
            Ae := Fin.elim0
            be := Fin.elim0 }, ?_⟩
  rintro ⟨Z, hZ⟩
  -- a zonotope is symmetric about its center
  have hsym : ∀ x ∈ Z.construct, (Z.c + Z.c - x : Vec ℝ 2) ∈ Z.construct := by
    rintro x ⟨β, hβ, rfl⟩
    refine ⟨fun j => -β j, fun j => by simpa using hβ j, ?_⟩
    simp only [neg_smul, Finset.sum_neg_distrib]
    abel
  -- the three vertices, and the reflections of two of them
  have hmem : ∀ x : Vec ℝ 2, x ∈ Z.construct ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := fun x => by
    rw [hZ]
    constructor
    · rintro ⟨h, -⟩
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      simp at h0 h1 h2
      exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun i => ?_, fun i => i.elim0⟩
      fin_cases i <;> simp [p, h0, h1, h2]
  have v0 : (fun _ => 0 : Vec ℝ 2) ∈ Z.construct := (hmem _).mpr (by simp)
  -- the vertices lie in the triangle, and so do their reflections about the center
  have v1 : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∈ Z.construct :=
    (hmem _).mpr (by simp)
  have v2 : (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1) ∈ Z.construct :=
    (hmem _).mpr (by simp)
  have r0 := (hmem _).mp (hsym _ v0)
  have r1 := (hmem _).mp (hsym _ v1)
  have r2 := (hmem _).mp (hsym _ v2)
  simp at r0 r1 r2
  linarith [r0.2.2, r1.1, r2.2.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
