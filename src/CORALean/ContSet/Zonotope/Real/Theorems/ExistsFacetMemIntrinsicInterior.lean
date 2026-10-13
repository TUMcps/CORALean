import CORALean.ContSet.Zonotope.Real.Definitions.Degree
import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemIntrinsicInterior
import CORALean.ContSet.Zonotope.Real.Theorems.ExistsFacetSuperset

/-!
# A point of degree at most `n - 1` shares a facet with a point interior to it

[1, Cor. 3.5]: for `x ∈ Z` of degree `≤ n - 1` there is a point `x*` and a facet `F` with
`{x, x*} ⊆ F` and `x*` in the interior of `F`, the interior relative to the affine hull of `F`
(`intrinsicInterior`), a facet having no interior in `ℝⁿ`. For a full-dimensional `Z`, which a
facet needs. [1] iterates Lemma 3.4 `n - 1` times; here the least face through `x`, proper as its
dimension is below `n`, lies in a facet `F = Z.face u` (`exists_facet_superset`,
`construct_face`), and `x*` is that zonotope's centre (`center_mem_intrinsicInterior`). For
`n = 0` the zonotope is a point and its own facet. "Found in polynomial time" is a running time,
not stated here.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 3.5]: for `x ∈ Z` of degree `≤ n - 1`, a facet `F ∋ x` and a point `x*` in the
relative interior of `F`. -/
theorem Zonotope.exists_facet_mem_intrinsicInterior (Z : Zonotope (Vec ℝ n))
    (hfull : Submodule.span ℝ (Set.range Z.G) = ⊤) {x : Vec ℝ n} (hx : x ∈ Z.construct)
    (hdeg : Zonotope.degree Z.construct x ≤ n - 1) :
    ∃ (xs : Vec ℝ n) (F : Set (Vec ℝ n)), IsExposed ℝ Z.construct F ∧
      Module.finrank ℝ (vectorSpan ℝ F) = n - 1 ∧ x ∈ F ∧ xs ∈ F ∧
      xs ∈ intrinsicInterior ℝ F := by -- --- PROOF ---
  have hZ : Module.finrank ℝ (vectorSpan ℝ Z.construct) = n := by
    rw [Zonotope.vectorSpan_construct, hfull, finrank_top]
    exact Module.finrank_fin_fun ℝ
  have hD : {d | ∃ F : Set (Vec ℝ n), IsExposed ℝ Z.construct F ∧ x ∈ F ∧
      Module.finrank ℝ (vectorSpan ℝ F) = d}.Nonempty :=
    ⟨_, Z.construct, IsExposed.refl _, hx, rfl⟩
  -- the least face through `x`
  obtain ⟨F0, hF0, hxF0, hdim0⟩ := Nat.sInf_mem hD
  have hk : Module.finrank ℝ (vectorSpan ℝ F0) = Zonotope.degree Z.construct x := hdim0
  by_cases hprop : F0 = Z.construct
  · -- the least face is `Z`, so `n = 0` and `Z` is its own facet
    subst hprop
    exact ⟨Z.c, Z.construct, IsExposed.refl _, by omega, hx,
      ⟨0, fun _ => by simp, by simp⟩, Z.center_mem_intrinsicInterior⟩
  · -- a facet over it, and the facet's centre
    obtain ⟨F', hF', hdim', hsub⟩ := Z.exists_facet_superset hfull hF0 ⟨x, hxF0⟩ hprop
    obtain ⟨l', rfl⟩ := hF' ⟨x, hsub hxF0⟩
    have hface := Z.construct_face (l' : Vec ℝ n →ₗ[ℝ] ℝ)
    refine ⟨(Z.face (l' : Vec ℝ n →ₗ[ℝ] ℝ)).c, _, hF', hdim', hsub hxF0, ?_, ?_⟩
    · have h : (Z.face (l' : Vec ℝ n →ₗ[ℝ] ℝ)).c ∈ (Z.face (l' : Vec ℝ n →ₗ[ℝ] ℝ)).construct :=
        ⟨0, fun _ => by simp, by simp⟩
      rw [hface] at h
      exact h
    · have h := (Z.face (l' : Vec ℝ n →ₗ[ℝ] ℝ)).center_mem_intrinsicInterior
      rw [hface] at h
      exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
