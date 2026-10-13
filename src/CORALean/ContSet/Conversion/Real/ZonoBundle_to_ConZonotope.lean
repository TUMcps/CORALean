module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructFoldlIntersectionEq

@[expose] public section

/-!
# A bundle's constrained zonotope, at one component

Through `ZonoBundle.zonotope i`, then the constrained zonotope with nothing to
satisfy — that second leg loses nothing. Whichever component `i` names already
throws away every other one the bundle intersects against — the whole point of
a bundle being that the intersection is tighter than any one member — so all the
loss here is that choice.

`conZonotopeAll` keeps every member, as CORA's `conZonotope(zB)` does: the first member's
constrained zonotope, intersected one `ConZonotope.intersection` at a time with each of the others.
Exact over ℝ, as each intersection is, and it needs a first member, `0 < k`: CORA answers
`conZonotope.empty` for no members, where a bundle of none is the whole space here.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}

def ZonoBundle.conZonotope (zB : ZonoBundle α) (i : Fin zB.k) : ConZonotope α :=
  (zB.zonotope i).conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conZonotope_contains (zB : ZonoBundle α) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.conZonotope_exact _).subset

/-- CORA's `conZonotope(zB)`: `cZ = conZonotope(zB.Z{1})`, then `cZ = and_(cZ, conZonotope(zB.Z{i}),
'exact')` for `i = 2, …, parallelSets`. -/
def ZonoBundle.conZonotopeAll (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    ConZonotope (Vec ℝ n) :=
  let cZ₁ := (zB.Z ⟨0, hk⟩).conZonotope
  Fin.foldl (zB.k - 1)
    (fun cZ i =>
      let cZ_i := (zB.Z ⟨i + 1, by omega⟩).conZonotope
      cZ.intersection cZ_i)
    cZ₁

/-- Exact: the folded intersection denotes the bundle. -/
theorem ZonoBundle.conZonotopeAll_exact (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    (zB.conZonotopeAll hk).construct = zB.construct := by -- --- PROOF ---
  unfold ZonoBundle.conZonotopeAll
  rw [ConZonotope.construct_foldl_intersection_eq]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, ← Zonotope.conZonotope_exact,
    ZonoBundle.construct]
  constructor
  · rintro ⟨h0, hi⟩ ⟨j, hj⟩
    rcases j with _ | j
    · exact h0
    · exact hi ⟨j, by omega⟩
  · intro h
    exact ⟨h ⟨0, hk⟩, fun i => h ⟨i + 1, by omega⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
