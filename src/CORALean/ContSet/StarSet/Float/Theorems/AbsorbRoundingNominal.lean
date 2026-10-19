module

public import CORALean.ContSet.StarSet.Float.Operations.AbsorbRounding
public import CORALean.ContSet.StarSet.Float.Theorems.MemNominalSet
public import CORALean.ContSet.StarSet.Float.Theorems.LinPredMemAppendNominal

@[expose] public section

/-!
# `StarSet.absorbRounding` holds the whole set in its nominal part

A point `c + Gα + e`, `e` in the box, is the absorbed star set's nominal point at the factors
`(α, e)`: the old rows ignore the new factors, which lie in the box's own bounds, and the new
identity generators add `e` to the point.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float.SoundFloatArithmetic Float.FloatOps InflatedContSet Pointwise

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of the set, box included, is a nominal point of `absorbRounding`. -/
theorem StarSet.absorbRounding_nominal (s : StarSet 𝕋 n) :
    s.construct ⊆ nominalSet s.absorbRounding := by -- --- PROOF ---
  -- a point is a nominal point plus an error within the box
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨α, ⟨hbox, hcons⟩, hy⟩ := StarSet.mem_nominalSet_iff s y |>.mp hy
  -- the witness: the old factors, which meet the old rows, then the error, in the box
  have hold : α ∈ ContSet.construct s.pred.nominal :=
    ⟨hbox, List.forall_mem_map.mpr hcons⟩
  have hnew := (StarSet.LinPred.mem_append_nominal_iff s.pred s.I_error.inf s.I_error.sup α e).mpr
    ⟨hold, fun k => he k⟩
  refine (StarSet.mem_nominalSet_iff _ _).mpr
    ⟨Fin.append α e, ⟨hnew.1, fun r hr => ?_⟩, fun i => ?_⟩
  · exact hnew.2 _ (List.mem_map_of_mem hr)
  -- the point: the identity generators add the error
  · have hunit : ∀ k : Fin n, toReal (if k = i then (one : 𝕋) else zero) = if k = i then 1 else 0 :=
      fun k => by split_ifs <;> simp [toReal_one, toReal_zero]
    show y i + e i = toReal (s.c i) + ∑ k : Fin (s.m + n),
      toReal (Fin.append (s.G i) (fun k : Fin n => if k = i then (one : 𝕋) else zero) k)
        * (Fin.append α e : Fin (s.m + n) → ℝ) k
    rw [Fin.sum_univ_add, hy i]
    simp [Fin.append_left, Fin.append_right, hunit, add_assoc]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
