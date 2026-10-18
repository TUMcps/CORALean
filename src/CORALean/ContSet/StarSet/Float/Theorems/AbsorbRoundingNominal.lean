module

public import CORALean.ContSet.StarSet.Float.Operations.AbsorbRounding
public import CORALean.ContSet.StarSet.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `StarSet.absorbRounding` holds the whole set in its nominal part

A point `c + Gα + e`, `e` in the box, is the absorbed star set's nominal point at the factors
`(α, e)`: the old rows ignore the new factors, which lie in the box's own bounds, and the new
identity generators add `e` to the point.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
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
  -- the witness: the old factors, then the error itself
  refine (StarSet.mem_nominalSet_iff _ _).mpr ⟨Fin.append α e, ⟨?_, ?_⟩, fun i => ?_⟩
  -- the factor box: the old bounds, then the error box's
  · refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simpa [StarSet.absorbRounding] using hbox k
    · have hb : toReal (s.I_error.inf k) ≤ e k ∧ e k ≤ toReal (s.I_error.sup k) := he k
      simpa [StarSet.absorbRounding] using hb
  -- the rows: each old row reads the old factors only
  · intro r hr
    change r ∈ s.pred.cons.map _ at hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    have h := hcons r' hr'
    show ∑ k : Fin (s.m + n), toReal (Fin.append r'.1 (fun _ : Fin n => (zero : 𝕋)) k)
      * (Fin.append α e : Fin (s.m + n) → ℝ) k ≤ toReal r'.2
    rw [Fin.sum_univ_add]
    simpa [Fin.append_left, Fin.append_right, toReal_zero] using h
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
