import CORALean.ContSet.Taylm.Float.Operations.RangeBound
import CORALean.ContSet.Taylm.Float.Theorems.CodeEvalEncloses
import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem

/-!
# Floating-point range bounding encloses the range

[1, Alg. 1] in floats: whenever it returns a bound, the code list (its constants read as reals)
takes its values over `D` inside it. A point of the box is the identity models' polynomial at
some `t` plus an offset inside their remainders (`taylm_contains`); the identity models enclose
that map, [1, Thm. 3] carries the enclosure through the code list, and `bounds` contains every
value of an enclosed function.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.rangeBound_mem {m : ℕ} {p q s N : ℕ} {e : Real.Taylm.CodeList 𝕋 m}
    {D : Interval (Vec 𝕋 m)} {b : 𝕋 × 𝕋} (hb : Taylm.rangeBound p q s e D N = some b)
    {x : Vec ℝ m} (hx : x ∈ D.construct) :
    toReal b.1 ≤ (e.map toReal).eval x ∧ (e.map toReal).eval x ≤ toReal b.2 := by -- --- PROOF ---
  simp only [Taylm.rangeBound, Option.map_eq_some_iff] at hb
  obtain ⟨T, hT, rfl⟩ := hb
  obtain ⟨t, ht, hxt⟩ := Interval.taylm_contains D N hx
  -- each coordinate is its model's polynomial plus a fixed offset inside the remainder
  set f : Fin m → Vec ℝ _ → ℝ := fun i t' =>
    (D.taylm N i).nominal.poly t' + (x i - (D.taylm N i).nominal.poly t)
  have hF : ∀ i, (D.taylm N i).Encloses (f i) := by
    intro i t' _
    have := hxt i
    simp only [f, add_sub_cancel_left]
    exact this
  have hE := Taylm.codeEval_encloses p q s N hF e hT
  have hfx : (fun i => f i t) = x := by
    funext i
    simp only [f, add_sub_cancel]
  have := Taylm.bounds_mem hE ht
  rwa [hfx] at this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
