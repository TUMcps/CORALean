import CORALean.Global.Tensor

/-!
# `d(box(S))`, the width of the tightest box over a set

The tightest axis-aligned box over `S` has `[inf_i S, sup_i S]` for its `i`-th
interval, so its diameter — the vector of widths — is `sup_i S - inf_i S` and
the box itself never has to be named. That is what `boxDiameter` is, and it is
the one notion every error measure stated as `d(box(·))` reads.

Deliberately on a bare `Set` rather than on `Interval`: the sets it is asked
about are a Minkowski difference and an infinite Minkowski sum, neither of which
is a representation, so `2 • Interval.radius` would have nothing to apply to.
Where the set *is* a representation, `interval` boxes it first and the two
agree.

Mathlib's `sSup` and `sInf` are `0` off their domain, so an unbounded or empty
`S` gets a junk value rather than an error. Boundedness is therefore a
hypothesis on the theorems that need it, as in `boxDiameter_mono`, and not a
field on the definition.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The coordinate images of a bounded set are bounded above, which is what
`sSup` needs to be the supremum rather than its junk value. -/
theorem aux_bddAbove_eval_image {S : Set (Vec ℝ n)} (hS : Bornology.IsBounded S) (i : Fin n) :
    BddAbove ((fun x : Vec ℝ n => x i) '' S) := by -- --- PROOF ---
  obtain ⟨C, hC⟩ := hS.exists_norm_le
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  -- `x i ≤ |x i| = ‖x i‖ ≤ ‖x‖ ≤ C`, the middle step being the supremum norm
  calc x i ≤ |x i| := le_abs_self _
    _ = ‖x i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖x‖ := norm_le_pi_norm x i
    _ ≤ C := hC x hx

/-- The same bound below, `sInf`'s side of `aux_bddAbove_eval_image`. -/
theorem aux_bddBelow_eval_image {S : Set (Vec ℝ n)} (hS : Bornology.IsBounded S) (i : Fin n) :
    BddBelow ((fun x : Vec ℝ n => x i) '' S) := by -- --- PROOF ---
  obtain ⟨C, hC⟩ := hS.exists_norm_le
  refine ⟨-C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  -- `-C ≤ -|x i| ≤ x i`, the first step being the bound of the previous lemma negated
  have h : |x i| ≤ C :=
    ((Real.norm_eq_abs (x i)) ▸ norm_le_pi_norm x i).trans (hC x hx)
  linarith [neg_abs_le (x i)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `d(box(S))`: the width of the tightest axis-aligned box over `S`, read
coordinatewise. -/
noncomputable def boxDiameter (S : Set (Vec ℝ n)) : Vec ℝ n :=
  fun i => sSup ((fun x : Vec ℝ n => x i) '' S) - sInf ((fun x : Vec ℝ n => x i) '' S)

/-- A larger set has a wider box, provided the larger one is bounded at all and
the smaller one is not empty. -/
theorem boxDiameter_mono {S T : Set (Vec ℝ n)} (hne : S.Nonempty)
    (hT : Bornology.IsBounded T) (hST : S ⊆ T) (i : Fin n) :
    boxDiameter S i ≤ boxDiameter T i := by -- --- PROOF ---
  have himg : (fun x : Vec ℝ n => x i) '' S ⊆ (fun x : Vec ℝ n => x i) '' T :=
    Set.image_mono hST
  have hne' : ((fun x : Vec ℝ n => x i) '' S).Nonempty := hne.image _
  -- the supremum grows and the infimum falls, and the difference of the two does both
  exact sub_le_sub (csSup_le_csSup (aux_bddAbove_eval_image hT i) hne' himg)
    (csInf_le_csInf (aux_bddBelow_eval_image hT i) hne' himg)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
