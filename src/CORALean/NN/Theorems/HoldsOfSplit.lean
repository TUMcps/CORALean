import CORALean.NN.Theorems.ImageSubset
import CORALean.Specification.Theorems.HoldsOfOuter
import CORALean.Specification.Theorems.HoldsIUnion

/-!
# Verification by splitting the input set

`hcov` is a cover, not a partition: the parts may overlap and may stick out
beyond `X`, all that matters is that nothing in `X` is missed — which is what
a splitter that rounds outward, as any representation's bounded arithmetic
does, still gives. Read `nn.eval '' construct X ⊆ nn.eval '' ⋃ i, construct
(parts i) = ⋃ i, nn.eval '' construct (parts i)`, each part's image inside its
own enclosed set, then `holds_iUnion` with `holds_of_outer`.

Which parts to split into owes no proof: the theorem holds at every cover, so
the splitting heuristic is free, exactly as `ConPolyZono.reduceBy_outer` is
sound at every partition and `Relaxation` at every slope. At `Interval`,
`ι := Bool` and `parts := fun b => if b then (I.splitAt j).1 else
(I.splitAt j).2` with `hcov` supplied by `Interval.splitAt_cover` is one
instance; nothing here searches for which coordinate `j` to bisect.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `hcov` covers `X`, not necessarily equals it — the parts may overlap and
overshoot `X`, so this is a cover a splitter produces, not a `Partition`. -/
theorem NeuralNetwork.holds_of_split {ι : Type} (nn : NeuralNetwork S n m) (X : S n)
    (parts : ι → S n) (hcov : construct X ⊆ ⋃ i, construct (parts i))
    (spec : Specification (Vec ℝ m))
    (h : ∀ i, spec.Holds (construct (nn.enclose (parts i)))) :
    spec.Holds (nn.image (construct X)) := by -- --- PROOF ---
  have hsub : nn.image (construct X) ⊆ ⋃ i, construct (nn.enclose (parts i)) :=
    calc nn.image (construct X) = nn.eval '' construct X := nn.image_eq_eval_image _
      _ ⊆ nn.eval '' ⋃ i, construct (parts i) := Set.image_mono hcov
      _ = ⋃ i, nn.eval '' construct (parts i) := Set.image_iUnion
      _ ⊆ ⋃ i, construct (nn.enclose (parts i)) :=
          Set.iUnion_mono fun i => by
            rw [← nn.image_eq_eval_image]; exact nn.image_subset (parts i)
  exact spec.holds_of_outer hsub (spec.holds_iUnion h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
