module

public import CORALean.NN.Theorems.ImageSubset
public import CORALean.Specification.Theorems.HoldsOfOuter
public import CORALean.Specification.Theorems.HoldsIUnion

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `hcov` covers `X`, not necessarily equals it — the parts may overlap and
overshoot `X`, so this is a cover a splitter produces, not a `Partition`. -/
theorem NeuralNetwork.holds_of_split {ι : Type} {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m} (hf : nn.Sound f) (X : S n)
    (parts : ι → S n) (hcov : construct X ⊆ ⋃ i, construct (parts i))
    (spec : Specification ContSet)
    (h : ∀ i, spec.Holds (construct (nn.enclose (parts i)))) :
    spec.Holds (f '' construct X) := by -- --- PROOF ---
  have hsub : f '' construct X ⊆ ⋃ i, construct (nn.enclose (parts i)) :=
    calc f '' construct X ⊆ f '' ⋃ i, construct (parts i) := Set.image_mono hcov
      _ = ⋃ i, f '' construct (parts i) := Set.image_iUnion
      _ ⊆ ⋃ i, construct (nn.enclose (parts i)) :=
          Set.iUnion_mono fun i => hf.image_subset (parts i)
  exact spec.holds_of_outer hsub (spec.holds_iUnion h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
