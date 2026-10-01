import CORALean.ContSet.Fullspace.Real.Operations.ProjectHighDim

/-!
# `Fullspace.projectHighDim_` is exact

At `n = N` and distinct coordinates, `proj` is a bijection, so embedding the coordinates
at `proj` (the rest, of which there are none, held at zero) reaches everything.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.projectHighDim_exact (F : Fullspace n) (N : ℕ) (proj : Fin n → Fin N)
    (hN : n = N) (hproj : Function.Injective proj) :
    (F.projectHighDim_ N proj).construct =
      (fun (x : Vec ℝ n) => (Function.extend proj x 0 : Vec ℝ N)) ''
        F.construct := by -- --- PROOF ---
  subst hN
  have hsurj : Function.Surjective proj := Finite.injective_iff_surjective.mp hproj
  ext y
  refine ⟨fun _ => ⟨(fun i => y (proj i) : Vec ℝ n), Set.mem_univ _, ?_⟩,
    fun _ => Set.mem_univ _⟩
  funext j
  obtain ⟨i, rfl⟩ := hsurj j
  exact hproj.extend_apply _ 0 i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
