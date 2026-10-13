import CORALean.NN.Definitions.Schedule
import CORALean.NN.Layers.Layer

/-!
# Raising one layer's orders, neuron by neuron

The one step every refinement rule here is an instance of: `refine`,
`refineLayer` and `Schedule.refineWorstNeurons` each call this with a different
`b`, so the rule that decides *which* orders move never has to touch a schedule
directly.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Layer `l` raised neuron by neuron, which is the one step every refinement
rule here is an instance of. -/
def Schedule.raise (sch : Schedule) (l : ℕ) (b : ℕ → ℕ) : Schedule :=
  Function.update sch l fun j => sch l j + b j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
