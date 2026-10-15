module

public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.Basic

@[expose] public section

/-!
# `Ext` is transitive

Extending an extension extends the original list.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.ext_trans {a b c : List (OnlineAnalyzerNode A)}
    (h1 : OnlineReachSetAnalyzer.Ext a b) (h2 : OnlineReachSetAnalyzer.Ext b c) :
    OnlineReachSetAnalyzer.Ext a c :=
  ⟨h1.1.trans h2.1, fun j h h' => OnlineReachSetAnalyzer.same_trans
    (h1.2 j h (lt_of_lt_of_le h h1.1)) (h2.2 j (lt_of_lt_of_le h h1.1) h')⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
