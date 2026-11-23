import PEqualNP.Library.L010

/-- P is contained in NP, under the reference definitions. The proof is the reference
library lemma `PEqualNP.Library.L010`: the verifier ignores the witness, projects the pair
encoding to its first component (`Machines.filterMap_polyTime`) and runs the decider
(`L007`, composition of polynomial-time machines). -/
theorem PEqualNP.Outside.P_subset_NP : PEqualNP.Library.P ⊆ PEqualNP.Library.NP :=
  PEqualNP.Library.L010
