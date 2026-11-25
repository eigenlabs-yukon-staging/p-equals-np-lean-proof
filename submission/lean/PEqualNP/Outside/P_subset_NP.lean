import PEqualNP.Library.L010

namespace PEqualNP.Outside

/-- The reference verifier can ignore an empty certificate for a deterministic decider. -/
theorem P_subset_NP : PEqualNP.Library.P ⊆ PEqualNP.Library.NP :=
  PEqualNP.Library.L010

end PEqualNP.Outside
