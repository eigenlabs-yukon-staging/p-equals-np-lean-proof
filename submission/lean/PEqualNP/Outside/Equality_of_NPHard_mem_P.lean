import PEqualNP.Library.L010
import PEqualNP.Library.L016

/-- The same conditional bridge, packaged as the equality: if some NP-hard language is in P,
then P = NP. `P ⊆ NP` is `PEqualNP.Library.L010`; `NP ⊆ P` is the reduction argument through
`PEqualNP.Library.L016`. The hypothesis is not discharged here. -/
theorem PEqualNP.Outside.Equality_of_NPHard_mem_P : ∀ L : Language Bool,
    PEqualNP.Library.NPHard L → L ∈ PEqualNP.Library.P →
    PEqualNP.Library.P = PEqualNP.Library.NP :=
  fun L hhard hp => Set.Subset.antisymm PEqualNP.Library.L010
    (fun L' hL' => PEqualNP.Library.L016 L' L (hhard L' hL') hp)
