import PEqualNP.Library.L016

/-- A conditional bridge toward `NP ⊆ P`: if some NP-hard language is in P, then every NP
language is in P. Each `L'` in NP reduces to `L` in polynomial time, and P is closed under
polynomial-time reductions (`PEqualNP.Library.L016`, which rests on the composition of
polynomial-time machines, `L007`). The hypothesis is not discharged here. -/
theorem PEqualNP.Outside.Collapse_of_NPHard_mem_P : ∀ L : Language Bool,
    PEqualNP.Library.NPHard L → L ∈ PEqualNP.Library.P →
    PEqualNP.Library.NP ⊆ PEqualNP.Library.P :=
  fun L hhard hp L' hL' => PEqualNP.Library.L016 L' L (hhard L' hL') hp
