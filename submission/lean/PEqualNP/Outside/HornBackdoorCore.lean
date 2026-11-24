import PEqualNP.Outside.BackdoorChunkCore
import PEqualNP.Outside.PositivePairMachine

namespace PEqualNP.Outside.HornBackdoorCore

open PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal hiding step
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word formula selected code finish finish_cpt)
open PEqualNP.Outside.BackdoorChunkCore (advanceChunk endStateChunk endStateChunk_cpt)
open PEqualNP.Outside.PositivePairMachine (obstruction obstruction_cpt)

local notation "CPT" => ComputableInPolyTime (fun x : Word => x) (fun x : Word => x)

def probe (z : Word) : Word := obstruction (formula z, selected z)

theorem probe_cpt : CPT probe := by
  have h := cpt_comp (cpt_pair cpt_unpairB1 (cpt_unpairB1_1 cpt_unpairB2)) obstruction_cpt
  exact h

def pick (q b : Word) : Word := sel (bflag (b.headD false)) (unpairB q).1 (unpairB q).2

def choose (z : Word) : Word := pick (probe z) (code z)

theorem choose_cpt : CPT choose := by
  have hb : CPT code := cpt_unpairB2_1 (cpt_unpairB2_1 cpt_unpairB2)
  exact cptl (cpt_sel (cpt_comp hb cpt_firstF) (cpt_unpairB1_1 probe_cpt)
    (cpt_unpairB2_1 probe_cpt)) (fun _ => rfl)

def step : Word → Word := advanceChunk 1 probe choose

def endState : Word × Word → Word := endStateChunk 1 probe choose

def query (q : Word × Word) : Word := finish (endState q)

theorem query_cpt : ComputableInPolyTime encodePair (fun x : Word => x) query := by
  have h := cpt_comp (endStateChunk_cpt 1 probe_cpt choose_cpt) finish_cpt
  exact h

end PEqualNP.Outside.HornBackdoorCore
