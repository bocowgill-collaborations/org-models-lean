import OrgLib
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! # Continuous-law axiom audit -/

run_cmd do
  for name in [
      ``OrgLib.NK.unitUniform,
      ``OrgLib.NK.unitUniform_isProbabilityMeasure,
      ``OrgLib.NK.tableUniform,
      ``OrgLib.NK.tableUniform_isProbabilityMeasure,
      ``OrgLib.NK.independentTablesUniform,
      ``OrgLib.NK.independentTablesUniform_isProbabilityMeasure,
      ``OrgLib.NK.independentRealization,
      ``OrgLib.NK.measurable_independentRealization,
      ``OrgLib.NK.sharedRealization,
      ``OrgLib.NK.measurable_sharedTables,
      ``OrgLib.NK.measurable_sharedRealization,
      ``OrgLib.NK.sharedUniformCyclic,
      ``OrgLib.NK.sharedUniformCyclic_isProbabilityMeasure,
      ``OrgLib.NK.independentUniform,
      ``OrgLib.NK.independentUniform_isProbabilityMeasure,
      ``OrgLib.NK.independentUniformCyclic,
      ``OrgLib.NK.independentUniformCyclic_isProbabilityMeasure,
      ``OrgLib.NK.unitUniform_univ,
      ``OrgLib.NK.tableUniform_univ,
      ``OrgLib.NK.independentTablesUniform_univ,
      ``OrgLib.NK.sharedUniformCyclic_univ,
      ``OrgLib.NK.independentUniform_univ,
      ``OrgLib.NK.independentUniformCyclic_univ,
      ``OrgLib.NK.unitUniform_Ioi_half,
      ``OrgLib.NK.unitUniform_Iic_half,
      ``OrgLib.NK.entryRectangle,
      ``OrgLib.NK.measurableSet_entryRectangle,
      ``OrgLib.NK.independentTablesUniform_entryRectangle,
      ``OrgLib.NK.SharedCyclic.landscapeEvent,
      ``OrgLib.NK.SharedCyclic.measurableSet_landscapeEvent,
      ``OrgLib.NK.SharedCyclic.fitness_gt_half_of_entries_gt,
      ``OrgLib.NK.SharedCyclic.fitness_le_half_of_entries_le,
      ``OrgLib.NK.SharedCyclic.shared_event_preimage_empty,
      ``OrgLib.NK.SharedCyclic.shared_event_zero_of_rotate,
      ``OrgLib.NK.SharedCyclic.entryRectangle_subset_event_preimage,
      ``OrgLib.NK.SharedCyclic.independent_event_lower_bound,
      ``OrgLib.NK.SharedCyclic.cyclic_landscape_laws_ne,
      ``OrgLib.NK.SharedCyclic.extract_state01_ne_state10,
      ``OrgLib.NK.SharedCyclic.shared_event_state01_state10,
      ``OrgLib.NK.SharedCyclic.independent_event_state01_state10,
      ``OrgLib.NK.SharedCyclic.shared_independent_laws_ne,
      ``OrgLib.NK.SharedCyclic.alternating01,
      ``OrgLib.NK.SharedCyclic.alternating10,
      ``OrgLib.NK.SharedCyclic.rotate_alternating01,
      ``OrgLib.NK.SharedCyclic.alternating_bits_ne,
      ``OrgLib.NK.SharedCyclic.alternating_extract_ne,
      ``OrgLib.NK.SharedCyclic.shared_event_zero_N12,
      ``OrgLib.NK.SharedCyclic.independent_event_lower_bound_N12,
      ``OrgLib.NK.SharedCyclic.landscape_laws_ne_N12] do
    let unexpected := (← Lean.collectAxioms name).filter fun ax ↦
      !(([``propext, ``Classical.choice, ``Quot.sound] : List Lean.Name).contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"

#print axioms OrgLib.NK.measurable_independentRealization
#print axioms OrgLib.NK.measurable_sharedRealization
#print axioms OrgLib.NK.independentTablesUniform_entryRectangle
#print axioms OrgLib.NK.SharedCyclic.shared_event_state01_state10
#print axioms OrgLib.NK.SharedCyclic.independent_event_state01_state10
#print axioms OrgLib.NK.SharedCyclic.shared_independent_laws_ne
#print axioms OrgLib.NK.SharedCyclic.independent_event_lower_bound_N12
#print axioms OrgLib.NK.SharedCyclic.landscape_laws_ne_N12
