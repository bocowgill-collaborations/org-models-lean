import OrgLib
import OrgLibExamples.ThreeComponent
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! # Rational cast and example axiom audit -/

run_cmd do
  for name in [``OrgLib.NK.contribution_ratCast, ``OrgLib.NK.fitness_ratCast,
      ``OrgLibExamples.ThreeComponent.expected_code_0,
      ``OrgLibExamples.ThreeComponent.expected_code_1,
      ``OrgLibExamples.ThreeComponent.expected_code_2,
      ``OrgLibExamples.ThreeComponent.expected_code_3,
      ``OrgLibExamples.ThreeComponent.expected_code_4,
      ``OrgLibExamples.ThreeComponent.expected_code_5,
      ``OrgLibExamples.ThreeComponent.expected_code_6,
      ``OrgLibExamples.ThreeComponent.expected_code_7,
      ``OrgLib.NK.SharedCyclic.witness_fitness_state01,
      ``OrgLib.NK.SharedCyclic.witness_fitness_state10] do
    let unexpected := (← Lean.collectAxioms name).filter fun ax ↦
      !(([``propext, ``Classical.choice, ``Quot.sound] : List Lean.Name).contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"

#print axioms OrgLib.NK.fitness_ratCast
