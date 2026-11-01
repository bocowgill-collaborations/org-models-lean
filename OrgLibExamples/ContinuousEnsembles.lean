import OrgLib

/-!
# Checked applications of the continuous ensemble laws

All displayed bounds below are measure-theoretic theorems. No finite approximation,
sampled input, or Monte Carlo computation is used to establish their probabilities.
-/

namespace OrgLibExamples.ContinuousEnsembles

open OrgLib.NK OrgLib.NK.SharedCyclic

example : sharedUniformCyclic (by decide : 0 < 1) Set.univ = 1 :=
  sharedUniformCyclic_univ (by decide)

example : independentUniformCyclic (by decide : 0 < 1) Set.univ = 1 :=
  independentUniformCyclic_univ (by decide)

example : independentTablesUniform 2 0
    (entryRectangle
      (fun i ↦ extract (cyclicTopology (by decide : 0 < 2)) state01 i)
      (fun i ↦ extract (cyclicTopology (by decide : 0 < 2)) state10 i)) =
      (1 / 16 : ENNReal) := by
  rw [independentTablesUniform_entryRectangle _ _ extract_state01_ne_state10]
  norm_num [← ENNReal.inv_pow]

example : sharedUniformCyclic (by decide : 0 < 2) (landscapeEvent state01 state10) = 0 :=
  shared_event_state01_state10

example : (1 / 16 : ENNReal) ≤
    independentUniformCyclic (by decide : 0 < 2) (landscapeEvent state01 state10) :=
  independent_event_state01_state10

example : sharedUniformCyclic (by decide : 0 < 12)
    (landscapeEvent alternating01 alternating10) = 0 :=
  shared_event_zero_N12 (by decide)

example : (1 / 2 : ENNReal) ^ 24 ≤ independentUniformCyclic (by decide : 0 < 12)
    (landscapeEvent alternating01 alternating10) :=
  independent_event_lower_bound_N12 (by decide)

example : sharedUniformCyclic (by decide : 5 < 12)
    (landscapeEvent alternating01 alternating10) = 0 :=
  shared_event_zero_N12 (by decide)

example : (1 / 2 : ENNReal) ^ 24 ≤ independentUniformCyclic (by decide : 5 < 12)
    (landscapeEvent alternating01 alternating10) :=
  independent_event_lower_bound_N12 (by decide)

example : sharedUniformCyclic (by decide : 5 < 12) ≠
    independentUniformCyclic (by decide : 5 < 12) :=
  landscape_laws_ne_N12 (by decide)

end OrgLibExamples.ContinuousEnsembles
