import OrgLib

/-!
# Continuous ensemble public interface

The product laws are normalized, realization is measurable in all landscape
coordinates, and the separation bounds concern evaluated landscape events.
-/

namespace OrgLibTest.Ensemble

open OrgLib.NK OrgLib.NK.SharedCyclic MeasureTheory

variable {N K : ℕ}

example : unitUniform = volume.restrict (Set.Icc (0 : ℝ) 1) := rfl

example : IsProbabilityMeasure unitUniform := inferInstance

example (K : ℕ) : IsProbabilityMeasure (tableUniform K) := inferInstance

example (N K : ℕ) : IsProbabilityMeasure (independentTablesUniform N K) := inferInstance

example (T : Topology N K) : Measurable (independentRealization T) :=
  measurable_independentRealization T

example (hKN : K < N) : Measurable (sharedRealization hKN) :=
  measurable_sharedRealization hKN

example (T : Topology N K) : independentUniform T Set.univ = 1 :=
  independentUniform_univ T

example (hKN : K < N) : sharedUniformCyclic hKN Set.univ = 1 :=
  sharedUniformCyclic_univ hKN

example (x y : Config N) : MeasurableSet (landscapeEvent x y) :=
  measurableSet_landscapeEvent x y

example (wx wy : Fin N → LocalWord K) (hne : ∀ i, wx i ≠ wy i) :
    independentTablesUniform N K (entryRectangle wx wy) = (1 / 4 : ENNReal) ^ N :=
  independentTablesUniform_entryRectangle wx wy hne

example (T : Topology N K) (x y : Config N) (hd : ∀ i, extract T x i ≠ extract T y i) :
    (1 / 4 : ENNReal) ^ N ≤ independentUniform T (landscapeEvent x y) :=
  independent_event_lower_bound T x y hd

example : sharedUniformCyclic (by decide : 0 < 2) (landscapeEvent state01 state10) = 0 :=
  shared_event_state01_state10

example : (1 / 16 : ENNReal) ≤
    independentUniformCyclic (by decide : 0 < 2) (landscapeEvent state01 state10) :=
  independent_event_state01_state10

example : sharedUniformCyclic (by decide : 0 < 2) ≠
    independentUniformCyclic (by decide : 0 < 2) :=
  shared_independent_laws_ne

example (hK : K < 12) :
    sharedUniformCyclic hK (landscapeEvent alternating01 alternating10) = 0 :=
  shared_event_zero_N12 hK

example (hK : K < 12) : (1 / 2 : ENNReal) ^ 24 ≤
    independentUniformCyclic hK (landscapeEvent alternating01 alternating10) :=
  independent_event_lower_bound_N12 hK

example (hK : K < 12) : sharedUniformCyclic hK ≠ independentUniformCyclic hK :=
  landscape_laws_ne_N12 hK

end OrgLibTest.Ensemble
