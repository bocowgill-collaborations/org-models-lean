import OrgLib.NK.Cyclic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Continuous NK ensemble laws

These idealized laws use Lebesgue measure restricted to the unit interval and
finite products over table entries. Topology stays fixed. Evaluated landscape
laws reuse canonical NK fitness and the product measurable structure on functions.

They specify mathematical continuous distributions, not R's pseudorandom generator
or a distribution over sampled topologies.
-/

noncomputable section

namespace OrgLib.NK

open MeasureTheory Set
open scoped BigOperators

/-- Continuous uniform probability on the closed real unit interval. -/
def unitUniform : Measure ℝ :=
  volume.restrict (Icc 0 1)

instance unitUniform_isProbabilityMeasure : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform, Real.volume_Icc]

/-- Independently uniform entries of one local contribution table. -/
def tableUniform (K : ℕ) : Measure (LocalWord K → ℝ) :=
  Measure.pi (fun _ : LocalWord K ↦ unitUniform)

instance tableUniform_isProbabilityMeasure (K : ℕ) : IsProbabilityMeasure (tableUniform K) :=
  Measure.pi.instIsProbabilityMeasure _

/-- Independent local tables, each with independently uniform entries. -/
def independentTablesUniform (N K : ℕ) : Measure (Tables N K ℝ) :=
  Measure.pi (fun _ : Fin N ↦ tableUniform K)

instance independentTablesUniform_isProbabilityMeasure (N K : ℕ) :
    IsProbabilityMeasure (independentTablesUniform N K) :=
  Measure.pi.instIsProbabilityMeasure _

variable {N K : ℕ}

/-- Realize an arbitrary fixed topology and its real tables as an evaluated landscape. -/
def independentRealization (T : Topology N K) (c : Tables N K ℝ) : Config N → ℝ :=
  fitness T c

/-- Evaluation is measurable jointly in every independently supplied table entry. -/
theorem measurable_independentRealization (T : Topology N K) :
    Measurable (independentRealization T) :=
  measurable_pi_lambda _ fun x ↦
    (Finset.measurable_sum Finset.univ (fun i _ ↦
      (measurable_pi_apply (extract T x i)).comp (measurable_pi_apply i))).div_const _

/-- Realize a shared table on the fixed forward cyclic topology. -/
def sharedRealization (hKN : K < N) (φ : LocalWord K → ℝ) : Config N → ℝ :=
  fitness (cyclicTopology hKN) (sharedTables φ)

/-- Reusing one table at every locus is a measurable map of the input data. -/
theorem measurable_sharedTables :
    Measurable (sharedTables : (LocalWord K → ℝ) → Tables N K ℝ) :=
  measurable_pi_lambda _ fun _ ↦ measurable_id

/-- Shared cyclic evaluation is measurable into the landscape's product measurable space. -/
theorem measurable_sharedRealization (hKN : K < N) :
    Measurable (sharedRealization hKN) :=
  (measurable_independentRealization (cyclicTopology hKN)).comp measurable_sharedTables

/-- Law of evaluated shared-table cyclic landscapes under continuous uniform entries. -/
def sharedUniformCyclic (hKN : K < N) : Measure (Config N → ℝ) :=
  Measure.map (sharedRealization hKN) (tableUniform K)

instance sharedUniformCyclic_isProbabilityMeasure (hKN : K < N) :
    IsProbabilityMeasure (sharedUniformCyclic hKN) :=
  Measure.isProbabilityMeasure_map (measurable_sharedRealization hKN).aemeasurable

/-- Law of evaluated independent-table landscapes at an explicitly supplied fixed topology. -/
def independentUniform (T : Topology N K) : Measure (Config N → ℝ) :=
  Measure.map (independentRealization T) (independentTablesUniform N K)

instance independentUniform_isProbabilityMeasure (T : Topology N K) :
    IsProbabilityMeasure (independentUniform T) :=
  Measure.isProbabilityMeasure_map (measurable_independentRealization T).aemeasurable

/-- Independently uniform locus tables evaluated on the same cyclic scopes as the shared law. -/
def independentUniformCyclic (hKN : K < N) : Measure (Config N → ℝ) :=
  independentUniform (cyclicTopology hKN)

instance independentUniformCyclic_isProbabilityMeasure (hKN : K < N) :
    IsProbabilityMeasure (independentUniformCyclic hKN) :=
  independentUniform_isProbabilityMeasure _

/-- The base continuous uniform law has total mass one. -/
@[simp]
theorem unitUniform_univ : unitUniform univ = 1 :=
  measure_univ

/-- The local table product law is normalized at every arity. -/
@[simp]
theorem tableUniform_univ (K : ℕ) : tableUniform K univ = 1 :=
  measure_univ

/-- The nested independent table product law is normalized. -/
@[simp]
theorem independentTablesUniform_univ (N K : ℕ) : independentTablesUniform N K univ = 1 :=
  measure_univ

/-- The evaluated shared cyclic law has total mass one. -/
@[simp]
theorem sharedUniformCyclic_univ (hKN : K < N) : sharedUniformCyclic hKN univ = 1 :=
  measure_univ

/-- The evaluated independent law has total mass one for every supplied topology. -/
@[simp]
theorem independentUniform_univ (T : Topology N K) : independentUniform T univ = 1 :=
  measure_univ

/-- The independent cyclic specialization also has total mass one. -/
@[simp]
theorem independentUniformCyclic_univ (hKN : K < N) : independentUniformCyclic hKN univ = 1 :=
  measure_univ

end OrgLib.NK

end
