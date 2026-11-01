import OrgLib.NK.SharedCyclic.EnsembleSeparation

/-!
# Alternating-state separation on twelve loci

The two alternating configurations on twelve loci are rotations and differ at
every focal coordinate. Consequently, every permitted cyclic local word differs,
regardless of `K < 12`. This lets the continuous-law separation argument constrain
twenty-four distinct locus/word entries while retaining the same topology.
The `N = 12`, `K = 0` and `K = 5` settings appear in Scott C. Ganz,
*Adaptive Rationality, Garbage Cans, and the Policy Process*, printed p.86.
-/

namespace OrgLib.NK.SharedCyclic

open OrgLib.NK

/-- The labeled twelve-coordinate state `010101010101`. -/
def alternating01 : Config 12 := fun i ↦ i.val % 2 == 1

/-- The labeled complementary state `101010101010`. -/
def alternating10 : Config 12 := fun i ↦ !(alternating01 i)

/-- A one-coordinate rotation exchanges the alternating states, including the wrap. -/
theorem rotate_alternating01 : rotate (1 : Fin 12) alternating01 = alternating10 := by
  decide

/-- At every locus the two alternating states have opposite focal bits. -/
theorem alternating_bits_ne : ∀ i, alternating01 i ≠ alternating10 i := by
  decide

/-- Focal-slot disagreement makes the selected words distinct for every arity K<12. -/
theorem alternating_extract_ne {K : ℕ} (hK : K < 12) (i : Fin 12) :
    extract (cyclicTopology hK) alternating01 i ≠
      extract (cyclicTopology hK) alternating10 i :=
  fun h ↦ alternating_bits_ne i (by
    simpa [extract, (cyclicTopology hK).self] using congrFun h 0)

/-- T15: at all paper-size arities, shared cyclic tables give the event zero mass. -/
theorem shared_event_zero_N12 {K : ℕ} (hK : K < 12) :
    sharedUniformCyclic hK (landscapeEvent alternating01 alternating10) = 0 := by
  simpa only [rotate_alternating01] using
    shared_event_zero_of_rotate hK alternating01 (1 : Fin 12)

/-- T15: twenty-four distinct selected entries give the continuous bound 2⁻²⁴. -/
theorem independent_event_lower_bound_N12 {K : ℕ} (hK : K < 12) :
    (1 / 2 : ENNReal) ^ 24 ≤
      independentUniformCyclic hK (landscapeEvent alternating01 alternating10) :=
  calc
    (1 / 2 : ENNReal) ^ 24 = (1 / 4 : ENNReal) ^ 12 := by
      norm_num [← ENNReal.inv_pow]
    _ ≤ independentUniformCyclic hK (landscapeEvent alternating01 alternating10) :=
      independent_event_lower_bound (cyclicTopology hK) alternating01 alternating10
        (alternating_extract_ne hK)

/-- T15: the shared and independent evaluated laws differ for every K<12. -/
theorem landscape_laws_ne_N12 {K : ℕ} (hK : K < 12) :
    sharedUniformCyclic hK ≠ independentUniformCyclic hK :=
  cyclic_landscape_laws_ne hK alternating01 (1 : Fin 12) (fun i ↦ by
    simpa only [rotate_alternating01] using alternating_extract_ne hK i)

end OrgLib.NK.SharedCyclic
