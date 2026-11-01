import OrgLib

/-!
# Release client checks for the slot-reindexing action

The earlier public checks apply the fitness-preservation theorem. These typed
applications also protect the identity and composition interfaces promised by T05.
They introduce no additional mathematical assumptions or library definitions.
-/

namespace OrgLibTest.Reindex

open OrgLib.NK

variable {N K : ℕ} {R : Type*}

example (T : Topology N K) :
    T.reindex (fun _ ↦ Equiv.refl _) (fun _ ↦ rfl) = T :=
  T.reindex_refl

example (c : Tables N K R) :
    reindexTables c (fun _ ↦ Equiv.refl _) = c :=
  reindexTables_refl c

example (T : Topology N K) (σ τ : Fin N → Equiv.Perm (Fin (K + 1)))
    (hσ : ∀ i, σ i 0 = 0) (hτ : ∀ i, τ i 0 = 0) :
    (T.reindex σ hσ).reindex τ hτ =
      T.reindex (fun i ↦ (τ i).trans (σ i))
        (fun i ↦ (congrArg (σ i) (hτ i)).trans (hσ i)) :=
  T.reindex_reindex σ τ hσ hτ

example (c : Tables N K R) (σ τ : Fin N → Equiv.Perm (Fin (K + 1))) :
    reindexTables (reindexTables c σ) τ =
      reindexTables c (fun i ↦ (τ i).trans (σ i)) :=
  reindexTables_reindex c σ τ

end OrgLibTest.Reindex
