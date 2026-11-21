module

public import Mathlib.Topology.Compactness.Compact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

@[expose] public section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.UGeo

theorem isCompact_KG_set : ∀ (n : ℕ) (ε : Fin n → Bool),
    IsCompact ((S7.KG ε : Subgroup (S7.UJ ε)) : Set (S7.UJ ε)) := by
  intro n ε
  exact isCompact_iff_compactSpace.mpr (S7.compactSpace_KG ε)

end GlobalTheory.CompanionTheory.UGeo
