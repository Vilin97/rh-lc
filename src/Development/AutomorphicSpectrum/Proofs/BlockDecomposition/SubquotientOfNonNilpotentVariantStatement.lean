module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariant

@[expose] public section

open GlobalTheory.PRep (IsSmooth fixed)
open GlobalTheory.SmGL (HasFiniteLength IsSubquotient)

namespace PositivityTheory.Rg.BcN.F2

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

def SubOfNonNil' : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
    ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ → τ.IsIrreducible →
      IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0) →
      (∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0) → IsSubquotient π ρ

theorem _root_.GlobalTheory.T.subquotient_of_non_nilpotent_variant : SubOfNonNil' F ι := by
  intro K e hE V _ _ π _ _ U _ _ ρ hρ hfl hkill hnil
  by_contra hns
  obtain ⟨r, hr⟩ :=
    GlobalTheory.CompanionTheory.HeckeSub.exists_iterate_eq_zero_of_subquot hE π ρ hρ hfl hkill hns ⊤
  obtain ⟨u, hu, hne⟩ := hnil r
  exact hne (hr u trivial hu)

end PositivityTheory.Rg.BcN.F2
