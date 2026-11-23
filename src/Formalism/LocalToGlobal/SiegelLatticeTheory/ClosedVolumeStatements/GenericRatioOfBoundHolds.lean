module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Corank
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
public import Formalism.PeriodIntegrals.PairCorankPos
public import Formalism.PadicSubsetSums.StableGradedCounts.MemBesselSetZeroIffUpperTriangular
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.BetaIndep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMatBound
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMirBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TermIdIffInSOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagClassConstancy.FlagOfInSFRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelevantCarrierNonempty.InSCarrierNonempty
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PairCorankPos
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalEquivGen
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalRelRepFree
public import Formalism.PeriodIntegrals.ScalarPairDr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.TermStableHolds
public import Formalism.PeriodIntegrals.WhitFunctDual
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DCRelEquiv

section

@[expose] public section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_eq_iff_relation (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermEqIff D u u' := by
  intro F0 Λ _
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdCellInS

section

section

theorem term_id_iff_in_s (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermIdIffInS D u u' :=
  PI.UnitaryGroupMassFormula.IdCellInSW.termIdIffInS_of D (PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D) u u'
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSClassConst

section

@[expose] public section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem in_s_class_constant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSFun D u u' :=
  fun _ Λ _ => PI.InSClassConstW.inSFun_all Λ _ _
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSRelevant

section

section

theorem in_s_relevant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSRel D u u' :=
  PI.UnitaryGroupMassFormula.InSRelevantW.termInSRel_main D u u'
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalarPairDr

section

@[expose] public section

theorem scalar_pair_dr (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalarPairDr.ScalarDr D u u' :=
  PI.ScalarPairDr.W.scalarDr D u u'
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermCarrierStable

section

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_carrier_stable (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermStable D u u' :=
  PI.TCS.termStable_holds D u u'
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WhittakerFunctionalDual.StableOfIrreducible

section

@[expose] public section

namespace PI.WhitFunctDualWork

open Formalism.L2.SG.GGMirabolic

theorem stable_of_irreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, π g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  have := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    show (⊥ : Submodule ℂ V) = ⊤
    ext x
    simp [Subsingleton.elim x 0]
  · rcases IsSimpleOrder.eq_bot_or_eq_top
        (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation π) with h1 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem isIrr_dual {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr (Representation.dual π) := by
  obtain ⟨hnt, hst⟩ := stable_of_irreducible π h
  refine ⟨Module.nontrivial_of_finrank_pos (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_pos),
    fun W hW => ?_⟩
  have hU : ∀ g, ∀ v ∈ W.dualCoannihilator, π g v ∈ W.dualCoannihilator := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hv _ (hW g⁻¹ f hf)
  have hW' : W = W.dualCoannihilator.dualAnnihilator :=
    Subspace.dualCoannihilator_dualAnnihilator_eq.symm
  rcases hst _ hU with h0 | h0
  · right
    rw [hW', h0, Submodule.dualAnnihilator_bot]
  · left
    rw [hW', h0, Submodule.dualAnnihilator_top]

theorem besselEdge_zero (i j : ℕ) : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge 0 0 i j ↔ j = i + 1 := by
  unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge
  constructor <;> intro h <;> omega

theorem whit_mem {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V)
    (ℓ : Module.Dual ℂ V) (hℓ : IsWhit ψ₀ π ℓ) :
    ℓ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := by
  intro u
  beta_reduce
  obtain ⟨hdiag, hlow, -⟩ := u.2
  have huni : IsUni k (u : GL (Fin k) F) := ⟨hdiag, hlow⟩
  have hp : psiU ψ₀ (u : GL (Fin k) F) ≠ 0 := by
    intro h0
    have h3 := AddChar.map_add_eq_mul ψ₀ (superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))
      (-superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at h3
    unfold psiU at h0
    rw [h0, zero_mul] at h3
    exact one_ne_zero h3
  have hchar : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar ψ₀⁻¹ 0 0 k (u : GL (Fin k) F) =
      (psiU ψ₀ (u : GL (Fin k) F))⁻¹ := by
    unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar psiU superdiag
    rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
    congr 2
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : (j : ℕ) = (i : ℕ) + 1 <;> simp [hij, besselEdge_zero]
  ext v
  have hinv : π (u : GL (Fin k) F) (π ((u : GL (Fin k) F)⁻¹) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hw := hℓ (u : GL (Fin k) F) huni (π ((u : GL (Fin k) F)⁻¹) v)
  rw [hinv] at hw
  rw [Representation.dual_apply, LinearMap.smul_apply, hchar, smul_eq_mul,
    Module.Dual.transpose_apply, LinearMap.comp_apply, hw, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem whitFunctDual_main : PI.WhitFunctDual := by
  intro hGG F _ _ k ψ₀ hψ V _ _ _ π hπ ℓ₁ ℓ₂ h1 h2 hne
  have hψ' : ψ₀⁻¹ ≠ 1 := inv_ne_one.mpr hψ
  have hirr := isIrr_dual π hπ
  have hdim := hGG F (Module.Dual ℂ V) k ψ₀⁻¹ (Representation.dual π) hψ' hirr
  have m1 : ℓ₁ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := whit_mem ψ₀ π ℓ₁ h1
  have m2 : ℓ₂ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := whit_mem ψ₀ π ℓ₂ h2
  have hne' : (⟨ℓ₁, m1⟩ : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) ≠ 0 :=
    fun h0 => hne (congrArg Subtype.val h0)
  have hpos : 0 < Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne'⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne').mp (le_antisymm hdim hpos) ⟨ℓ₂, m2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

end PI.WhitFunctDualWork
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WhitFunctDual

section

@[expose] public section

theorem whittaker_functional_dual : PI.WhitFunctDual := PI.WhitFunctDualWork.whitFunctDual_main
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed

section Terms

variable (D : D7) (u u' : D.what₂.Word)

theorem TermEqIff_holds : Formalism.L2.SG.TermDef.TermEqIff D u u' := term_eq_iff_relation D u u'
theorem TermStable_holds : Formalism.L2.SG.TermDef.TermStable D u u' := term_carrier_stable D u u'
theorem TermFun_holds : Formalism.L2.SG.TermDef.TermFun D u u' := term_function_const D u u'

theorem TermInSFun_holds : Formalism.L2.SG.FourParts.TermInSFun D u u' := in_s_class_constant D u u'
theorem TermInSRel_holds : Formalism.L2.SG.FourParts.TermInSRel D u u' := in_s_relevant D u u'
theorem TermIdIffInS_holds : Formalism.L2.SG.FourParts.TermIdIffInS D u u' := term_id_iff_in_s D u u'

theorem ScalarEquiv_holds : Formalism.L2.SG.Corank.ScalarEquiv D u u' := Formalism.L2.SG.Corank.scalarEquiv_of_G (D := D) scalar_equiv_general u u'
theorem ScalarRepFree_holds : Formalism.L2.SG.Corank.ScalarRepFree D u u' := scalar_rep_free D u u'
theorem BetaFree_holds : Formalism.L2.SG.Corank.BetaFree D u u' := scalPairs_betaFree D u u'

theorem ScalarDr_holds : Formalism.L2.SG.Corank.ScalarDr D u u' := by
  intro F0 what₂ hrows p hp
  exact scalar_pair_dr D u u' F0 what₂ hrows p.lam p.mem p.fst p.snd p.G_fst p.G_snd p.beta p.isPair
    hp.1 hp.2

end Terms

theorem CorankPosG_holds : PI.PairCorankPos.CorankPosG := pair_corank_pos
theorem ScalarEquivG_holds : Formalism.L2.SG.Corank.ScalarEquivG := scalar_equiv_general

theorem GelfandGraevMultOne_holds : Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne := whittaker_functional_dual Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gelfand_graev_multiplicity_one
theorem MirabolicBound_holds : Formalism.L2.SG.GGMirabolic.MirabolicBound := mirabolic_bound
theorem GGMatrixBoundOfLit_holds : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit := gg_matrix_bound
theorem GGMatrixBound_holds : Formalism.L2.SG.GGMirabolic.GGMatrixBound :=
  GGMatrixBoundOfLit_holds GelfandGraevMultOne_holds MirabolicBound_holds
theorem TermsGGBound_holds : Formalism.L2.SG.GGMirabolic.TermsGGBound :=
  Formalism.L2.SG.GGMirabolic.termsGGBound_of_matrix GGMatrixBound_holds

theorem IsSplitRow_holds (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) :
    Formalism.L2.SG.Saturated.IsSplitRow D F0 Λ := split_row_iso D u F0 Λ hΛ

end Formalism.L2.SG.Closed
end
end
