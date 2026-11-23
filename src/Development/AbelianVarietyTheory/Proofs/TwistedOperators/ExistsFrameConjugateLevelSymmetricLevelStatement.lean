module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReductionEqFlagBasisOtherInstanceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.exists_diagonal_conj_edgeSum_addChar_finiteField : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ {r : ℕ} (ρ k : ℕ) (ψ' ψ0 : AddChar κf ℂ), ψ' ≠ 1 → ψ0 ≠ 1 → ∀ a : Fin r → Fin r → κfˣ, ∃ d : Fin r → κfˣ, ∀ u : GL (Fin r) κf, u ∈ unipSym κf r ρ k → ψ' (∑ i, ∑ j, if symEdge ρ k i j then (a i j : κf) * u.val i j else 0) = ψ0 (edgeSum (symEdge ρ k) ((diagGL d)⁻¹ * u * diagGL d)) := by
  first | exact @GlobalTheory.SeeConjScale.scale_conj | exact GlobalTheory.SeeConjScale.scale_conj | (intros; apply GlobalTheory.SeeConjScale.scale_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.exists_frame_rescale_conj_reductions_diagonal : ∀ {D : D7} {n r : ℕ} (hr : r ≤ n) (β : GL (Fin n) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), IsFrame β Λ → ∀ (Pg : Finset (Pl D.host.E)) (d : ∀ PP : Pl D.host.E, Fin r → (kP PP)ˣ), ∃ β' : GL (Fin n) (EAf D), IsFrame β' Λ ∧ (∀ M, M ∈ St β' ↔ M ∈ St β) ∧ ∀ PP ∈ Pg, ∀ M ∈ St β, upperLeftBlock hr (redFn β' PP M) = (diagGL (d PP))⁻¹ * upperLeftBlock hr (redFn β PP M) * diagGL (d PP) := by
  first | exact @GlobalTheory.FrameRescale.exists_rescale | exact GlobalTheory.FrameRescale.exists_rescale | (intros; apply GlobalTheory.FrameRescale.exists_rescale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.instanceIota_readout_realTrivial_stabilizer_unitary : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ κ : GA D (Yc D 0), (((iotaX X h).toMulEquiv κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧ (((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset ↔ finE (Yc D 0) κ ∈ St β) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram := by
  first | exact @GlobalTheory.SeeConjReadIota.read_iota | exact GlobalTheory.SeeConjReadIota.read_iota | (intros; apply GlobalTheory.SeeConjReadIota.read_iota <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIff

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem mem_levS_dat0_PsharpSym_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  intro D T Lc β ψ0 κ
  have hH : ∀ g : G0 Lc.Pg D.R.r, g ∈ (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ PP : ↥Lc.Pg, g PP ∈ unipSym (kP PP.1) D.R.r D.R.rS D.R.k := by
    intro g
    show g ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    simp
  refine ⟨?_, fun hκ => ?_⟩
  · rw [GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff, hH]
    simp only [GlobalTheory.SeeConjReord.r0]
    constructor
    · rintro ⟨⟨h0, h1, h2⟩, h3⟩
      exact ⟨h0, h1, h2, fun PP hPP => h3 ⟨PP, hPP⟩⟩
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨h0, h1, h2⟩, fun PP => h3 PP.1 PP.2⟩
  · have hm := ((GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff Lc _ β κ).1 hκ).2
    rw [GlobalTheory.SeeConjReord.principalRowLevelCharacter_trivial, extendOne_of_mem _ hm]
    letI : IsOneApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ => rfl⟩
    letI : IsMulApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
    erw [prod_apply, Units.coe_prod]
    rw [← Finset.prod_coe_sort Lc.Pg]
    rfl

end GlobalTheory.SeeConjRead
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.mem_symmetricPositionLevel_firstSpace_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  first | exact @GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | exact GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | (intros; apply GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameConjugateLevelSymmetricLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConj.exists_frame_symLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi R.Pg ψ0 → ∃ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔ κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0))) ∧ (κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = levChi (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) κ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp ψ0 hψ0
  classical
  obtain ⟨β, hβ, hred⟩ := GlobalTheory.T.exists_frame_reduction_eq_flagBasis_otherInstance R F X h hIs hGrp
  obtain ⟨ψ', a, hψ', hchi⟩ := GlobalTheory.T.conjCharacter_eq_prod_symmetricEdge_characters_alt R F X h hIs hGrp β hβ hred
  have hsc : ∀ PP ∈ R.Pg, ∃ d : Fin D.R.r → (kP PP)ˣ, ∀ u : GL (Fin D.R.r) (kP PP), u ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k →
      ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * u.val i j else 0) =
        ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) ((diagGL d)⁻¹ * u * diagGL d)) :=
    fun PP hP => GlobalTheory.T.exists_diagonal_conj_edgeSum_addChar_finiteField (κf := kP PP) ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal)
      D.R.rS D.R.k (ψ' PP) (ψ0 PP) (hψ' PP hP) (hψ0 PP hP) (a PP)
  choose! dd hdd using hsc
  obtain ⟨β₃, hβ₃, hSt, hconj⟩ := GlobalTheory.T.exists_frame_rescale_conj_reductions_diagonal (r_le_Y (D := D) 0) β _ hβ R.Pg dd
  refine ⟨β₃, hβ₃, fun κ => ?_⟩
  obtain ⟨hR1, hR2, hUA⟩ := GlobalTheory.T.instanceIota_readout_realTrivial_stabilizer_unitary X h β hβ κ
  obtain ⟨hL1, hL2⟩ := GlobalTheory.T.mem_symmetricPositionLevel_firstSpace_iff R.toLevCh β₃ ψ0 κ
  have hgrp := GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions R F X h hIs hGrp β hβ hred κ
  have key : κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔
      κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) := by
    refine Iff.trans ?_ hL1.symm
    show ((iotaX X h).toMulEquiv κ).1 = 1 ∧ ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ h2
      have hS := hR2.1 hK
      have hG' := (hgrp hK hS).1 h2
      refine ⟨hR1.1 h1, hUA, (hSt _).2 hS, fun PP hP => ?_⟩
      rw [hconj PP hP _ hS]
      exact (unipSym_conj_iff _ _ _ _).1 (hG' PP hP)
    · rintro ⟨h1, _, h3, h4⟩
      have hS : finE (Yc D 0) κ ∈ St β := (hSt _).1 h3
      have hK := hR2.2 hS
      refine ⟨hR1.2 h1, (hgrp hK hS).2 fun PP hP => ?_⟩
      have h5 := h4 PP hP
      rw [hconj PP hP _ hS] at h5
      exact (unipSym_conj_iff _ _ _ _).2 h5
  refine ⟨key, fun hk => ?_⟩
  obtain ⟨h1, _, h3, h4⟩ := hL1.1 hk
  have hS : finE (Yc D 0) κ ∈ St β := (hSt _).1 h3
  have hK := hR2.2 hS
  have hK2 : ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 := (key.2 hk).2
  rw [hL2 hk, hchi κ hS hK2]
  refine Finset.prod_congr rfl fun PP hP => ?_
  rw [hconj PP hP _ hS]
  exact hdd PP hP _ ((hgrp hK hS).1 hK2 PP hP)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameConjugateLevelSymmetricLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_frame_conjugate_level_symmetricLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi R.Pg ψ0 → ∃ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔ κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0))) ∧ (κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = levChi (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) κ) := by
  first | exact @GlobalTheory.SeeConj.exists_frame_symLevel | exact GlobalTheory.SeeConj.exists_frame_symLevel | (intros; apply GlobalTheory.SeeConj.exists_frame_symLevel <;> assumption)
end
end
