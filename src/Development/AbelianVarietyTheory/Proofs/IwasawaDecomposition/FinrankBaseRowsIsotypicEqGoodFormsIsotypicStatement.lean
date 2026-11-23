module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugateStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicSumEqOfFramesInnerConjStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicSumInfGroupAlgebraKilledEqBotStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoOfEquivariantHomIntoIsotypicSumStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankEquivariantHomsIntoIsotypicSumOfIsoStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankIsotypicConjTypeEqConjModelStatement
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypeIsotypicPartEqISupEquivariantHomsFrame

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsotHom

theorem isotIn_eq_iSup_homInto : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f := by
  intro D V S θ M n P π
  classical
  set e := GlobalTheory.KapIsot.eqv P with he
  have hσ : ∀ κ (x : π.S), ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (e κ) x = GlobalTheory.OccRowVec.finRep π κ x := fun κ x => by
    show GlobalTheory.OccRowVec.finRep π (e.symm (e κ)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hact : ∀ κ (T : MMap M), principalLevelFrame.actM P M κ T = finRep M (e κ) T := fun κ T => by
    refine MultilinearMap.ext fun v => funext fun g => ?_
    rw [principalLevelFrame.actM_apply, finRep_apply]
    rfl
  have hle : principalLevelFrame.Minf θ P M ≤ allMaps θ M := iSup_le fun N => GlobalTheory.PartDims.mult_le θ M fun k hk => hk.elim
  apply le_antisymm
  · refine iSup₂_le fun Φ hΦ => ?_
    refine le_iSup₂_of_le (f := fun f (_ : f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (finRep M) (allMaps θ M)) => LinearMap.range f) Φ ⟨fun s => hle (hΦ.2 ⟨s, rfl⟩), fun g s => ?_⟩ le_rfl
    obtain ⟨κ, rfl⟩ := e.surjective g
    rw [hσ, ← hact]
    exact hΦ.1 κ s
  · refine iSup₂_le fun f hf => ?_
    have hfe : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π f := by
      intro κ x
      have h1 := hf.2 (e κ) x
      rw [hσ, ← hact] at h1
      exact h1
    have hfr : LinearMap.range f ≤ principalLevelFrame.Minf θ P M := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨N, hN, hfix⟩ := π.smooth x x.2
      obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      refine Submodule.mem_iSup_of_mem N (Submodule.subset_span ?_)
      have h1 := (GlobalTheory.MultMem.mem_mult_iff ..).1 (hf.1 x)
      refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
      rintro v _ ⟨κ, hκ, rfl⟩ g
      have h2 := hfe κ x
      rw [show (⟨Formalism.L2.NG.rt D.host.E n κ x, π.stable κ x x.2⟩ : π.S) = x from Subtype.ext (hfix κ hκ)] at h2
      rw [one_mul]
      exact (congrArg (fun T : MMap M => T v g) h2).symm
    exact le_iSup₂_of_le (f := fun (Φ : π.S →ₗ[ℂ] MMap M) (_ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π Φ ∧ LinearMap.range Φ ≤ principalLevelFrame.Minf θ P M) => LinearMap.range Φ) f ⟨hfe, hfr⟩ le_rfl

end GlobalTheory.IsotHom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypeIsotypicPartEqISupEquivariantHomsFrameStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.finiteTypeIsotypicPart_eq_iSup_equivariantHoms_frame : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f := by
  first | exact @GlobalTheory.IsotHom.isotIn_eq_iSup_homInto | exact GlobalTheory.IsotHom.isotIn_eq_iSup_homInto | (intros; apply GlobalTheory.IsotHom.isotIn_eq_iSup_homInto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleFiniteTypeFrameOfCuspMap

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.AdmOfHom

theorem isAdmissible_finRep : GlobalTheory.Published.HarishChandraFinite → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S') (Φ : GfC V ≃ₜ* GfC V') (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P' : LevelP L.Pg L.r ℂ) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), L.s = 0 → L.Q = ∅ → killed ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (eqSet V β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) ≠ ⊥ → (homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M) ≠ ⊥ ∨ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) ((finRep M').comp Φ.toMulEquiv.toMonoidHom) (allMaps θ M') ≠ ⊥) → GlobalTheory.PRep.IsAdmissible ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) := by
  intro hP D θ hθ V V' S S' M M' Φ β L G _ _ eG c P' n P π hs hQ hk hhom
  set σ : Representation ℂ (GfC V) π.S := (GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom with hσdef
  have hirr : ∀ U : Submodule ℂ π.S, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤ := fun U hU =>
    GlobalTheory.OccRowVec.finRep_irr π U fun g x hx => by
      have := hU (GlobalTheory.KapIsot.eqv P g) x hx
      simpa [σ] using this
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have ho := GlobalTheory.PartDims.isOpen_stab hs hQ hy
  haveI := GlobalTheory.PartDims.isTopologicalGroup_GA V
  rcases hhom with h | h
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact GlobalTheory.KapIsot.isAdmissible_of hirr hy0 ho hf hf0
      (fun K hK => GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ K hK)
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine GlobalTheory.KapIsot.isAdmissible_of hirr hy0 ho hf hf0 (fun K hK => ?_)
    have hK' : IsOpen ((K.map Φ.toMulEquiv.toMonoidHom : Subgroup (GfC V')) : Set (GfC V')) := by
      rw [Subgroup.coe_map]
      exact Φ.toHomeomorph.isOpenMap _ hK
    haveI := GlobalTheory.CuspDec.finiteDimensional_fixed (M := M') hP hθ _ hK'
    refine Submodule.finiteDimensional_of_le (S₂ := allMaps θ M' ⊓ GlobalTheory.PRep.fixed (finRep M') (K.map Φ.toMulEquiv.toMonoidHom))
      fun x hx => ⟨hx.1, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => ?_⟩
    obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.1 hk
    exact GlobalTheory.CuspDec.mem_fixed.1 hx.2 k0 hk0

end GlobalTheory.AdmOfHom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleFiniteTypeFrameOfCuspMapStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.isAdmissible_finiteType_frame_of_cuspMap : GlobalTheory.Published.HarishChandraFinite → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S') (Φ : GfC V ≃ₜ* GfC V') (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P' : LevelP L.Pg L.r ℂ) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), L.s = 0 → L.Q = ∅ → killed ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (eqSet V β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) ≠ ⊥ → (homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M) ≠ ⊥ ∨ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) ((finRep M').comp Φ.toMulEquiv.toMonoidHom) (allMaps θ M') ≠ ⊥) → GlobalTheory.PRep.IsAdmissible ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) := by
  first | exact @GlobalTheory.AdmOfHom.isAdmissible_finRep | exact GlobalTheory.AdmOfHom.isAdmissible_finRep | (intros; apply GlobalTheory.AdmOfHom.isAdmissible_finRep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankBaseRowsIsotypicEqGoodFormsIsotypic

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.Mem.R3.IsotMult

theorem finrank_isot_killed_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] (S0 X Y : Type) [AddCommGroup S0] [Module ℂ S0] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), σ0.IsIrreducible → (killed σ0 I ≠ ⊥ → (homInto σ0 ρ C ≠ ⊥ ∨ homInto σ0 ρ' C' ≠ ⊥) → GlobalTheory.PRep.IsAdmissible σ0) → (killed σ0 I ≠ ⊥ → GlobalTheory.PRep.IsAdmissible σ0 → Module.rank ℂ (homInto σ0 ρ C) = Module.rank ℂ (homInto σ0 ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ ((⨆ f ∈ homInto σ0 ρ' C', LinearMap.range f) ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ ((⨆ f ∈ homInto σ0 ρ' C', LinearMap.range f) ⊓ killed ρ' I : Submodule ℂ Y) := by
  intro H _ _ S0 X Y _ _ _ _ _ _ σ0 ρ ρ' C C' I hirr hadm hrank ho ho' f f'
  classical
  have hbot : ∀ {Z : Type} [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ H Z) (B : Submodule ℂ Z),
      homInto σ0 τ B = ⊥ → (⨆ g ∈ homInto σ0 τ B, LinearMap.range g) = ⊥ := by
    intro Z _ _ τ B h
    refine iSup₂_eq_bot.2 fun g hg => ?_
    rw [h, Submodule.mem_bot] at hg
    rw [hg, LinearMap.range_zero]
  by_cases hk : killed σ0 I = ⊥
  · rw [GlobalTheory.T.isotypicSum_inf_groupAlgebraKilled_eq_bot _ _ _ σ0 ρ C I hirr hk, GlobalTheory.T.isotypicSum_inf_groupAlgebraKilled_eq_bot _ _ _ σ0 ρ' C' I hirr hk,
      finrank_bot, finrank_bot]
  by_cases h0 : homInto σ0 ρ C = ⊥ ∧ homInto σ0 ρ' C' = ⊥
  · rw [hbot ρ C h0.1, hbot ρ' C' h0.2, bot_inf_eq, bot_inf_eq, finrank_bot, finrank_bot]
  have hadm0 := hadm hk (not_and_or.1 h0)
  have hr := hrank hk hadm0
  have hdec : ∀ {Z : Type} [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ H Z) (B : Submodule ℂ Z),
      IsDecomp τ (⨆ g ∈ homInto σ0 τ B, LinearMap.range g) := by
    intro Z _ _ τ B x hx _
    refine (iSup₂_le (fun g hg => ?_) : (⨆ g ∈ homInto σ0 τ B, LinearMap.range g) ≤ irrSum τ _) hx
    rintro _ ⟨s, rfl⟩
    exact GlobalTheory.RepCount.apply_mem_irrSum hirr hadm0
      ⟨fun t => (le_iSup₂_of_le g hg le_rfl : LinearMap.range g ≤ _) ⟨t, rfl⟩, hg.2⟩ s
  refine GlobalTheory.T.finrank_killed_eq_of_equal_multiplicities H X Y ρ ρ' _ _ I (hdec ρ C) (hdec ρ' C') ?_ ho ho' f f'
  intro W _ _ σ hσ _ _
  by_cases hz : homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) = ⊥ ∧
      homInto σ ρ' (⨆ g ∈ homInto σ0 ρ' C', LinearMap.range g) = ⊥
  · rw [hz.1, hz.2, rank_bot, rank_bot]
  have he : Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
    rcases not_and_or.1 hz with h | h
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact GlobalTheory.T.nonempty_iso_of_equivariantHom_into_isotypicSum _ _ _ _ σ0 σ ρ C hirr hσ g hg hg0
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact GlobalTheory.T.nonempty_iso_of_equivariantHom_into_isotypicSum _ _ _ _ σ0 σ ρ' C' hirr hσ g hg hg0
  rw [GlobalTheory.T.rank_equivariantHomsInto_isotypicSum_of_iso _ _ _ _ σ0 σ ρ C he, GlobalTheory.T.rank_equivariantHomsInto_isotypicSum_of_iso _ _ _ _ σ0 σ ρ' C' he]
  exact hr

end GlobalTheory.Mem.R3.IsotMult

namespace GlobalTheory.Mem.R3.IsotMult

theorem isotL_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G]
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P' : LevelP L.Pg L.r ℂ) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (π : Formalism.L2.NG.FinTyp D.host.E n) (hs : L.s = 0) (hQ : L.Q = ∅) (hl : LiftsExist V β L) :
    principalLevelFrame.isotL θ P M (levS V β (withP L P')) (levChi V β (withP L P')) (gaL V β L eG c) π =
      (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f) ⊓
        killed (finRep M) (eqSet V β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) := by
  have e1 := GlobalTheory.T.goodForms_eq_killed_by_groupAlgebra θ M β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim hs hQ hl
  have htop : hPart M (levG V β (flag1L L)) (∅ : Set Empty) Empty.elim Empty.elim Empty.elim = ⊤ :=
    eq_top_iff.2 fun x _ => GlobalTheory.PartDims.mem_hPart.2 fun P hP => hP.elim
  rw [htop, inf_top_eq] at e1
  have hle : (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f) ≤ allMaps θ M :=
    iSup₂_le fun f hf => by rintro _ ⟨s, rfl⟩; exact hf.1 s
  show goodPart θ M (levS V β (withP L P')) (levChi V β (withP L P')) (gaL V β L eG c) ⊓
    principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = _
  rw [e1, GlobalTheory.T.finiteTypeIsotypicPart_eq_iSup_equivariantHoms_frame]
  exact le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
    (le_inf (le_inf (inf_le_left.trans hle) inf_le_right) inf_le_left)

end GlobalTheory.Mem.R3.IsotMult

namespace GlobalTheory.Mem.R3.IsotMult




theorem finrank_isotL_transfer (hHC : GlobalTheory.Published.HarishChandraFinite) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) (hD : CuspDecomp D) (hM : MultEq R)
    (hF : D.host.F = maximalRealSubfield D.host.E) {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (i : Fin D.R.m)
    (PW : principalLevelFrame.RowPsi (Wc D i) n) (hPY : GlobalTheory.StdFrame.StdPsi hF PY) (hPW : GlobalTheory.StdFrame.StdPsi hF PW)
    (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (P : LevelP R.Pg D.R.r ℂ) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (hfin : FiniteDimensional ℂ (principalLevelFrame.isotL R.θ PY M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 π)) :
    Module.finrank ℂ (principalLevelFrame.isotL R.θ PY M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 π) =
      Module.finrank ℂ (principalLevelFrame.isotL R.θ PW (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))
        (R.eWf i (sg0 D A)) π) := by
  classical
  obtain ⟨c, hc⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  obtain ⟨c', hc'⟩ := hC.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := GlobalTheory.PartDims.rank_zeroth_component_eq.trans (GlobalTheory.PartDims.rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.FinIsoExists.exists_isFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg hrk
    hc hc' (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg hC.lev.Pg)
  obtain ⟨h, hh⟩ := GlobalTheory.KapIsot.frames_inner (Yc D 0) (Wc D i) hF PY PW hPY hPW
    (by rw [GlobalTheory.PartDims.rank_zeroth_component_eq]; exact GlobalTheory.KapIsot.odd_r D.R) _ _ _ j Φ hΦ
  have eY := isotL_eq R.θ M₀ (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) P PY π rfl rfl
    (GlobalTheory.DimFull.liftsY' hC)
  have eW := isotL_eq R.θ (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG (RealDat.eC (A := A) (sg0 D A)) P PW π rfl rfl
    (GlobalTheory.DimFull.liftsW' hC i)
  have e3 : RealDat.eC (A := A) (sg0 D A) = RealDat.eC (A := A) D.what₂.embLL := by rw [GlobalTheory.PartDims.sign_at_base_place_eq_embedding R]
  have hl := GlobalTheory.T.isometry_matches_parahoric_levels (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ
  have e4 : killed ((finRep (R.MW i (sg0 D A))).comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC (Yc D 0)) _)
        (eqSet (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) P (∅ : Set Empty) Empty.elim
          Empty.elim Empty.elim) =
      killed (finRep (R.MW i (sg0 D A))) (eqSet (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG
        (RealDat.eC (A := A) D.what₂.embLL) P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) :=
    GlobalTheory.T.levelTypeHecke_killed_correspond_matching_iso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi (fun _ _ => 1) Φ R.eG _ P
      (∅ : Set Empty) Empty.elim Empty.elim Empty.elim _ _ hrk (fun κ => (hl κ).1) (fun κ => (hl κ).2) (fun P0 => P0.elim)
  have eF := GlobalTheory.T.isotypicSum_eq_of_frames_innerConj (Yc D 0) (Wc D i) PY PW Φ h hh _ (finRep (R.MW i (sg0 D A)))
    (allMaps R.θ (R.MW i (sg0 D A))) π
  have eY' : principalLevelFrame.isotL R.θ PY M₀ (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0 π = _ := eY
  have eW' : principalLevelFrame.isotL R.θ PW (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))
      (R.eWf i (sg0 D A)) π = _ := eW
  rw [e3, ← e4, ← eF] at eW'
  have hWle : principalLevelFrame.isotL R.θ PW (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))
      (R.eWf i (sg0 D A)) π ≤ R.Wall i (sg0 D A) :=
    inf_le_left.trans ((GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _).trans inf_le_left)
  have fW := (GlobalTheory.PartDims.finrank_comap (hC.models.HW i (sg0 D A)) hWle).2
  rw [eY'] at hfin ⊢
  rw [eW'] at fW ⊢
  haveI := GlobalTheory.PartDims.isTopologicalGroup_GA (Yc D 0)
  have hne : Nontrivial π.S := Submodule.nontrivial_iff_ne_bot.2 π.ne
  have hirr : Representation.IsIrreducible (((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) : Representation ℂ (GfC (Yc D 0)) π.S) := by
    refine GlobalTheory.KapIsot.isIrreducible_of fun U hU => GlobalTheory.OccRowVec.finRep_irr π U fun g x hx => ?_
    have := hU (GlobalTheory.KapIsot.eqv PY g) x hx
    simpa using this
  refine finrank_isot_killed_eq _ _ _ _ ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) (finRep M₀)
    ((finRep (R.MW i (sg0 D A))).comp Φ.toMulEquiv.toMonoidHom) (allMaps R.θ M₀) (allMaps R.θ (R.MW i (sg0 D A))) _ hirr
    (fun hk hor => GlobalTheory.T.isAdmissible_finiteType_frame_of_cuspMap hHC R.θ hC.models.inf (Yc D 0) (Wc D i) M₀ (R.MW i (sg0 D A)) Φ (R.βY 0)
      (R.dat0 R.triv) R.eG _ P PY π rfl rfl hk hor)
    (fun hk hadm => ?_) (fun x hx => GlobalTheory.PartDims.isOpen_stab rfl rfl hx) (fun x hx => GlobalTheory.PartDims.isOpen_stab rfl rfl hx)
    hfin fW
  rw [GlobalTheory.PartDims.homInto_comp]
  exact hM i M₀ j Φ hΦ π.S _ hirr hadm (GlobalTheory.PartDims.isGoodRep_of_killed rfl rfl (GlobalTheory.DimFull.liftsY' hC) hk)

end GlobalTheory.Mem.R3.IsotMult

namespace GlobalTheory.Mem.R3.IsotMult




theorem finrank_isotE_eq_isotL : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → ∀ (i : Fin D.R.m) (π : D.what₂.FT), Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) = Module.finrank ℂ (principalLevelFrame.isotL R.toRealDat.θ (Y.PW i) (R.toRealDat.MW i (sg0 D A3.A)) (levS _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  intro _ _ h3 _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ hX hD hM i π
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex).1
  obtain ⟨M₀, c, hc⟩ := GlobalTheory.PartDims.exists_conjModel (S' := parA (Ptw D) 0)
    (fun τ => by rw [Nat.zero_min]; exact (dualPar_dualPar _).symm) (R.toRealDat.MY 0)
  have hr := GlobalTheory.T.rank_isotypic_conjType_eq_conjModel R.toRealDat.θ (R.toRealDat.MY 0) M₀ c hc
    (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false)))
    (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false)))
    (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levL F.lv2 false D.what₂.embLL)))
    R.toRealDat.e0 R.toRealDat.e0 Y.PY (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))
    (fun k hk => GlobalTheory.PartDims.star_levChi false hk)
    (GlobalTheory.PartDims.gaL_star (L := R.toRealDat.dat0 R.toRealDat.triv) R.toRealDat.eG _ rfl rfl
      (GlobalTheory.T.star_idemOf_coeff_eq_self D.what₂.embLL A3.A.X hH.ok.ok2.irr hX))
  have hE : R.toRealDat.EEat (R.toRealDat.levR F.lv2 false) ≤ R.toRealDat.EEat R.toRealDat.triv :=
    GlobalTheory.PartDims.goodPart_le_flag (L := R.toRealDat.dat0 R.toRealDat.triv) R.toRealDat.θ _ rfl rfl _ _
  have fE : FiniteDimensional ℂ (principalLevelFrame.isotL R.toRealDat.θ Y.PY (R.toRealDat.MY 0)
      (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false)))
      (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0
      (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π)))) :=
    (GlobalTheory.PartDims.finrank_comap hC.models.HE (inf_le_left.trans hE)).2
  have f1 : FiniteDimensional ℂ (principalLevelFrame.isotL R.toRealDat.θ Y.PY M₀
      (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levL F.lv2 false D.what₂.embLL)))
      (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levL F.lv2 false D.what₂.embLL))) R.toRealDat.e0
      (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) :=
    Module.rank_lt_aleph0_iff.1 (lt_of_eq_of_lt hr.symm (Module.rank_lt_aleph0_iff.2 fE))
  have hl : R.toRealDat.levL F.lv2 false (sg0 D A3.A) = R.toRealDat.levL F.lv2 false D.what₂.embLL := by
    rw [GlobalTheory.PartDims.sign_at_base_place_eq_embedding R.toRealDat]
  rw [hl]
  refine (congrArg Cardinal.toNat hr).trans ?_
  exact finrank_isotL_transfer h3 R.toRealDat F.lv2 hC hD hM Y.hF Y.PY i (Y.PW i) Y.stdPsi.1 (Y.stdPsi.2 i) M₀
    (R.toRealDat.levL F.lv2 false D.what₂.embLL) _ f1

end GlobalTheory.Mem.R3.IsotMult
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankBaseRowsIsotypicEqGoodFormsIsotypicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.finrank_baseRows_isotypic_eq_goodForms_isotypic : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → ∀ (i : Fin D.R.m) (π : D.what₂.FT), Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) = Module.finrank ℂ (principalLevelFrame.isotL R.toRealDat.θ (Y.PW i) (R.toRealDat.MW i (sg0 D A3.A)) (levS _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  first | exact @GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL | exact GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL | (intros; apply GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL <;> assumption)
end
end
