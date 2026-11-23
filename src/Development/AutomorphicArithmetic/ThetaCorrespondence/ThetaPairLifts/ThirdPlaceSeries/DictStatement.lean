module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.InstMainA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffGp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerMoreStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityEighth

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.StrSplitDict.cast_ne_zero : ∀ (D : D7) (μ : D.what₂.Tup) (a b : ℕ) (h : a = b) (f : D.what₂.Mt μ a), f ≠ 0 → (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  intro D μ a b h f hf
  subst h
  exact hf
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocCompHasSatake

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.SplitSatLoc
section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
end Local
section Key
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
end Key
section Main

theorem exists_locComp_hasSatake_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ B : Multiset ℂˣ, B.card = D.R.nV → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k • F) → ∃ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ ∧ GlobalTheory.SmGL.HasSatake σ.ρ α ∧ Finset.univ.val.map α = B := by
  intro _ hL D P i Q sp hJ B hB F hFiso hFty hF0 hFeig
  have hirr := P.H.av.irr i Q
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV
    ({ (P.M.loc i).wt with S := P.H.av.S i Q, irrS := hirr } : NG.AutRep D.host.E D.R.nV) sp
  have hσ' : IsLocS (P.H.av.S i Q) sp σ := hσ
  obtain ⟨c, T0, hc, hcL, -, -, -⟩ := hσ'
  have hFfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ F = F := by
    intro κ hκ ht
    have hJκ := ((hJ κ ht).1).2 hκ
    have h1 := hFty.2 ⟨κ, hJκ⟩
    rw [(hJ κ ht).2 hJκ] at h1
    simpa using h1
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) hirr sp σ hσ c hc hcL
    (Formalism.UG.GLint (Fin D.R.nV) (sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) 1
    (fun g hg => hg) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) F hFiso hF0
    (fun κ ht h => by
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      exact hFfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff sp ht).1 h) ht)
  have hufix : u ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL sp.w (n := D.R.nV)) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    have hA' := (map_mem_KGL_iff hc hcL (Matrix.GeneralLinearGroup.map c.symm.toRingHom A)).1
      (by rw [map_map_symm]; exact hA)
    have := hu _ hA'
    rwa [map_map_symm, MonoidHom.one_apply, Units.val_one, one_smul] at this
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := by
    have : u ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (sp.w.adicCompletion D.host.E) (Fin D.R.nV)) := by
      rw [GlobalTheory.HeckeEigConj.KO_eq_KGL D.host.E sp.w D.R.nV]; exact hufix
    exact (Submodule.ne_bot_iff _).2 ⟨u, this, hu0⟩
  have hR := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt hR ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hR σ).2 hsph)
  have hSat := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake D.host.E sp.w D.R.nV σ.V σ.ρ α hα
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E D.R.nV sp
  have hspan := GlobalTheory.SpanLoc.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) hirr sp σ hσ c hc hcL hFiso
  rw [iSup_subtype'] at hspan
  have hFK : F ∈ GlobalTheory.PRep.fixed (locAct D.R.nV (P.M.loc i).wt.W sp c e) (GlobalTheory.LFun.KGL sp.w (n := D.R.nV)) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    rw [locAct_apply]
    refine hFfix _ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff sp (he1 _)).1 ?_) (he1 _)
    rw [he2]
    exact (map_mem_KGL_iff hc hcL _).1 (by rw [map_map_symm]; exact hA)
  have hspan' : F ∈ ⨆ T : {T : σ.V →ₗ[ℂ] (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) // (∀ v, T v ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {sp.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (sp.loc D.R.nV x)) v) = NG.rt D.host.E D.R.nV x (T v)}, LinearMap.range T.1 := hspan
  have hequiv : ∀ (T : {T : σ.V →ₗ[ℂ] (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) // (∀ v, T v ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {sp.v} x → ∀ v, T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (sp.loc D.R.nV x)) v) = NG.rt D.host.E D.R.nV x (T v)}) g v, T.1 (σ.ρ g v) = locAct D.R.nV (P.M.loc i).wt.W sp c e g (T.1 v) := by
    intro T g v
    rw [locAct_apply, ← T.2.2 _ (he1 _) v, he2, map_map_symm]
  have hIs : GlobalTheory.LFun.IsSatVecGL sp.w (locAct D.R.nV (P.M.loc i).wt.W sp c e) F (Finset.univ.val.map α) :=
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := locAct D.R.nV (P.M.loc i).wt.W sp c e) σ.irr hSat
      Subtype.val hequiv hspan' hFK hF0
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := maximalRealSubfield D.host.E) sp.v
  have hϖ' : IsUnif D.host.E sp.v ϖ := hϖ
  have heq : ∀ k ≤ D.R.nV, GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV (Finset.univ.val.map α) k =
      GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k := by
    intro k hk
    have h1 := hIs.2.2.2 (c ϖ) (isUnifV_map hc hcL hϖ') k hk
    rw [← heckeD_eq_heckeVec sp c hc hcL e he1 he2 _ (fun κ ht => (hJ κ ht).1) hϖ' k hFfix, hFeig ϖ hϖ' k hk] at h1
    exact (smul_left_injective ℂ hF0 h1).symm
  exact ⟨σ, α, hσ, hα, GlobalTheory.LFun.eq_of_satEig_eq (GlobalTheory.LFun.qV_ne_zero sp.w) (by simp) hB heq⟩
end Main
end GlobalTheory.SplitSatLoc
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocCompHasSatakeStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.iso_type_space_maximal_compact_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ B : Multiset ℂˣ, B.card = D.R.nV → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E sp.w) D.R.nV B k • F) → ∃ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ ∧ GlobalTheory.SmGL.HasSatake σ.ρ α ∧ Finset.univ.val.map α = B := by
  first | exact @_root_.GlobalTheory.SplitSatLoc.exists_locComp_hasSatake_alt | exact _root_.GlobalTheory.SplitSatLoc.exists_locComp_hasSatake_alt | (intros; apply _root_.GlobalTheory.SplitSatLoc.exists_locComp_hasSatake_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffGpStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isSplit_of_hk3_good : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ sp : SplitPlace D.host.E, sp.w = w ∧ (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) := by
  exact _root_.GlobalTheory.OffBad.offbad_alt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocVUnrFrobEigOfHasSatake

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LlcSplit
theorem locV_unr_frobEig_of_hasSatake_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ → GlobalTheory.SmGL.HasSatake σ.ρ α → D.naut.unr (D.naut.locV i Q sp.w) ∧ D.naut.frobEig (D.naut.locV i Q sp.w) = Finset.univ.val.map (fun k => (((α k)⁻¹ : ℂˣ) : ℂ)) := by
  intro hL D P i Q sp σ α hS hα
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hS
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w,
    _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 sp.w)) hα] at h3
  have hu : D.naut.unr (D.naut.locV i Q sp.w) :=
    (P.T.unr _ _).2 (by rw [h3]; exact (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _))
  refine ⟨hu, ?_⟩
  rw [P.T.frobEig _ _ hu, h3, GlobalTheory.WeilDeligne.WD.frobEig_diag]
end GlobalTheory.LlcSplit
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocVUnrFrobEigOfHasSatakeStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unr_and_frobEig_eq_inv_satake : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ → GlobalTheory.SmGL.HasSatake σ.ρ α → D.naut.unr (D.naut.locV i Q sp.w) ∧ D.naut.frobEig (D.naut.locV i Q sp.w) = Finset.univ.val.map (fun k => (((α k)⁻¹ : ℂˣ) : ℂ)) := by
  first | exact @_root_.GlobalTheory.LlcSplit.locV_unr_frobEig_of_hasSatake_alt | exact _root_.GlobalTheory.LlcSplit.locV_unr_frobEig_of_hasSatake_alt | (intros; apply _root_.GlobalTheory.LlcSplit.locV_unr_frobEig_of_hasSatake_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Dict

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.StrSplitDict.dict_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ D.naut.unr (D.naut.locV i Q w) ∧ (B w).map (fun a : ℂˣ => (a : ℂ)) = (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hh s B hs hB w hw hsp
  have hrank : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨sp, hspw, hJ⟩ := _root_.GlobalTheory.T.isSplit_of_hk3_good hAF hL D P X hA h41 h7 htl i w hw hsp
  have hv : w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) :=
    (GlobalTheory.DownLift.Params.good_iff _ _ _).1 hw
  rcases hB _ hv w rfl with ⟨-, hcard, heq⟩ | ⟨hin, -⟩
  swap
  · exact absurd hsp (GlobalTheory.LFun.not_isSplit_of_isInertAt hin)
  rw [hrank] at hcard heq
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hy0
    have h1 : X.R.extV j (X.tupT (D.nd.mu i)) y = 0 := by
      rw [hy]
      show (X.IL.jMt (D.nd.mu i) hμ j 0).1 = 0
      simp only [map_zero, ZeroMemClass.coe_zero, Submodule.coe_zero]
    exact X.hinj j (X.tupT (D.nd.mu i)) (h1.trans (LinearMap.map_zero _).symm)
  have hf'0 := GlobalTheory.StrSplitDict.cast_ne_zero D _ _ _ hj f hf0
  subst hspw
  have htr := _root_.GlobalTheory.T.extension_vector_theta_compatible_alt hAF hL D P X hA h41 h7 htl i hμ j hj f y hy h hh s hs sp hw hJ
  obtain ⟨Q, hQx, F, hFi, hFt, hF0, hFe⟩ := _root_.GlobalTheory.T.exists_automorphic_vector_satake_alt hL D P i x _ hf hf'0 sp
    (fun k => s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) htr
  obtain ⟨σ, α, hloc, hsat, hα⟩ := _root_.GlobalTheory.T.iso_type_space_maximal_compact_alt hAF hL D P i Q sp hJ (B sp.w) hcard F hFi hFt hF0
    (fun ϖ hϖ k hk => by rw [hFe ϖ hϖ k hk, heq k hk])
  obtain ⟨hu, hfr⟩ := _root_.GlobalTheory.T.unr_and_frobEig_eq_inv_satake hL D P i Q sp σ α hloc hsat
  refine ⟨Q, hQx, hu, ?_⟩
  rw [hfr, ← hα]
  simp [Multiset.map_map, Function.comp_def]
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DictStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.theta_eigen_compatibility_eighth_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ D.naut.unr (D.naut.locV i Q w) ∧ (B w).map (fun a : ℂˣ => (a : ℂ)) = (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) := by
  first | exact @_root_.GlobalTheory.StrSplitDict.dict_alt | exact _root_.GlobalTheory.StrSplitDict.dict_alt | (intros; apply _root_.GlobalTheory.StrSplitDict.dict_alt <;> assumption)
end
end
end
