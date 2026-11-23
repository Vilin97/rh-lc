module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeInfinitesimalCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeLocalLanglandsAtTrivialTwist
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MGoodRef

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInf

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LiftChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG



theorem charAt (D : D7) (cf : CharFrame D) (C : CharSide D cf) (j : Fin D.R.m) :
    ∃ μ : D.naut.CG 1, (C.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧
      (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧
      ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧
        D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  have hm := cf.isMu0 j
  refine ⟨C.e1.symm ⟨cf.mu0 j, hm.unitary⟩, by simp, ?_, ?_, ?_⟩
  · rw [C.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ hm.triv
  · intro w hw
    refine ⟨(C.unr_iff _ w).2 ?_, (C.unr_iff _ w).2 ?_⟩
    · rw [Equiv.apply_symm_apply]
      refine hm.unr w fun k hk => hw ?_
      exact (Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1
    · rw [C.etaTinv]
      intro x hx
      have := cf.isEta.unr w x hx
      show ((cf.eta.loc w) x)⁻¹ = 1
      rw [this, inv_one]
  · have hinf : (C.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => -(1/2 : ℚ)) := by
      rw [C.etaTinv]
      refine ⟨fun _ => -1, fun _ => by norm_num, fun k => ?_⟩
      have h := cf.isEta.inf k
      show (((cf.eta.inf k)⁻¹ : ℂˣ) : ℂ) = _
      rw [Units.val_inv_eq_inv_val, h]
      simp only [zpow_one, zpow_neg_one, Finset.prod_inv_distrib]
    intro τ
    obtain ⟨h1, h2⟩ := C.infG _ _ hinf (D.eTau τ)
    refine ⟨?_, ?_⟩
    · show D.naut.infG _ (embPsi D.host (D.eTau τ)) = _
      rw [h1]
      congr 1
      push_cast
      ring
    · show D.naut.infG _ ((starRingEnd ℂ).comp (embPsi D.host (D.eTau τ))) = _
      rw [h2]
      congr 1
      push_cast
      ring

end GlobalTheory.LiftChar

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeCentralCharacterEqCompNorm

section

@[expose] public section



section
section
noncomputable section
namespace GlobalTheory.LiftChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG


theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ _ a _ => ∀ j : Fin D.R.m, ∃ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧ (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧ ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  intro _ hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows EvLgG
  refine evG_all fun K => lg_all K fun B f T _ => ?_
  intro _ w _ Z Wt hX z p0 Y _ _ _ _ _ Rw a M tup Q _ _
  exact charAt _ _ a.chr
end GlobalTheory.LiftChar
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.infG_embTau_eq_neg_half_and_embTauBar_eq_half : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ _ a _ => ∀ j : Fin D.R.m, ∃ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧ (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧ ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  first | exact @_root_.GlobalTheory.LiftChar.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LiftChar.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LiftChar.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.standardFrame_nonsplit_maxCompact_in_level : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (i : Fin (w.st Z).toD7.R.m)
      (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV), StdFrame Y.hF P →
      ∀ w' : PlE (w.st Z).toD7.host, ¬ IsSplitPl (w.st Z).toD7.host w' →
      ∀ κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
        TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ →
        P.ψ κ ∈ Formalism.IndefR.Links.levS _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)) ∧
          Formalism.IndefR.Lev.levChi _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false))
            (P.ψ κ) = 1 := by
  first | exact @GlobalTheory.NonSplitLevel.lift_level | exact GlobalTheory.NonSplitLevel.lift_level | (intros; apply GlobalTheory.NonSplitLevel.lift_level <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MSphInert

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open GlobalTheory.SphInertRef
noncomputable section
theorem UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → SphericalInertData.SphInert D.nd D.naut D.nbc j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) := by
  have hLvl := GlobalTheory.T.standardFrame_nonsplit_maxCompact_in_level
  intro hP hL
  have hG := _root_.UpperTheory.One.M.goodRef_alt hP hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hG ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hLvl hG (fun K B f T w Z Wt hX z p0 Y h hg => ?_)
  intro Rw a M tup Q hMA hx j h1 h2 S hS hne w' hw'
  have hgood := hg Rw a M tup Q hMA hx j h1 h2 S hS hne
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, i.1 + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  rw [a.A.sph (i.1 + 1) h1 h2 _ w' (HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w') hw' rfl]
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hry : (M _ _ h1 h2).real y ≠ 0 := fun e =>
    hy0 ((M _ _ h1 h2).real_inj (e.trans (map_zero _).symm))
  obtain ⟨f, hf, hf0, hff⟩ := GlobalTheory.AutUnr.exists_fixed_of_isoTyp _ hS.1.stable
    {κ | κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV ∧
      TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ} hy hry
    (fun κ hκ => rt_real_eq_of_lev hMA i y κ (h i (hMA.PV i) (hMA.std i) w' hw' κ hκ.1 hκ.2).1
      (h i (hMA.PV i) (hMA.std i) w' hw' κ hκ.1 hκ.2).2)
  exact _root_.UpperTheory.One.M.New.sphMk ⟨f, hf, hf0, fun κ hU htr => hff κ ⟨hU, htr⟩⟩ fun _ => hgood
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalBaseChangeInertCompatible

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.SphInertRef
section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}
end Read
end GlobalTheory.SphInertRef
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.sph_inert_cls_of_iso_typ_comap_ne_bot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → SphericalInertData.SphInert D.nd D.naut D.nbc j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) := by
  first | exact @_root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot | exact _root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot | (intros; apply _root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeLocalCompatibleAllPlaces

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.LiftRef
theorem baseChange_local_compatible_all_places_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → LiftAll (w.st Z).toD7 Rw := by
  intro hP hL
  have h := overRows_and_mono (_root_.GlobalTheory.T.infG_embTau_eq_neg_half_and_embTauBar_eq_half hP hL) (_root_.GlobalTheory.T.baseChange_localLanglands_at_trivial_twist_alt hP hL) (fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b)
  have h' := overRows_and_mono h (_root_.GlobalTheory.T.sph_inert_cls_of_iso_typ_comap_ne_bot hP hL) (fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b)
  refine overRows_and_mono h' (_root_.GlobalTheory.T.baseChange_infinitesimalCharacter_alt hP hL) ?_
  rintro K B f T w Z Wt hX z p0 Y ⟨⟨hc, hl⟩, hs⟩ hi Rw a M tup Q hA hI j h1 h2 σ hσ
  obtain ⟨S, hS, hm, hloc⟩ := hl Rw a M tup Q hA hI j h1 h2 σ hσ
  obtain ⟨μ, hμ, hcsd, hunr, heta⟩ := hc Rw a M tup Q hA hI ⟨j - 1, by omega⟩
  exact ⟨_, μ, ⟨hcsd, hunr, hs Rw a M tup Q hA hI j h1 h2 S hS hm, hloc μ hμ, heta, hi Rw a M tup Q hA hI j h1 h2 S hS μ hμ⟩⟩
end GlobalTheory.LiftRef
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.liftAll_of_parIn_of_mtInput : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → LiftAll (w.st Z).toD7 Rw := by
  first | exact @_root_.GlobalTheory.LiftRef.baseChange_local_compatible_all_places_alt | exact _root_.GlobalTheory.LiftRef.baseChange_local_compatible_all_places_alt | (intros; apply _root_.GlobalTheory.LiftRef.baseChange_local_compatible_all_places_alt <;> assumption)
end
end
end
end
