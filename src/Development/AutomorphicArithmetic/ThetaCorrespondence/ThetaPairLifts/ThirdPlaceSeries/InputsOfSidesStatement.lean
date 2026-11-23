module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmQAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInField
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteAllLifts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeEltAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemDecIsFrob
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfRowsGuarded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatHeckeRealRd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSeriesSpecialisedUniversalDatumMemSpanStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRationalStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalTwistedSeriesDistributionOfCompatibilit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisInputs
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.admT4_of_roots_in_field : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → ∀ E : IntegralHeckeForms.XD D, IntegralHeckeForms.admT4 D.nexp E := by
  first | exact @GlobalTheory.TwInputs.admT4_of_full_compatibility | exact GlobalTheory.TwInputs.admT4_of_full_compatibility | (intros; apply GlobalTheory.TwInputs.admT4_of_full_compatibility <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeriesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.specialised_universal_series_eq_twisted_thetaSeries : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      specXi ρ Y i j b k Q M χ h P = specSer ρ Y i j b k Q M χ h P := by
  first | exact @GlobalTheory.SpecFac.specXi_eq_specSer | exact GlobalTheory.SpecFac.specXi_eq_specSer | (intros; apply GlobalTheory.SpecFac.specXi_eq_specSer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLatticeConditionOfSeriesComparisonUniversal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.SeriesTie

theorem thetaLatticeCondition_of_seriesComparison_universalChar {D : D7} {ρ : Setup D.ntw} {hρ : ρ.Good} {rd : Rds D.nexp ρ} (T : Comparison₂ hρ rd)
    (hY : GlobalTheory.UnivChar.IsUnivChar D.nexp) (hR : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatTwist hρ (rd i j b)) :
    Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp := by
  intro i hi j hj b k Q M χ hψ a hQa
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := T i j' b
  by_cases hoff : InRange D.ntw i Q ∧ ∀ a', ρ.xi i j' b D.nexp Q M (T.cls a) (T.coef a) a' ∈ Set.range (rd i j' b)
  · choose x hx using hoff.2
    rw [T.thU_eq Q M a hoff.1 x hx]
    obtain ⟨z, hz, hzr⟩ := exists_mem_thPsi_of_mem_span T (hR i hi j' b) hψ hoff.1.2.1 a
      (f := specXi ρ D.nexp i j' b k Q M χ (T.cls a) (T.coef a))
      (by
        rw [GlobalTheory.T.specialised_universal_series_eq_twisted_thetaSeries ρ hρ D.nexp hY i j' b k Q M χ hψ]
        exact GlobalTheory.T.twistedSeries_specialisedUniversalDatum_mem_span ρ hρ D.nexp hY i j' b k Q M χ hψ hoff.1 _ _ _ (T.dat a)
          fun v hv h => Finset.disjoint_left.1 hQa hv ((T.lev_iff a v).2 h))
    have e : z = Formalism.MainNotions.IntegralHeckeForms.specU D.nexp i ((j' : ℕ) + 1) b Q M k χ (grpSum D.nexp (ρ.ch i) Q M x) := by
      refine T.injective_rdK k (hzr.trans ?_)
      rw [rdK_specU_grpSum hρ (rd i j' b) k Q M χ x, specXi]
      exact Finset.sum_congr rfl fun a' _ => by rw [hx a']
    rw [← e]
    exact hz
  · rw [T.thU_off Q M a hoff, map_zero]
    exact zero_mem _

theorem thetaLatticeCondition_of_fullSeriesComparison : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    GlobalTheory.TwInputs.Laws hρ rd → Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp :=
  fun _ _ _ _ F L => thetaLatticeCondition_of_seriesComparison_universalChar F.tie F.univ fun i hi j b => (L.rat i hi j b).2.1

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

end GlobalTheory.SeriesTie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnivSupOfXi

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.TwInputs

theorem univSup_of_xi : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → Laws hρ rd → XiType rd → XiBdd rd → ∀ E : IntegralHeckeForms.XD D, UnivSup D E := by
  intro D ρ hρ rd F L hT hB E i hi j hj b a _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := F.tie i j' b
  obtain ⟨c, hc⟩ := hB i hi j' b _ _ _ (T.dat a)
  refine ⟨c, fun Q M hs hcl hS hlev => ?_⟩
  have hQ : InRange D.ntw i Q := ⟨hs, hcl, hS⟩
  have hnp : ∀ v ∈ Q, ((normProd (T.supp a) : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    fun v hv h => Finset.disjoint_left.1 hlev hv ((T.lev_iff a v).2 h)
  obtain ⟨x, hx, he⟩ := T.thU_of_rat (L.rat i hi j' b).2.2 M hQ hlev
  classical
  refine ⟨∑ a', Finsupp.single (spread D.nexp i Q M (ρ.ch i) a') (x a'), ?_, fun δ => ?_⟩
  · rw [he, grpSum, ← Finsupp.sum_finsetSum_index (fun _ => by rw [TensorProduct.zero_tmul])
      (fun _ _ _ => by rw [TensorProduct.add_tmul])]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finsupp.sum_single_index (by rw [TensorProduct.zero_tmul])]
  · have h0 : ∀ a', x a' ∈ Fm0 D.nexp i ((j' : ℕ) + 1) b :=
      fun a' => hT i hi j' b Q M hQ _ _ _ (T.dat a) hnp a' (x a') (hx a')
    have h1 : ∀ a', ((D.ntw.l i : D.ntw.O i) ^ c) • x a' ∈ D.nexp.Bsup i ((j' : ℕ) + 1) b :=
      fun a' => hc Q M hQ hnp a' (x a') (hx a')
    rw [Finsupp.finsetSum_apply]
    refine ⟨Submodule.sum_mem _ fun a' _ => ?_, ?_⟩
    · rw [Finsupp.single_apply]; split_ifs
      · exact h0 a'
      · exact zero_mem _
    · rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun a' _ => ?_
      rw [Finsupp.single_apply]; split_ifs
      · exact h1 a'
      · rw [smul_zero]; exact zero_mem _

end GlobalTheory.TwInputs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalTwistedSeriesDistributionOfCompatibilitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.universalTwistedSeriesDistribution_of_compatibility : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → Laws hρ rd → ThURel D.nexp := by
  first | exact @GlobalTheory.DistRel.thURel_of_fullTie | exact GlobalTheory.DistRel.thURel_of_fullTie | (intros; apply GlobalTheory.DistRel.thURel_of_fullTie <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InputsOfSides

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwInputs
theorem exists_inputs_of_hkSup_galHodge : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator →
    ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ G : _root_.GlobalTheory.TwInputs.GalSideAlt D,
      (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd →
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd →
      (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
      ∃ N0, Inputs D E N0 := by
  intro hCh hArt hTor D X E Y G hRat hBdd hSup hHodge hRoots
  obtain ⟨a1, a2, a8, good, sig, ⟨N0, a9⟩, a10, hyp⟩ := _root_.GlobalTheory.TwGalInputs.galois_inputs_alt hCh hArt hTor D G hHodge
  have hUnit : ∀ i b P, P ∉ D.ntw.S0 i → ∃ u : (D.ntw.O i)ˣ, Y.H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u := by
    intro i b P hP
    obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
    exact ⟨Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom
      (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹), Y.del i b P hP σ hσ⟩
  have hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (Y.S.A j).IsKsForm := by
    intro j h1 h2
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
    exact GlobalTheory.isKsForm_of_formsIso _ _ (Y.YS.fi ⟨n, h2⟩) (X.integral ⟨n, h2⟩).1
  have hL : Laws Y.Z.good Y.Z.rd := by
    refine ⟨fun i j b => ?_, fun i j b => ?_, fun i j b => ?_, fun i hi j b => Y.Z.rat (hRat i hi j b)⟩
    · exact GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
        (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j)
        (hKs _ (Nat.le_add_left _ _) j.2)
    · exact GlobalTheory.SeriesTie.actRead_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
        Y.Z.pin X.unif X.char.models.HW
    · exact Y.Z.heckeRead (GlobalTheory.SeriesTie.HkRat.ratHecke_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
        Y.Z.pin (X.char.lev.mu0 j) (GlobalTheory.SplitOffS0.main Y.Z.good i _ (Y.Sb i)) Y.H.hL
        (Y.H.hs _ (Nat.le_add_left _ _) j.2) Y.reads)
  have hLevel : Y.Z.ρ.LevelOf D.nexp :=
    ⟨fun i j b g => (Y.Z.tie i j b).U_eq g, fun i j b u hu => (Y.Z.tie i j b).psiU_eq u hu⟩
  have hXi : XiType Y.Z.rd := GlobalTheory.XiTypeProof.xiType D Y.Z.ρ Y.Z.good Y.Z.rd hL.faithful hL.act hLevel
  have hSupLaws : SupG D ∧ SupFull D ∧ SupHk D ∧ CommG D ∧ HkComm D := by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.twistedFormSupLattice_full_groupStable_of_eq_rational D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS Y.sup X.integral
    obtain ⟨h3, h4⟩ := GlobalTheory.HkSupComm.supHk_commG D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS Y.H Y.sup X.char.lev X.char.allPl
      (fun i => (X.integral i).2.1) hSup Y.reads (fun i b P h _ => hUnit i b P h)
    have hC : GlobalTheory.ExportPin.Model.Covered X.R := GlobalTheory.ExportPin.Model.covered_of_allPlaces X.R X.char.lev X.char.allPl
    have hComm : HkComm D := by
      exact hkComm_of_family X.R X.cG Y.S Y.YS Y.H.hL Y.H.hs Y.H.cHk Y.H.hkEq fun i j a b k P k' P' hk hk' =>
        family_comm X.R X.cG Y.S Y.YS X.char.lev X.char.fam X.char.models.HW
          (fun n => GlobalTheory.ExportPin.Model.j_injective X.R X.unif n _) hC Y.H.hL
          (fun i n k P hk α R ha hR => ⟨_, fun x => Y.reads n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) hk.2.1 α R ha hR x⟩)
          i j a b k P k' P' hk hk'
    exact ⟨h1, h2, h3, h4, hComm⟩
  obtain ⟨supG, supFull, supHk, commG, comm⟩ := hSupLaws
  have hSS : HkSS D := by
    have hX : Formalism.IndefR.NX.NExpHeckeRowX X.R X.cG Y.S Y.YS Y.H (fun j => Formalism.IndefR.NX.goodProjW Y.S j D.nexp.eLL0) :=
      ⟨fun i k P hs ho _ _ hk α R hα hR x _ => Y.reads i k P hs ho hk α R hα hR x⟩
    exact GlobalTheory.GoodSpan.hkSS_of_rows_guarded X.R X.F X.cG Y.S Y.YS Y.H commG comm supFull hX X.char X.unif X.integral
      (fun i P P' hP hc => Y.Z.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => Y.Z.good.goodSetup_placesOverTwo_subset i) Y.Sb
      (fun i _ j hj b k P hk x => Y.hk_emb i j b k P x (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hk)
      Y.B_range Y.hk_split
  exact ⟨N0,
    { a1 := a1
      a2 := a2
      a8 := a8
      good := good
      sig := sig
      a9 := a9
      a10 := a10
      univChar := Y.Z.univ
      off := Y.off
      rel := GlobalTheory.T.universalTwistedSeriesDistribution_of_compatibility D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL
      l3 := GlobalTheory.SeriesTie.thetaLatticeCondition_of_fullSeriesComparison D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL
      t4 := GlobalTheory.T.admT4_of_roots_in_field D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hRoots E
      type := GlobalTheory.ExportType.typeKept_of_fullTie D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL.act E
      univ := univSup_of_xi D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL hXi hBdd E
      supG := supG
      supFull := supFull
      supHk := supHk
      commG := commG
      comm := comm
      ss := hSS
      hyp := hyp }⟩
end GlobalTheory.TwInputs
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InputsOfSidesStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_inputs_of_galHodgeN_roots : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ G : _root_.GlobalTheory.TwInputs.GalSideAlt D, (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → ∃ N0, Inputs D E N0 := by
  first | exact @_root_.GlobalTheory.TwInputs.exists_inputs_of_hkSup_galHodge | exact _root_.GlobalTheory.TwInputs.exists_inputs_of_hkSup_galHodge | (intros; apply _root_.GlobalTheory.TwInputs.exists_inputs_of_hkSup_galHodge <;> assumption)
end
end
end
