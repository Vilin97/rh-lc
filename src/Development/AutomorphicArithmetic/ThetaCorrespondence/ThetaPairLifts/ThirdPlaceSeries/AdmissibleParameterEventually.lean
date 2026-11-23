module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedLift
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfLargeResidueChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersOfLargeScale
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundExtendedOfRationalBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwistsStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorIner
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholzeStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnit
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionFourOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraExtraStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraFurtherStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraMoreStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraTerStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpBoundOfFactsLargeFamilyStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionary

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AdmissibleDictionary

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  exact GlobalTheory.TameFixedLift.main D.nd i

end GlobalTheory.AdmissibleDictionary
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerCharStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.aux₃ D HW F := by
  first | exact @GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt | exact GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt | (intros; apply GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorInerStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  first | exact @GlobalTheory.UseFive.objects_globalStep_gen | exact GlobalTheory.UseFive.objects_globalStep_gen | (intros; apply GlobalTheory.UseFive.objects_globalStep_gen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnitStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  first | exact @GlobalTheory.CutCoreUnit.main | exact GlobalTheory.CutCoreUnit.main | (intros; apply GlobalTheory.CutCoreUnit.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostRamificationIdxEqOne

section

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem host_ramificationIdx_eq_one :
    ∀ (D : D7) (p : ℕ), p.Prime → p ∉ D.host.small → p ≠ D.host.q → p ≠ D.host.d → ∀ P ∈ placesOver D.host.E p, P.asIdeal.ramificationIdx ℤ = 1 :=
  fun D _ hp h2 hq hd P hP => GlobalTheory.HubLoc.ramIdx_eq_one D.host hp (UpperTheory.Small.not_dvd_condN D.host hp h2 hq hd) P hP

end GlobalTheory.TripleGal
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraBis

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.AdmissibleSetting
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r := by
  intro D L nch i r π ρ fa _ _ _ hr _ _
  exact ⟨_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i r fa.Conclusion1.1 hr, Formalism.MainNotions.N.continuous_family_of D i r hr,
    Formalism.MainNotions.N.semisimple_family_of D i r hr⟩
end GlobalTheory.AdmissibleSetting
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraBisStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.admG1_continuous_admSS_of_rank_r_summand : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r := by
  first | exact @_root_.GlobalTheory.AdmissibleSetting.main_alt_alt | exact _root_.GlobalTheory.AdmissibleSetting.main_alt_alt | (intros; apply _root_.GlobalTheory.AdmissibleSetting.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraRest

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.QuadAtQ
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1 := by
  intro D L nch i r π ρ fa _ _ hHG hr _ _ v hv
  exact ⟨fun x _ γ hγ => ((galois_condition_five_of D i r fa.Conclusion2.1 hHG hr v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ,
    ((GlobalTheory.TameDesign.main D i).2 v (Or.inr hv)).2.2.1 hv⟩
end GlobalTheory.QuadAtQ
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraRestStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.quadAt_and_zeta_ne_one_of_large_place : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1 := by
  first | exact @_root_.GlobalTheory.QuadAtQ.main_alt_alt | exact _root_.GlobalTheory.QuadAtQ.main_alt_alt | (intros; apply _root_.GlobalTheory.QuadAtQ.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleParameterEventually

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
private theorem admissible_parameter_eventually {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (a : Fm.Ix x), AdmissibleParameterJ.AdmPar (Fm.L x a) := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  exact (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1
theorem GlobalTheory.NLinkE.main_alt_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x i) (Fm.ex x hx i).nch → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at (Fm.D x i) (Fm.L x i) := by
  intro hP eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.T.exists_localPositionData_off_exceptional_primes Fm
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.T.eventually_prvJ_of_facts Fm
  obtain ⟨x3, h3⟩ := admissible_parameter_eventually Fm
  refine ⟨max (max x1 x2) x3, fun x hx' hx1 a hF => ?_⟩
  have hx : max x1 x2 ≤ x := le_trans (le_max_left _ _) hx'
  have hA := h3 x (le_trans (le_max_right _ _) hx') hx1 a
  have hJ := h2 x (le_trans (le_max_right _ _) hx) hx1 a hF
  intro k hl hg hexc _hW hHG r hr π hπ ρ hρ
  have hlp : (Fm.D x a).nd.l k |>.Prime := ((Fm.D x a).nd.lPrime k).out
  obtain ⟨⟨h5, ht, hq, hd, hsm⟩, hposition⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 a hJ _ hlp hl
  have hur := GlobalTheory.TripleGal.host_ramificationIdx_eq_one (Fm.D x a) _ hlp hsm hq hd
  have heps := GlobalTheory.AdmissibleDictionary.main (Fm.D x a) k
  obtain ⟨g1, gc, gss⟩ := _root_.GlobalTheory.T.admG1_continuous_admSS_of_rank_r_summand _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g3 := _root_.GlobalTheory.T.admG3_of_isRankR_of_lStar_lt _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g2 := _root_.GlobalTheory.T.admG2_of_isRankR_of_lStar_lt hP.font _ _ _ k r π ρ hF hA hl hg hHG hr hπ hρ
  obtain ⟨gno, gunr⟩ := _root_.GlobalTheory.T.noChiOff_and_unrOut_of_large_good_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gS := _root_.GlobalTheory.T.quadAt_unit_zeta_sub_one_or_polyAt _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gQ := _root_.GlobalTheory.T.quadAt_and_zeta_ne_one_of_large_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition k r (fun _ => ρ) π := hρ.2
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia _ k r (fun _ => ρ) π hr g1 g3 gc gss gdec heps g3.2.2 hπ hur ht
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x a)
  have hTOP := GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar hP.bk hP.tate hP.euler (Fm.D x a) HW F Cm
  have hloc := GlobalTheory.UseLoc.main (Fm.D x a) HW F k r (fun _ => ρ) π hTOP (GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists _ HW F) hJ.1 hr hπ g2 g3 gc gdec heps h5 hsm hq hd
    (fun n _ up τ => hposition hexc _ ((Fm.D x a).nd.j_range k).1 ((Fm.D x a).nd.j_range k).2 n up τ)
  exact GlobalTheory.T.congruenceBound_extended_of_rationalBound _ k π ρ hπ (fun v hv => (gQ v hv).2)
    (fun hs hsha => GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit hP.artin _ k r _ π S hr hS hπ gno gunr gS gQ hloc hs hsha)
end
end
end
