module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionTrivialOffSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrame
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLifts

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistTypeDet


open Classical in
theorem detChar_eq_one_of_suppAt : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  intro D S T B hB _ A _ t ht hadm u κ hlift hsupp
  have hst : Lev.finE T κ ∈ St B.F.βT := Formalism.L2.DIV.parLev_St hlift.2.1
  rw [GlobalTheory.TwistDetStabAll.detChar_eq_prod_res B hB t ht hlift.1 hst]
  refine Finset.prod_eq_one fun PP hPP => ?_
  obtain ⟨P, hPg, hQ, hsplit⟩ := hadm.1.split
  have hnot : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.mp hadm.1.disj h (Finset.mem_union_right _ hPP)
  rw [GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT hsplit hPg (hQ (Finset.mem_union_right _ hPP)) hnot hst hsupp,
    map_one, map_one]

end GlobalTheory.TwistTypeDet
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodTwist_detChar_eq_one_of_supported_typePlaces : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  first | exact @GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt | exact GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt | (intros; apply GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLiftsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_type_under_supported_lifts : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T), series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  first | exact @GlobalTheory.TypeSupportLift.series_type_supp | exact GlobalTheory.TypeSupportLift.series_type_supp | (intros; apply GlobalTheory.TypeSupportLift.series_type_supp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiType

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiTypeProof

theorem xiType : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) →
    (∀ i j b, ActRead (rd i j b)) → ρ.LevelOf D.nexp → XiType rd := by
  intro D ρ hρ rd hF hA hL i _ j b Q M hQ s h P _ _ a x hx
  unfold Formalism.MainNotions.IntegralHeckeForms.Fm0
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D _ D.ntw ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have hu : ρ.eG i j b u ∈ (ρ.B i j b).G.P.H := (hL.U_eq i j b u).2 u.2
  obtain ⟨κ, hlift, hsupp, hser⟩ := GlobalTheory.T.thetaSeries_type_under_supported_lifts D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ (hρ.weil_base i j b) _ hu
  have hg := GlobalTheory.UnivGood.univOf_good D _ D.ntw ρ hρ D.nexp i Q M
  have hdet : detChar (Wc D j) ((univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))) κ = 1 := by
    apply Multiplicative.toAdd.injective
    funext PP
    have := GlobalTheory.T.goodTwist_detChar_eq_one_of_supported_typePlaces D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ ⟨{PP.1}, _, _⟩ (hg.2 PP.1 PP.2)
      (hadm.mono (by simpa using PP.2)) _ κ hlift hsupp
    exact congrArg Multiplicative.toAdd this
  apply (hF i j b).injective
  funext g
  change rd i j b (D.nexp.actG i _ b u x) g = rd i j b (((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x) g
  rw [hA i j b u κ hlift, map_smulₛₗ, Pi.smul_apply, hx]
  unfold Setup.xi
  rw [Base.xiCoef_apply, Base.xiCoef_apply, detChar_mul hg.delQ_real, hdet, mul_one]
  refine (hser _ hadm _ h P g).trans ?_
  rw [hL.psiU_eq i j b u hu, smul_eq_mul]
  rfl

end GlobalTheory.XiTypeProof
end
end
