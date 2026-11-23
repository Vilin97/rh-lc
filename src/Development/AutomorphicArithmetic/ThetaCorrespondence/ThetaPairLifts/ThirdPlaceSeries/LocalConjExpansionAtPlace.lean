module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumKeepingLattice
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvaluatesOfUnif
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateFunctionAtPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)

theorem GlobalTheory.PlaceRead.evaluates_of_lunif {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : Formalism.L2.Pj.CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hu : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV ?_
  by_contra hne
  have h0 := fw.ev0 i σ hσ hV hne
  have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := fun x => by
    by_contra hx
    have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
    have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
    rw [h0] at h2
    exact h2 rfl
  refine hne ⟨0, fun f => ?_⟩
  have hf : f = 0 := (fw.e i).injective (Subtype.ext ((hx _).trans (hx _).symm))
  subst hf
  refine Eq.trans ?_ (GlobalTheory.phiC_zero_rule T hV (wtA (κ i))).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalConjExpansionAtPlace

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)
theorem GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  intro _ D X X0 Y S YS Z c w j _ τ _ ζ Φ Φ' hC n a f hΦ
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls.base_of_tie (i := j) X.geo.fw
  have hso : (X.geo.O j).s0 = res X.core (sg0 _ X.A3.A) :=
    (sOv_eq X.core.toCore (X.geo.O j).c' (X.geo.O j).hle).trans hb.1.symm
  have hev := GlobalTheory.PlaceRead.evaluates_of_lunif X.geo.fw X.unif j (sg0 _ X.A3.A) hb.2.1 hb.2.2
  let cf : NX.FmK S ((j : ℕ) + 1) → X.core.cuspA ((j : ℕ) + 1) (wtA (X.geo.κ j)) (X.geo.κ j).n := fun g =>
    (X.geo.fw.e j).symm ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩
  have hread : ∀ (g : NX.FmK S ((j : ℕ) + 1)) h,
      (lieFac (X.core.Q.Dw ((j : ℕ) + 1)) (xiR D) (wtA (X.geo.κ j)) : ℂ) *
      (X.geo.O j).phi (X.core.cE ((j : ℕ) + 1) (X.geo.O j).s0) (cf g : X.core.R ((j : ℕ) + 1)) h =
        evW YS X.geo.v₀ j g.val h := by
    intro g h
    rw [phi_cE X.core X.R.toRealDat X.geo.O j]
    refine Eq.trans ?_ ((congrFun (hev (cf g)) h).symm.trans ?_)
    · exact congrFun (GlobalTheory.LiftRatObj.phiC_congr X.core hso (X.geo.O j).hV hb.2.2 _ _) h
    · have he : X.geo.fw.e j (cf g) = ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩ := LinearEquiv.apply_symm_apply _ _
      exact congrArg (fun x : (X.R.FW j).WK => (X.R.HW j (sg0 D X.A3.A)).e ((X.R.FW j).j (sg0 D X.A3.A) x.val)
        (X.geo.v₀ j (sg0 D X.A3.A)) h) he
  have h1 : Expands (X.geo.O j) (X.geo.κ j) Φ a fun k => cf (f k) := fun h => by
    rw [hΦ, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (hread _ _).symm
  have h2 := hC.2 n a _ h1
  funext h
  rw [h2 h, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact (congrArg (fun z => ζ * τ (a k) * z) (hread (f k) h)).trans (mul_assoc _ _ _)
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.GlobalTheory.T.local_conj_expansion_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  first | exact @_root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer | exact _root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer | (intros; apply _root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer <;> assumption)
end
end
end
end
