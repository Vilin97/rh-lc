module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedA
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntegralThetaLiftDefiniteFormNeZeroStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComponentParametersContainStringStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftFockVectorsSphericalPrincipalFixedStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsPlacesSingleton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnderEqOfConj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedAStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.linearForm_extV_mem_A0_and_prin_invariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  first | exact @GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed | exact GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed | (intros; apply GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeStringGivesSimplePoleHypotheses

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.StringPole

theorem good_of_not_mem_above {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F)))) :
    GlobalTheory.Hk3.Good R t w := by
  intro PP hPP
  have hmem : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl
    exact Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hw hmem
  · intro hc
    have e := GlobalTheory.GoodPrimes.isConjPl_iff.1 hc
    apply hw
    show w.under (𝓞 D.host.F) ∈ (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F)))
    rw [e, GlobalTheory.TwistTypePlaces.under_conjPl]
    exact hmem

end GlobalTheory.Core.Rk.StringPole


open GlobalTheory.Core.Rk.StringPole in
theorem GlobalTheory.Core.Rk.StringPole.string_pole_hyp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t s, HasString R i t s → ∃ B c : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧ GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))) D.R.r D.R.t c B (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i t s hs
  classical
  obtain ⟨B, hB, hstr⟩ := hs
  set x := GlobalTheory.LFun.val (F := D.host.F) (chiV R i t) with hx
  let c : GlobalTheory.LFun.Fam D.host.E := fun w => B w - GlobalTheory.LFun.segFam x D.R.t w
  refine ⟨B, c, hB, (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t).finite_toSet, D.R.rank_add_five_le, fun w hw => ?_⟩
  have hg := good_of_not_mem_above R t w hw
  obtain ⟨B', hB', hbd⟩ := hstr w hg
  have hcard : (B w).card = (Vc D i).rank := by
    rcases hB (w.under (𝓞 D.host.F)) (fun h => hw h) w rfl with ⟨_, h2, _⟩ | ⟨_, τ, ϖ, α, _, _, h3, _⟩
    · exact h2
    · rw [h3]
      simp [GlobalTheory.LGrp.bcParam]
      omega
  have hrank : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hseg : (GlobalTheory.LFun.segFam x D.R.t w).map (fun a : ℂˣ => (a : ℂ)) =
      str (Ideal.absNorm w.asIdeal) (valV R i t w : ℂ) D.R.t := by
    unfold GlobalTheory.LFun.segFam GlobalTheory.LFun.seg str
    rw [Multiset.map_map]
    rfl
  have hle : GlobalTheory.LFun.segFam x D.R.t w ≤ B w := by
    refine (Multiset.map_le_map_iff (f := fun a : ℂˣ => (a : ℂ)) Units.val_injective).1 ?_
    rw [hB', hseg]
    exact Multiset.le_add_left _ _
  have hsplit : B w = c w + GlobalTheory.LFun.segFam x D.R.t w := (tsub_add_cancel_of_le hle).symm
  have hc' : (c w).map (fun a : ℂˣ => (a : ℂ)) = B' := by
    have := congrArg (Multiset.map fun a : ℂˣ => (a : ℂ)) hsplit
    rw [Multiset.map_add (f := _), hB', hseg] at this
    exact (add_right_cancel this).symm
  refine ⟨?_, ?_, GlobalTheory.LFun.norm_val _ _, GlobalTheory.LFun.norm_val _ _, ?_⟩
  · have := congrArg Multiset.card hsplit
    rw [Multiset.card_add, hcard, hrank] at this
    simp only [GlobalTheory.LFun.segFam, GlobalTheory.LFun.card_seg] at this
    omega
  · intro b hb
    have hb' : (b : ℂ) ∈ B' := hc' ▸ Multiset.mem_map_of_mem _ hb
    exact hbd _ hb'
  · show B w = GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam c x x D.R.t w
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam
    rw [mul_inv_cancel, GlobalTheory.LFun.twist_one]
    exact hsplit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeStringGivesSimplePoleHypothesesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.satake_string_gives_simple_pole_hypotheses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t s, HasString R i t s → ∃ B c : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧ GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))) D.R.r D.R.t c B (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
  first | exact @GlobalTheory.Core.Rk.StringPole.string_pole_hyp | exact GlobalTheory.Core.Rk.StringPole.string_pole_hyp | (intros; apply GlobalTheory.Core.Rk.StringPole.string_pole_hyp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairDefinitePlaceCharacterData

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.DownPair

theorem pair_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∃ cA a, Defin R.θ (Vc D i) cA a) ∧ Places (Vc D i) (R.βV i) (R.Pg ∪ R.Q t) ∧ under (R.Pg ∪ R.Q t) = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t ∧ GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) ∧ (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) ∧ (Wc D i).SigOK ∧ (Wc D i).rank = D.R.r ∧ 0 < D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t ∧ D.R.r + 5 ≤ D.R.t ∧ R.ΛV i = GlobalTheory.AdelicU.frameLat (Vc D i) ∧ R.ΛW i = GlobalTheory.AdelicU.frameLat (Wc D i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t
  have hc := hG.core
  have hV := hc.lev.βV i
  have hW := hc.lev.βW i
  have hΛ : ∀ {V : Formalism.BasicNotions.HSpace D.host.E} {β Λ}, Formalism.IndefR.Links.IsSDFrame (D := D) V β Λ 1 → Λ = GlobalTheory.AdelicU.frameLat V := by
    intro V β Λ h
    obtain ⟨c, hf, -, -, h1, h2⟩ := h
    ext x
    rw [GlobalTheory.AdelicU.mem_frameLat]
    constructor
    · intro hx; have := h2 x hx; simp only [one_pow, Nat.cast_one, one_smul] at this; exact this
    · intro hx; simpa using h1 x hx
  have hΛV := hΛ hV
  have hΛW := hΛ hW
  have hEta : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η := by
    have hω := hc.thP.ωP i t
    refine ⟨R.eta, GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D R.eta R.C.eta hc.lev.eta R.C.isEta _ (Vc D i).rank (Wc D i).rank hω.resS hω.resT ?_⟩
    · rw [D.sp.V_rank _ (by omega) (by omega), D.sp.W_rank _ (by omega) (by omega)]
      unfold Formalism.BasicNotions.Ranks.nV
      have := D.R.t_odd
      obtain ⟨k, hk⟩ := this
      exact ⟨D.R.r + k, by omega⟩
  have hUnr : GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) := by
    intro w hw
    have hgood : GlobalTheory.Hk3.Good R t w := by
      intro PP hPP
      constructor
      · rintro rfl
        exact hw (Finset.mem_coe.2 (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, rfl⟩))
      · intro hcj
        exact hw (Finset.mem_coe.2 (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, GlobalTheory.RawLift.Small.under_eq_of_conj hcj⟩))
    have hg := ((GlobalTheory.GoodPrimes.good_primes R F hc.lev).2.1 t w hgood).1
    have hnotover : ∀ k, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) w := by
      intro k hk
      apply hg
      push_cast
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk
      · exact Ideal.mul_mem_left _ _ hk
    have hmu : (R.C.mu0 i).UnrAt w := (R.C.isMu0 i).unr w hnotover
    have hxi : (R.xiH t).UnrAt w := by
      by_contra h
      rcases (hc.lev.Q_ram t w).1 h with h1 | ⟨PP', h1, h2⟩
      · exact (hgood w (Or.inr h1)).1 rfl
      · exact (hgood PP' (Or.inr h1)).2 h2
    have heta : R.C.eta.UnrAt w := R.C.isEta.unr w
    have a1 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hc.lev.mu0 i) w).2 hmu
    have a2 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hc.lev.xi t) w).2 hxi
    have a3 := (GlobalTheory.LFun.unrAt_iff_of_chrEq hc.lev.eta w).2 heta
    exact (a1.mul a2).mul a3.inv
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  refine ⟨GlobalTheory.Core.Rk.Exh.Model.exists_defin hc.models.inf (D.sp.V_sig _) (hc.models.vpos i), ⟨?_, ?_, fun v h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2⟩, rfl, hUnr, hEta, D.sp.W_sig _, D.sp.W_rank _ (by omega) (by omega), hr, ?_, D.R.rank_add_five_le, hΛV, hΛW⟩
  · obtain ⟨c, hf, -⟩ := hV
    rw [← hΛV]; exact hf
  · obtain ⟨-, e, he, -⟩ := hc.thP.vP i t
    exact ⟨e, he⟩
  · rw [D.sp.V_rank _ (by omega) (by omega)]
    unfold Formalism.BasicNotions.Ranks.nV
    rfl

end GlobalTheory.DownPair
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairDefinitePlaceCharacterDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.thetaLiftPair_definite_place_character_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∃ cA a, Defin R.θ (Vc D i) cA a) ∧ Places (Vc D i) (R.βV i) (R.Pg ∪ R.Q t) ∧ under (R.Pg ∪ R.Q t) = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t ∧ GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) ∧ (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) ∧ (Wc D i).SigOK ∧ (Wc D i).rank = D.R.r ∧ 0 < D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t ∧ D.R.r + 5 ≤ D.R.t ∧ R.ΛV i = GlobalTheory.AdelicU.frameLat (Vc D i) ∧ R.ΛW i = GlobalTheory.AdelicU.frameLat (Wc D i) := by
  exact @GlobalTheory.DownPair.pair_data
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.NonVanAt

theorem up_eq_setIntegral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {χA χW : (AE D)ˣ →* Circle}
    {om : GlobalTheory.Core.Rk.IP.WRep A W} (hW : IsWeilDatumO ψ A W χA χW om) {m : Measure (GA D A)} {X : Set (GA D A)}
    (hm : m.IsHaarMeasure) (hX : IsFundamentalDomain (GQ A) X m) {f : WO A W → ℂ} (hf : IsThetaFunO ψ A W f)
    {u : GA D A → ℂ} (hu : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) u) (h : GA D W) :
    GlobalTheory.Core.Rk.IP.up om m f u h = ∫ g in X, thetaKO om g h f * u g ∂m := by
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) (fun g => thetaKO om g h f * u g) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D A × GA D W) = (γ, 1) * (g, h) := by simp
    have h1 : thetaKO om (γ * g) h f = thetaKO om g h f := by
      unfold thetaKO
      rw [e, map_mul, Module.End.mul_apply]
      exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hf)
    show thetaKO om (γ * g) h f * u (γ * g) = thetaKO om g h f * u g
    rw [h1, hu γ hγ g]
  rw [GlobalTheory.Core.Rk.IP.up, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]

theorem rcoef_zero {D : D7} {A : HSp D} (m : Measure (GA D A)) (b : GA D A) : GlobalTheory.Core.Rk.IP.rcoef m 0 0 b = 0 := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]



theorem nonVan_of_downNe : ∀ (D : D7) (_ : DownNe D) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  intro D hD G _ _ Pl0 T A Ks _ _ _ R F hG hP i t h hh s hs y hy hy0
  obtain ⟨⟨cA, a, hdef⟩, hpl, hun, hunr, hη, hsig, hrW, hr0, hrV, -, -, -⟩ := GlobalTheory.T.thetaLiftPair_definite_place_character_data D G Pl0 T A Ks R F hG hP i t
  obtain ⟨hlev, hX⟩ := hG.core.models.νV i t
  have hm : (R.νV i t).IsHaarMeasure := hlev.1
  have hW := hG.core.thP.ωP i t
  obtain ⟨l, P, hreal⟩ := GlobalTheory.T.realIntegral_thetaLift_definiteForm_ne_zero D G Pl0 T A Ks R F hG hP i t y hy0 (R.νV i t) hm
  obtain ⟨hA0, hfix⟩ := GlobalTheory.T.linearForm_extV_mem_A0_and_prin_invariant D G Pl0 T A Ks R F hG hP i t cA a hdef y l
  obtain ⟨B, c, hB, hHyp⟩ := GlobalTheory.T.satake_string_gives_simple_pole_hypotheses D G Pl0 T A Ks R F hG hP i t s hs
  obtain ⟨hcart, hfock, hsph, hfixΦ⟩ := GlobalTheory.T.thetaLiftFockVectors_spherical_principalFixed D G Pl0 T A Ks R F hG hP i t P
  have hu0 : (fun g => l (R.extV i t y g)) ≠ 0 := by
    intro h0
    obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
    obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D (Vc D i)
    have : LocallyCompactSpace (GinfC (Vc D i)) := i6.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : BorelSpace (GinfC (Vc D i)) := Subtype.borelSpace _
    refine hreal ν 𝓕 hν Measure.haar inferInstance ?_
    rw [h0]
    simp only [rcoef_zero, mul_zero, integral_zero]
  have hpar := GlobalTheory.T.scalarComponent_parameters_contain_string D G Pl0 T A Ks R F hG hP i t h hh s y hy l hu0 B hB
  have hpar' : GlobalTheory.LFun.IsParamFunV (Vc D i) (under (R.Pg ∪ R.Q t)) (fun g => l (R.extV i t y g)) B :=
    hun.symm ▸ hpar
  have hHyp' : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under (D := D) (R.Pg ∪ R.Q t) : Set (HeightOneSpectrum (𝓞 D.host.F))) (Wc D i).rank D.R.t c B
      (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
    rw [hrW, hun]; exact hHyp
  have hF : Form R.θ (Vc D i) cA (R.βV i) (R.Pg ∪ R.Q t) (chiV R i t) (Wc D i).rank D.R.t (fun g => l (R.extV i t y g)) B := by
    refine ⟨hA0, hfix, ?_, hunr, c, ?_⟩
    · exact hpar'
    · exact hHyp'
  have hO : Occ R.ψ R.θ (cart (R.MW i (sg0 D A))) (R.ωP i t) (R.νV i t) (R.βV i) (R.Pg ∪ R.Q t)
      (fun g => l (R.extV i t y g)) (R.ptP i t P) := ⟨hcart, hfock, hsph, hfixΦ, hreal⟩
  have hW' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (chiW R i t) (chiV R i t) (R.ωP i t) := hW
  have hr1 : 0 < (Wc D i).rank := by rw [hrW]; exact hr0
  have hr2 : (Vc D i).rank = (Wc D i).rank + D.R.t := by rw [hrW]; exact hrV
  have key := hD R.ψ R.θ (Vc D i) (Wc D i) D.R.t (chiW R i t) (chiV R i t) (R.ωP i t) cA a (R.βV i) (R.Pg ∪ R.Q t)
    (R.νV i t) (fun g => l (R.extV i t y g)) B (cart (R.MW i (sg0 D A))) (R.ptP i t P) hdef hsig hr1 hr2 hη hW' hpl hm hF hO
  by_contra hno
  refine key fun f hf g => ?_
  rw [up_eq_setIntegral hW hm hX hf (GlobalTheory.AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hA0).1.1.toIsAutFun)]
  by_contra hne
  exact hno ⟨f, l, g, hf, hne⟩

end GlobalTheory.Core.Rk.NonVanAt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDownStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.thetaLift_nonvanishing_onString_of_definiteDown : ∀ (D : D7) (_ : DownNe D) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  first | exact @GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe | exact GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe | (intros; apply GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe <;> assumption)
end
end
