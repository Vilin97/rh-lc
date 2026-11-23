module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodVOfGoodL
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointApplyOfEigen

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.SplitEigen

theorem adjoint_apply_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : Module.End ℂ H) (hA : Commute A (LinearMap.adjoint A)) (v : H) (μ : ℂ) (hv : A v = μ • v) :
    LinearMap.adjoint A v = starRingEnd ℂ μ • v := by
  set B : Module.End ℂ H := A - μ • 1 with hBdef
  have hBadj : LinearMap.adjoint B = LinearMap.adjoint A - starRingEnd ℂ μ • 1 := by
    rw [hBdef, map_sub, map_smulₛₗ]
    congr 2
    exact LinearMap.adjoint_id
  have hBv : B v = 0 := by
    rw [hBdef, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv, sub_self]
  have hc : Commute B (LinearMap.adjoint B) := by
    rw [hBadj, hBdef]
    exact (hA.sub_right ((Commute.one_right A).smul_right _)).sub_left ((Commute.one_left _).smul_left _)
  have h0 : LinearMap.adjoint B v = 0 := by
    have e : inner ℂ (LinearMap.adjoint B v) (LinearMap.adjoint B v) = (0 : ℂ) := by
      rw [LinearMap.adjoint_inner_left]
      have : B (LinearMap.adjoint B v) = LinearMap.adjoint B (B v) := by
        rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      rw [this, hBv, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 e
  rw [hBadj, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h0
  exact h0

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)) (X : Set M)
    (hS : ∀ b ∈ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u) : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem b hb => exact hS b hb
  | algebraMap r => exact ⟨r, fun u _ => Module.algebraMap_end_apply ℂ ℂ M r u⟩
  | add b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ + μ', fun u hu => by rw [LinearMap.add_apply, hμ u hu, hμ' u hu, add_smul]⟩
  | mul b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ * μ', fun u hu => by rw [Module.End.mul_apply, hμ' u hu, map_smul, hμ u hu, smul_smul, mul_comm]⟩

end GlobalTheory.SplitEigen

namespace GlobalTheory.SplitEigen



theorem label_scalar_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hEx _hH _hGE j c h hh hN P hP hconj d _hd
  obtain ⟨hCoreF, -, -, hOnto, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have hCore := hCoreF hEx
  have hM := hCore.models
  obtain ⟨P0, hP0, rfl⟩ := (hOnto _ hP).2 hconj
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hCore.lev hCore.fam hM).2 j A3.A.fam.μ0 h hh ⟨P0, hP0⟩
  have hK := RealDat3.kFormL_of (R := R) (F := F) hM

  have hop : ∀ k, k ≤ (Vc D j).rank → (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inl (⟨P0, hP0⟩, k))) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) := by
    intro k hk
    refine LinearMap.ext_on_range (hK j A3.A.fam.μ0).2 fun b => ?_
    rw [← CxData.jL_opL _ hK]
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (hsplit k hk _)

  have hT : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))) • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have e1 := (U2.mem_eigPart.1 hx) (Sum.inl (⟨P0, hP0⟩, k))
    have e2 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (U2.liftHeckeOperators A3 (R.toCx3 F) j (Sum.inl (⟨P0, hP0⟩, k)) x) =
        h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H)) (LinearMap.congr_fun (hop k hk) x)).trans rfl
    rw [← e2, e1]
    exact Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H) _ _

  have hD : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))) •
          (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have ha : LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) =
        h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) := by
      rw [hN.2 _ hP]
      congr 1
      rw [Finsupp.mapRange_single, star_one, GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single]
    have hc : Commute (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))
        (LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))) :=
      ha.symm ▸ hN.1 _ _ hP hP _ _
    exact (LinearMap.congr_fun ha _).symm.trans (adjoint_apply_of_eigen _ hc _ _ (hT k hk x hx))

  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Vc D j) (R.pl P0) hconj _
    (GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W) d
  have key := adjoin_scalar _ {u | ∃ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      u = (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)} (by
    rintro b ⟨k, hk, rfl | rfl⟩
    · refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hT k hk x hx)).trans (map_smul _ _ _)))
    · refine ⟨starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hD k hk x hx)).trans (map_smul _ _ _)))) a ha
  obtain ⟨μ, hμ⟩ := key
  refine ⟨μ, fun x hx => (hM.HV j A3.A.fam.μ0).1 ?_⟩
  have hfix : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) (R.pl P0), GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W k
      ((R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)) =
        (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
    obtain ⟨n, hn⟩ := hCore.lev.βV j
    have hn' : IsBaseFrame (Vc D j) (R.βV j) (R.ΛV j) 1 := (one_pow n : (1 : ℕ) ^ n = 1) ▸ hn
    refine GlobalTheory.DefiniteOps.fixed_of_mem (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j A3.A.fam.μ0) hn' (R.pl P0) hP (R.cV j).coef.ρ _ ?_
    have hm := LinearMap.mem_range_self (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)
    rw [(hM.HV j A3.A.fam.μ0).2.1] at hm
    exact hm
  exact (hh _ hP _ _).trans ((GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).trans ((hae _ hfix).symm.trans
    ((hμ _ ⟨x, hx, rfl⟩).trans (map_smul _ _ _).symm)))

end GlobalTheory.SplitEigen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIdealEqOfConjPl

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.InertEigScalar

theorem conjIdeal_eq_of_conjPl {D : D7} (P : Pl D.host.E) (hc : conjPl P = P) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal := by
  have h1 : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) := by
    unfold Formalism.HermitianLatticesTheory.conjIdeal
    show _ = Ideal.span _
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, hr⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.ext
      change _ = (algebraMap (𝓞 D.host.E) D.host.E r)
      rw [hr]
      rfl
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  rw [h1]
  exact congrArg HeightOneSpectrum.asIdeal hc



theorem inert_label_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P = P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC _hEx _hH _hPG j c h hh _hN P hP hc d hd
  have hlab := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) P d).1 hd
  obtain ⟨s', hs2, hsp, hspos, rfl⟩ :=
    (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank d).1 ⟨hlab.1, hlab.2.1, hlab.2.2 hc⟩
  have hPg : P ∉ R.Pg := fun hm => (hP P (Or.inl hm)).1 rfl
  have hPQ : P ∉ R.Q A3.A.fam.μ0 := fun hm => (hP P (Or.inr hm)).1 rfl
  have hfix := conjIdeal_eq_of_conjPl P hc
  have hSb : P ∉ R.Sb := by
    have e : R.Sb = R.Pg := hC.allPl
    rw [e]; exact hPg
  have hoff : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := ⟨hfix, fun hm => hSb (Finset.mem_coe.1 hm)⟩
  have honto : R.in_onto := hC.inert.onto
  have hex : ∃ Q, R.plI Q = P := honto P hoff
  obtain ⟨Q, hQ⟩ := hex
  have hQok : Q ∈ A3.okI A3.A.fam.μ0 := by
    refine (hC.inert.tie.okI A3.A.fam.μ0 Q).2 ⟨?_, ?_⟩
    · rw [hQ]; exact hfix
    · rw [hQ, hC.allPl]
      simp only [Set.mem_union, Finset.mem_coe]
      tauto
  subst hQ
  have hLt : R.in_L := hC.inert.hL
  have hn := hLt j A3.A.fam.μ0
  obtain ⟨Comparison₂⟩ := hn
  let inR' : ↥(A3.okI A3.A.fam.μ0) × List ℕ → Prop :=
    fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2 ∧ R.plI k.1 = R.plI Q
  let Tie' : Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j A3.A.fam.μ0).pres (A3.heckeLI j A3.A.fam.μ0) inR'
      (fun k => GlobalTheory.Hk3.IsLabElt (Vc D j) (R.plI k.1) (GlobalTheory.Hk3.labIn (Vc D j).rank k.2))
      (fun k => GlobalTheory.Hk3.IsLocElt (Vc D j) (R.plI k.1)) :=
    { hx := Comparison₂.hx, hA := Comparison₂.hA, hx_ok := fun i hi => Comparison₂.hx_ok i hi.1, hA_loc := fun i hi => Comparison₂.hA_loc i hi.1,
      chi_loc := fun i hi => Comparison₂.chi_loc i hi.1, hDC := fun i hi => Comparison₂.hDC i hi.1, op_eq := fun i hi => Comparison₂.op_eq i hi.1 }
  let k : ↥(A3.okI A3.A.fam.μ0) × List ℕ := (⟨Q, hQok⟩, s')
  have hk : inR' k := ⟨⟨hsp, hspos, hs2⟩, rfl⟩
  have hin : ∀ i, inR' i → GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
      (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    rintro ⟨Q', t'⟩ ⟨hty, hpl⟩
    simp only at hpl ⊢
    rw [hpl]
    exact ⟨hP, hc, ((GlobalTheory.Hk3.labIn_selfDual_iff _ _).2 ⟨t', hty.2.2, hty.1, hty.2.1, rfl⟩).2.1⟩
  have key := (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models j
    A3.A.fam.μ0 _ (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.fam.μ0) inR'
    hin Tie' k hk).2.2.2 h hh
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hC.base.models
  have hop : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s') 1)) := by
    apply LinearMap.ext_on_range (hK j A3.A.fam.μ0).2
    intro b
    rw [← Formalism.IndefR.Cx.CxData.jL_opL (R.toCx3 F) hK]
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j A3.A.fam.μ0 (A3.heckeLI j A3.A.fam.μ0 k _)) =
      Tw.mk (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) _ (R.jV j A3.A.fam.μ0 _))
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (key _)
  refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inr k)), fun x hx => ?_⟩
  have hx' : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) x = c (Sum.inr k) • x :=
    (Formalism.IndefR.U2.mem_eigPart.1 hx) (Sum.inr k)
  rw [hop] at hx'
  exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0)) hx'

end GlobalTheory.InertEigScalar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftInjectiveGoodPartJointEigenspace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows



namespace GlobalTheory.InjEigen

theorem label_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ), ∃ h, GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h ∧ ∃ e : Eig D, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → GlobalTheory.Hk3.IsLab (Vc D j) P d → h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = e P d • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hOk hpg j c
  obtain ⟨h, hops, hnf⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hch.base.lev hch.base.fam hch.base.models).2 j A3.A.fam.μ0
  have key : ∀ P d, ∃ a : ℂ, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P →
      GlobalTheory.Hk3.IsLab (Vc D j) P d → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
        h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
          a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro P d
    by_cases hg : GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P
    · by_cases hl : GlobalTheory.Hk3.IsLab (Vc D j) P d
      · first
          | exact (Classical.em (Formalism.L2.DIV.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
          | exact (Classical.em (Formalism.DivisionValues.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
      · exact ⟨0, fun _ hl' => absurd hl' hl⟩
    · exact ⟨0, fun hg' => absurd hg' hg⟩
  choose e he using key
  exact ⟨h, hops, e, fun x hx P d hg hl => he P d hg hl x hx⟩

theorem inj_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hinj hOk hpg j c x y hx hθx hy hθy
  obtain ⟨h, hops, e, he⟩ := label_eigensystem R F hok hch hex hOk hpg j c
  have hy' := Submodule.mem_inf.mp hy
  have hgood := GlobalTheory.goodV_of_goodL R F hok hch hex hOk hpg j y hy'.2
  clear hok hch hex hOk hpg hy
  have hθ : ∀ z : (R.toCx3 F).FLC j A3.A.fam.μ0, (R.toCx3 F).θ' j A3.A.fam.μ0 z =
      R.phs j • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) z := fun z => rfl
  have hp : R.phs j ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ, h0]
    exact zero_smul ℂ _
  have hcj : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    apply hp
    rw [← Formalism.IndefR.Links.cj_cj (twAt D.what₂.embLL A3.A.v0) (R.phs j), h0, map_zero]
  have hx0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ]
    have h1 : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) x = 0 := h0
    rw [h1]
    first
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j _).H) (R.phs j)
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) _) (R.phs j)
      | (simp only [smul_zero]; rfl)
  have hy0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := by
    have h2 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := hθy
    exact (smul_eq_zero.mp h2).resolve_left hcj
  exact hinj j h hops e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) (fun P d hg hl => he x hx P d hg hl)
    (fun P d hg hl => he y hy'.1 P d hg hl) hx0 hgood hy0

end GlobalTheory.InjEigen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftInjectiveGoodPartJointEigenspaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.thetaLift_injective_goodPart_jointEigenspace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  first | exact @GlobalTheory.InjEigen.inj_eig | exact GlobalTheory.InjEigen.inj_eig | (intros; apply GlobalTheory.InjEigen.inj_eig <;> assumption)
end
end
