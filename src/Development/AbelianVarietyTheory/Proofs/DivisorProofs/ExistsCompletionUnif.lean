module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitary
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPosDefFiniteProjectiveLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfTorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismCharacterActionConjugate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivMapOfTorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTrait
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictSurjectiveAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadOfTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOverModuli
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsGrpPullbackOfEqId

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.SelfCmp

theorem isGrpPullback_of_eq_id {S : Scheme.{0}} (G : Over S) [GrpObj G] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback G G f (𝟙 G.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.LN.SelfCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfIsGrpPullbackFst

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isMonHom_of_isGrpPullback_fst {S S' : Scheme.{0}} {s : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (bc : G' ≅ (Over.pullback s).obj G) (h : IsGrpPullback G' G s (bc.hom.left ≫ pullback.fst G.hom s)) :
    IsMonHom bc.hom := by
  obtain ⟨e, me, he⟩ := grpPullback_iso h (isGrpPullback_pullback G s)
  have : e.hom = bc.hom := Over.OverMorphism.ext (pullback.hom_ext he ((Over.w e.hom).trans (Over.w bc.hom).symm))
  exact this ▸ me

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeEquivCompletedLocalRing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory.UPoinc.TraitCompare

theorem exists_trait_lattice_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ (x : Y.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : Y.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsSemiAbelian G → IsGrpPullback G out.G (spMap j ≫ Y.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ ρT : D.toPre.X ≃+ T.P.D.toPre.X, (∀ y s, PsiCoord D.toPre y s → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (ψ s ^ 2) (T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r _hOver _hpt f _hf habl hT x R _ _ _ j hR _hj G _ _ gm hG hgm D A U hLB
    hPsi m hm T ψ hψ hTy
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : CharZero T.V := T.cdvr.2.2
  have hTV : GlobalTheory.Mum.Base T.V := ⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR T.cdvr, inferInstance⟩
  have hξT : spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x = spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x) := by
    rw [spMap_comp, Category.assoc]
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := by
    simp [spMap]
  obtain ⟨tW, mW, PW, e, he⟩ := GlobalTheory.UPoinc.TraitPull.exists_pull_unif E H Dw l Xo c T T.V hTV inferInstance (RingHom.id T.V)
    (fun _ _ h => h) inferInstance
  obtain ⟨βT, hβT, hLT, hactT⟩ := hT T _ hTy
  have hβ' : IsGrpPullback tW.G out.G (spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x)) (mW.φ ≫ βT) :=
    (mW.cart.comp hβT).congr (by rw [hid, Category.id_comp, hξT]) rfl
  have w : (mW.φ ≫ βT) ≫ out.G.hom = (tW.G.hom ≫ spMap ψ) ≫ (spMap j ≫ Y.Z.fromSpecStalk x) := by
    rw [hβ'.1.w, Category.assoc]
  let β : tW.G.left ⟶ G.left := hgm.1.lift (mW.φ ≫ βT) (tW.G.hom ≫ spMap ψ) w
  have hβgm : β ≫ gm = mW.φ ≫ βT := hgm.1.lift_fst _ _ _
  have hβG : β ≫ G.hom = tW.G.hom ≫ spMap ψ := hgm.1.lift_snd _ _ _
  have hβ : IsGrpPullback tW.G G (spMap ψ) β := hgm.cancel (by rw [hβgm]; exact hβ') hβG
  have hLBW : LBIso PW.U.LG.L (U.LG.L.pull β) := by
    rw [PW.bundle]
    exact LBIso.trans tW.PP.isLB (LB.isLB_pull out.L.isLB _) (LB.isLB_pull U.LG.isLB _)
      (LBIso.trans tW.PP.isLB (LB.isLB_pull T.t.PP.isLB _) (LB.isLB_pull out.L.isLB _)
        (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mW) (GlobalTheory.LN.GenericPoint.lbIso_pull hLT mW.φ rfl))
      (GlobalTheory.LN.GenericPoint.lbIso_pull hLB β hβgm.symm).symm

  have hab : ∀ z, (spMap j ≫ Y.Z.fromSpecStalk x) z ∈ abLocus out.G ↔ z ∈ abLocus G :=
    abLocus_pullback abLocusOne out.semi hgm.1
  have hTy' : jK T.V ≫ (spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x)) ≫ r = T.y ≫ C.i := by
    rw [← hξT]; exact hTy
  have hgen : spMap ψ (genericPoint (Sp T.V)) ∈
      (⟨abLocus G, GlobalTheory.AbLocusOpen.isOpen_abLocus_local G hG⟩ : (Sp R).Opens) := by
    show _ ∈ abLocus G
    rw [← hab]
    apply habl
    let pt : Sp (FractionRing T.V) := ⟨⊥, Ideal.isPrime_bot⟩
    have hpt : jK T.V pt = genericPoint (Sp T.V) := by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext (Ideal.ext fun s => ?_)
      change algebraMap T.V (FractionRing T.V) s ∈ (⊥ : Ideal (FractionRing T.V)) ↔ s ∈ (⊥ : Ideal T.V)
      rw [Ideal.mem_bot, Ideal.mem_bot, IsFractionRing.to_map_eq_zero_iff]
    rw [← hpt]
    exact ⟨T.y pt, (congrArg (fun g : Sp (FractionRing T.V) ⟶ C.Z => g pt) hTy').symm⟩

  have hPsi' : ∀ y, PsiUnitOn D.toPre y (⟨abLocus G, GlobalTheory.AbLocusOpen.isOpen_abLocus_local G hG⟩ : (Sp R).Opens) := by
    intro y
    have hs : (⇑(spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G) = abLocus G := Set.ext hab
    have := hPsi y
    rw [hs] at this
    exact this

  let bc : tW.G ≅ (Over.pullback (specOf ψ)).obj G :=
    Over.isoMk hβ.1.isoPullback (by simp)
  have hbcβ : β = bc.hom.left ≫ pullback.fst G.hom (specOf ψ) := by
    simp [bc]
  have hbc : IsMonHom bc.hom := GlobalTheory.Mum.isMonHom_of_isGrpPullback_fst bc (hβ.congr rfl hbcβ)
  obtain ⟨D₂, A₂, hD, U₂, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U T.V hTV.1 ψ hψ _ hPsi' hgen tW.G bc hbc
  obtain ⟨hL₁, hC₁, hE₁⟩ := PullUnif.main R hR G hG D A U T.V hTV tW.G tW.semi D₂ A₂ U₂ ψ β hψ bc hbc hbcβ hD hU

  have hid' : IsGrpPullback tW.G tW.G (spMap (RingHom.id T.V)) (𝟙 tW.G.left) :=
    GlobalTheory.LN.SelfCmp.isGrpPullback_of_eq_id tW.G hid
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SpreadTrait.exists_spread T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A PW.U
    (RingHom.id T.V) (𝟙 _) hid'
  have hρs := GlobalTheory.TorusOntoSpread.restrict_surjective T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id T.V) (𝟙 _) hid' ρ hρ
  have hρT := GlobalTheory.SpreadTorMatch.torMatch_of_spread T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id T.V) (𝟙 _) hid' ρ hρ
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.SpreadTrait.exists_spread T.V hTV tW.G tW.semi PW.D PW.A PW.U T.V hTV tW.G tW.semi D₂ A₂ U₂
    (RingHom.id T.V) (𝟙 _) hid'
  have hρ's := GlobalTheory.TorusOntoSpread.restrict_surjective T.V hTV tW.G tW.semi PW.D PW.A PW.U T.V hTV tW.G tW.semi D₂ A₂
    U₂ (RingHom.id T.V) (𝟙 _) hid' ρ' hρ'
  have hL₂ : LBIso PW.U.LG.L (U₂.LG.L.pull (𝟙 _)) :=
    LBIso.trans PW.U.LG.isLB (LB.isLB_pull U.LG.isLB _) (LB.isLB_pull U₂.LG.isLB _) hLBW
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL₁ (𝟙 _) (Category.id_comp β).symm).symm
  have hC₂ := TorCoord.coordMap_of_torMatch T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV inferInstance tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id _) (𝟙 _) (fun _ _ h => h) hid' hL₂ ρ hρT
  have hE₂ := equivMap_of_torMatch T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A PW.U (RingHom.id _)
    (𝟙 _) (fun _ _ h => h) ρ hρT
  obtain ⟨-, -, -, -, n, ⟨eZ⟩⟩ := GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice E H Dw l Xo c T
  haveI : Module.Finite ℤ T.P.D.toPre.X := Module.Finite.equiv eZ.symm
  haveI : Module.Finite ℤ PW.D.toPre.X := Module.Finite.equiv e.toAddEquiv.toIntLinearEquiv.symm
  have hρ'i : Function.Injective ρ' := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (ρ.comp ρ').toIntLinearMap (hρs.comp hρ's)
    exact Function.Injective.of_comp (f := ⇑ρ) (g := ⇑ρ') h
  haveI : Module.Finite ℤ D₂.toPre.X := Module.Finite.of_surjective ρ'.toIntLinearMap hρ's
  have hρi : Function.Injective ρ := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (ρ'.comp ρ).toIntLinearMap (hρ's.comp hρs)
    exact Function.Injective.of_comp (f := ⇑ρ') (g := ⇑ρ) h
  let ρE : D₂.toPre.X ≃+ PW.D.toPre.X := AddEquiv.ofBijective ρ ⟨hρi, hρs⟩
  refine ⟨(hD.xe.symm.trans ρE).trans e.toAddEquiv, ?_, ?_⟩
  · intro y s hs
    obtain ⟨r₂, hr₂⟩ := GlobalTheory.BetaAdd.exists_coord D₂ (hD.xe.symm y)
    obtain ⟨h0, r', hr', hass⟩ := he (ρ (hD.xe.symm y))
    refine ⟨h0, ?_⟩
    have h1 : Associated (ψ s) r' := (hC₁ y s r₂ hs hr₂).trans (hC₂ _ r₂ r' hr₂ hr' : Associated r₂ r')
    exact (h1.pow_pow (n := 2)).trans hass
  · intro a y
    obtain ⟨fR, hfRmon, hfRgm, hfRchar⟩ := hm a
    have hcompat : (tW.act.act a).left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc ((tW.act.act a).left ≫ β) ≫ gm = (tW.act.act a).left ≫ mW.φ ≫ βT := by rw [Category.assoc, hβgm]
          _ = mW.φ ≫ (T.t.act.act a).left ≫ βT := by rw [← Category.assoc, mW.act a, Category.assoc]
          _ = mW.φ ≫ βT ≫ (f a).left := by rw [hactT a]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, hfRgm, reassoc_of% hβgm]
      · rw [Category.assoc, hβG, Category.assoc, Over.w fR, hβG, ← Category.assoc, Over.w (tW.act.act a)]
    obtain ⟨m₂, hm₂⟩ := endChar_exists_of_isMonHom T.V hTV tW.G tW.semi D₂ A₂ U₂ (tW.act.act a) (tW.act.hom a)
    have h1 := hE₁ fR (tW.act.act a) hfRmon (tW.act.hom a) hcompat (m a) m₂ hfRchar hm₂ y
    have h2 := hE₂ (tW.act.act a) (tW.act.act a) (tW.act.hom a) (tW.act.hom a) (by simp) m₂ _ hm₂
      (GlobalTheory.UPoinc.endChar_act E H T.V hTV tW PW a) (hD.xe.symm y)
    show e (ρ (hD.xe.symm (m a y))) = H.bar a • e (ρ (hD.xe.symm y))
    have h1' : hD.xe.symm (m a y) = m₂ (hD.xe.symm y) := h1
    rw [h1', h2]
    exact e.map_smul _ _

end GlobalTheory.UPoinc.TraitCompare
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeEquivCompletedLocalRingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_traitLattice_equiv_completedLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ (x : Y.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : Y.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsSemiAbelian G → IsGrpPullback G out.G (spMap j ≫ Y.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ ρT : D.toPre.X ≃+ T.P.D.toPre.X, (∀ y s, PsiCoord D.toPre y s → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (ψ s ^ 2) (T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  first | exact @GlobalTheory.UPoinc.TraitCompare.exists_trait_lattice_equiv | exact GlobalTheory.UPoinc.TraitCompare.exists_trait_lattice_equiv | (intros; apply GlobalTheory.UPoinc.TraitCompare.exists_trait_lattice_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOverModuliStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.integerAction_semiAbelian_along_traits_over_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  first | exact @GlobalTheory.UPoinc.oAct_along_traits_of_over | exact GlobalTheory.UPoinc.oAct_along_traits_of_over | (intros; apply GlobalTheory.UPoinc.oAct_along_traits_of_over <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompletionUnif

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GPeriods

theorem exists_completion_unif {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)
    (hO : S.Over₀ M U₀) (x : M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R)
      (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R))
      (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsSemiAbelian G ∧
      IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧
      ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _, IsSemiAbelian.pullback ξ FinalForm.G FinalForm.semi,
    isGrpPullback_pullback _ _, hL, hP⟩

end GlobalTheory.UPoinc.GPeriods

theorem GlobalTheory.UPoinc.GPeriods.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = T.be (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hpt x
  obtain ⟨f, hf, hab, hβ⟩ := GlobalTheory.T.integerAction_semiAbelian_along_traits_over_moduli E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hS, hG, hL, hP⟩ :=
    GlobalTheory.UPoinc.GPeriods.exists_completion_unif out hO x
  have hm : ∀ a : 𝓞 E, ∃ m : D.toPre.X →+ D.toPre.X, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧
      EndChar U fR m := by
    intro a
    haveI := hf a
    obtain ⟨fR, hfR, e⟩ := GlobalTheory.PullAction.exists_lift_end hG (f a)
    obtain ⟨m, hm⟩ := GlobalTheory.Poinc.Eq8.endChar_exists_of_isMonHom R hB G hS D A U fR hfR
    exact ⟨m, fR, hfR, e, hm⟩
  choose m hm using hm
  have key := fun (T : UTrait Xo c) (ψ : R →+* T.V) (hψ : IsLocalHom ψ) hc =>
    GlobalTheory.T.exists_traitLattice_equiv_completedLocalRing E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt f hf hab hβ x R j hB hC G gm hS hG D A U hL hP m hm T ψ hψ hc
  haveI : CharZero R := hB.2
  have hco : ∀ y : D.toPre.X, ∃ s, PsiCoord D.toPre y s := fun y =>
    ((GlobalTheory.PsiCoordLocal.main R D hB.1.2.2.1 y).1).imp fun _ h => h.1
  choose s hs using hco
  by_cases hex : ∃ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ ∧
      jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i
  · obtain ⟨T₀, ψ₀, hψ₀, hc₀⟩ := hex
    obtain ⟨ρ₀, -, hρ₀⟩ := key T₀ ψ₀ hψ₀ hc₀
    refine ⟨R, inferInstance, inferInstance, inferInstance, j, T₀.P.D.toPre.X, inferInstance, inferInstance,
      fun y => s (ρ₀.symm y) ^ 2, hB, hC, ?_⟩
    intro T ψ hψ hc
    obtain ⟨ρT, hord, heq⟩ := key T ψ hψ hc
    have hsymm : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), ρ₀.symm (H.bar a • v) = m a (ρ₀.symm v) := fun a v => by
      apply ρ₀.injective
      rw [AddEquiv.apply_symm_apply, hρ₀, AddEquiv.apply_symm_apply]
    let e₀ : T₀.P.D.toPre.X ≃+ T.P.D.toPre.X := ρ₀.symm.trans ρT
    have hlin : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), e₀ (a • v) = a • e₀ v := fun a v => by
      obtain ⟨b, rfl⟩ := H.bar.surjective a
      show ρT (ρ₀.symm (H.bar b • v)) = H.bar b • ρT (ρ₀.symm v)
      rw [hsymm, heq]
    refine ⟨{ e₀ with map_smul' := hlin }, fun y => ?_⟩
    obtain ⟨h0, hA⟩ := hord (ρ₀.symm y) (s (ρ₀.symm y)) (hs _)
    refine ⟨(T.be (ρT (ρ₀.symm y)) (ρT (ρ₀.symm y))).toNat, Int.toNat_of_nonneg h0, ?_⟩
    rw [map_pow]
    exact hA
  · refine ⟨R, inferInstance, inferInstance, inferInstance, j, PUnit, inferInstance, inferInstance, fun _ => 0, hB, hC,
      fun T ψ hψ hc => (hex ⟨T, ψ, hψ, hc⟩).elim⟩

end
end
end
