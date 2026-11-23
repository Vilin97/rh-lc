module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoverLinkedThetaSystems
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldPointFiniteSurjectiveAfterExtensi
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoverLinkedThetaSystemsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_finite_cover_linked_thetaSystems : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Xo.XF c), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (yM : Sp K ⟶ X₁.M.Z), GlobalTheory.GSep.ULink C X₁ act u π ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ (∃ (U : C.Z.Opens) (g' : X₁.M.Z ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = π ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧ yM ≫ π = y' ≫ q ≫ C.i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  first | exact @GlobalTheory.UCovSep.exists_linked_cov | exact GlobalTheory.UCovSep.exists_linked_cov | (intros; apply GlobalTheory.UCovSep.exists_linked_cov <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGenericFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep.Setup

def RootsIn {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) (F : Polynomial V) : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (ψ : V₁ →+* D) (d : D), F.eval₂ (ψ.comp ρ) d = 0 → d ∈ ψ.range

theorem rootsIn_of_splits {V V₁ : Type} [CommRing V] [CommRing V₁] (ρ : V →+* V₁) {F : Polynomial V} (hF : F.Monic)
    (h : (F.map ρ).Splits) : RootsIn ρ F := by
  intro D _ _ ψ d hd
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.1 h
  rw [← Polynomial.eval₂_map, hm, (hF.map ρ).leadingCoeff, map_one, _root_.one_mul, Polynomial.eval₂_multiset_prod,
    Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  obtain ⟨a, -, ha⟩ := hd
  exact ⟨a, (sub_eq_zero.1 (by simpa using ha)).symm⟩

theorem exists_ext (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V) (L : Type) [Field L]
    [Algebra (FractionRing V) L] [FiniteDimensional (FractionRing V) L] (F : Polynomial V) (hF : F.Monic) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (σ : L →+* FractionRing V₁),
      GlobalTheory.Mum.Base V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧
      (σ.comp (algebraMap (FractionRing V) L)).comp (algebraMap V _) = (algebraMap V₁ _).comp ρ ∧ RootsIn ρ F := by
  haveI := hV.2
  let K := FractionRing V
  let F₁ : Polynomial L := F.map ((algebraMap K L).comp (algebraMap V K))
  let L₂ := F₁.SplittingField
  haveI : FiniteDimensional K L₂ := Module.Finite.trans L L₂
  obtain ⟨E, _, _, _, _, j, ζ, hζ⟩ := MumLevel.exists_galois_root K L₂ 1 le_rfl
  obtain ⟨V₁, _, _, _, ρ, e, -, hρ, he, -, -⟩ := MumLevel.exists_ring V hV E ζ 1 le_rfl hζ
  let τ : L₂ →+* FractionRing V₁ := e.toRingHom.comp j.toRingHom
  have hσ : ((τ.comp (algebraMap L L₂)).comp (algebraMap K L)).comp (algebraMap V K) = (algebraMap V₁ _).comp ρ :=
    RingHom.ext fun r => (congrArg e ((congrArg j (IsScalarTower.algebraMap_apply K L L₂ _).symm).trans
      (j.commutes _))).trans (he r)
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  haveI := hρ.1.2.2.1
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, τ.comp (algebraMap L L₂),
    ⟨hρ.1, (ρ.charZero_iff hρ.2.1).1 inferInstance⟩, hρ.2.1, hρ.2.2, hσ, rootsIn_of_splits ρ hF ?_⟩
  refine Polynomial.Splits.of_splits_map_of_injective hinj ?_ fun a ha => ?_
  · have := (Polynomial.SplittingField.splits F₁).map τ
    rw [Polynomial.map_map, Polynomial.map_map, ← RingHom.comp_assoc, hσ] at this
    rwa [Polynomial.map_map]
  · exact IsIntegrallyClosed.isIntegral_iff.1 ⟨F.map ρ, hF.map ρ, by
      rw [← Polynomial.eval_map]; exact (Polynomial.mem_roots'.1 ha).2⟩

theorem RootsIn.exists_sq {V V₁ : Type} [CommRing V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {F : Polynomial V}
    (h : RootsIn ρ F) {s : V} (hs : Polynomial.X ^ 2 - Polynomial.C s ∣ F) : ∃ r : V₁, r ^ 2 = ρ s := by
  let D := AlgebraicClosure (FractionRing V₁)
  let ψ : V₁ →+* D := (algebraMap (FractionRing V₁) D).comp (algebraMap V₁ _)
  have hψ : Function.Injective ψ := (algebraMap (FractionRing V₁) D).injective.comp (IsFractionRing.injective V₁ _)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (ψ (ρ s)) two_pos
  obtain ⟨G, rfl⟩ := hs
  obtain ⟨r, rfl⟩ := h D ψ d (by simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, hd])
  exact ⟨r, hψ (by rw [map_pow, hd])⟩


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


theorem exists_lift_genericFibre (C : UCompact Xo c) {O W : Type} [CommRing O] [CommRing W] (ev : O →+* W) [IsLocalHom ev]
    (t : Sp O ⟶ C.Z) (ξ : Sp W ⟶ pullback C.z (spMap C.b)) (h : spMap ev ≫ t = ξ ≫ pullback.fst _ _) :
    ∃ ζ : Sp O ⟶ pullback C.z (spMap C.b), ζ ≫ pullback.fst _ _ = t := by
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ C.z)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (ξ ≫ pullback.snd _ _)
  have e : φ ≫ CommRingCat.ofHom ev = CommRingCat.ofHom C.b ≫ β := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hβ, ← Category.assoc, h, Category.assoc, Category.assoc, pullback.condition])
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (φ.hom a) := fun a => by
    refine (isUnit_map_iff ev _).1 ?_
    rw [show ev (φ.hom a) = β.hom (C.b a) from congrArg (fun χ => χ.hom a.1) e]
    exact (IsLocalization.map_units c.F a).map β.hom
  refine ⟨pullback.lift t (spMap (IsLocalization.lift (S := c.F) hu)) ?_, pullback.lift_fst _ _ _⟩
  rw [← hφ, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (IsLocalization.lift_comp (S := c.F) hu).symm)

theorem fromSpecStalk_bot {X : Scheme.{0}} [IsIntegral X] (z : X) (p : Sp (X.presheaf.stalk z)) (hp : p.asIdeal = ⊥) :
    X.fromSpecStalk z p = genericPoint X := by
  obtain ⟨q, hq⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes z
  have h : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (show p.asIdeal ≤ q.asIdeal from hp ▸ bot_le)
  exact ((hq ▸ h.map (X.fromSpecStalk z).continuous).antisymm (genericPoint_specializes _)).eq

end GlobalTheory.USep.Setup
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinkedThetaSystemRegularMonomialFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.GSep

theorem exists_uLink_regAt_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : V →+* V₁) (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (r : Fin Cm.m → V₁), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ GlobalTheory.GSep.ULink C X₁ act u π ∧ IsCov C π z₁ ζ ∧ IsCN V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ev₁ ∧ GlobalTheory.GSep.RegAt X₁ z₁ ev₁ ∧ spMap ev₁ ≫ ζ = spMap ρ₁ ≫ ξ ∧ ∀ k, r k ^ 2 = ρ₁ (Cm.s k) := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hV ξ hξ n hn ho j₀
  classical
  obtain ⟨j, Y, q, hj, hqf, hqs, hB⟩ := GlobalTheory.T.exists_finite_cover_linked_thetaSystems E H Dw hpq l Xo c C n hn ho j₀
  obtain ⟨L, _, _, _, yL, hyL⟩ := GlobalTheory.FinLift.lift_point_finite_surjective (FractionRing V) _ _ Cm.y q hqf hqs
  obtain ⟨X₁, act, u, π, yM, hlink, hrN, ⟨U, g', hg', hgU, hrange⟩, hyM, hreg⟩ := hB L yL
  let G : Polynomial V := ∏ k, (Polynomial.X ^ 2 - Polynomial.C (Cm.s k))
  have hG : G.Monic := Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_pow_sub_C _ two_ne_zero
  obtain ⟨V₁, _, _, _, ρ₁, σ, hV₁, hinj, hfin, hσ, hR⟩ := GlobalTheory.USep.Setup.exists_ext V hV L G hG
  choose r hr₂ using fun k => hR.exists_sq
    (Finset.dvd_prod_of_mem (fun k => Polynomial.X ^ 2 - Polynomial.C (Cm.s k)) (Finset.mem_univ k))
  have hr : Set.range (ξ ≫ pullback.fst _ _ :) ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hrange ⟨ξ p, rfl⟩
  let f : Sp V ⟶ U.toScheme := IsOpenImmersion.lift U.ι _ hr
  have hf : f ≫ U.ι = ξ ≫ pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ _
  have hkey : spMap σ ≫ spMap (algebraMap (FractionRing V) L) ≫ jK V = jK V₁ ≫ spMap ρ₁ := by
    simp only [← Spec.map_comp]
    exact congrArg (fun χ => spMap χ) hσ
  have hcomp : (spMap σ ≫ yM) ≫ g' = jK V₁ ≫ spMap ρ₁ ≫ f := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [hgU, hyM, hf, ← Category.assoc yL, hyL]
    simp only [Category.assoc, UCompact.i]
    rw [← Category.assoc Cm.y, hξ]
    simp only [Category.assoc]
    rw [reassoc_of% hkey]
  obtain ⟨z₁, ev, hloc, hev, hev2⟩ := GlobalTheory.FiniteLift.exists_stalk_lift V₁ hV₁.1.2.2.1 X₁.M.Z U.toScheme g' hg'
    (spMap ρ₁ ≫ f) (spMap σ ≫ yM) hcomp
  have hev' : spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = (spMap ρ₁ ≫ ξ) ≫ pullback.fst _ _ := by
    rw [← hgU, reassoc_of% hev, hf, Category.assoc]
  haveI := hloc
  obtain ⟨ζ, hζ⟩ := GlobalTheory.USep.Setup.exists_lift_genericFibre C ev _ _ hev'
  haveI : IsPreimmersion (spMap C.b) := by
    letI : Algebra C.o c.F := C.b.toAlgebra
    haveI := C.isFractionRing
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hgen : ∀ p : Sp (X₁.M.Z.presheaf.stalk z₁), p.asIdeal = ⊥ → ζ p ∈ Set.range C.iF := by
    intro p hp
    have hpt := hlink.2.2.2
    have h1 : π (genericPoint X₁.M.Z) =
        (pullback.fst C.z (spMap C.b)) (C.iF (u (spMap (ratHull X₁.S.R).val.toRingHom (closedPoint X₁.Ω₁)))) := by
      rw [← X₁.M.pt_apply (closedPoint X₁.Ω₁)]
      exact congrArg (fun χ : Sp X₁.Ω₁ ⟶ C.Z => χ (closedPoint X₁.Ω₁)) hpt
    refine ⟨u (spMap (ratHull X₁.S.R).val.toRingHom (closedPoint X₁.Ω₁)),
      (pullback.fst C.z (spMap C.b)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply ζ, hζ, Scheme.Hom.comp_apply, GlobalTheory.USep.Setup.fromSpecStalk_bot z₁ p hp, h1]
  refine ⟨j, X₁, act, u, π, z₁, ζ, V₁, inferInstance, inferInstance, inferInstance, ρ₁, ev, r, hj, hrN, hlink,
    ⟨X₁.normal, ⟨U, g', hg', hgU, hrange⟩, hζ, hgen⟩, ⟨hV₁.1.1, hV₁.1.2.2.1, hV₁.1.2.2.2, hV₁.2⟩, hinj, hfin, hloc, ?_, ?_, hr₂⟩
  · intro a ha
    rw [hev2]
    convert hreg a ha using 2
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg yM (Subsingleton.elim (α := PrimeSpectrum L) _ _))
  · rw [← cancel_mono (pullback.fst C.z (spMap C.b)), Category.assoc, hζ, hev']

end GlobalTheory.GSep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinkedThetaSystemRegularMonomialFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_linked_thetaSystem_regular_monomialFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : V →+* V₁) (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (r : Fin Cm.m → V₁), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ GlobalTheory.GSep.ULink C X₁ act u π ∧ IsCov C π z₁ ζ ∧ IsCN V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ev₁ ∧ GlobalTheory.GSep.RegAt X₁ z₁ ev₁ ∧ spMap ev₁ ≫ ζ = spMap ρ₁ ≫ ξ ∧ ∀ k, r k ^ 2 = ρ₁ (Cm.s k) := by
  first | exact @GlobalTheory.GSep.exists_uLink_regAt_chart | exact GlobalTheory.GSep.exists_uLink_regAt_chart | (intros; apply GlobalTheory.GSep.exists_uLink_regAt_chart <;> assumption)
end
end
