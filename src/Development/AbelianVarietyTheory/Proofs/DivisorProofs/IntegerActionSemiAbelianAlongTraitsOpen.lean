module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompleteDVROfGenericCompatStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullEndo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitaryStatement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericSemiAbelianCompleteDVRStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismExtOfDensePoint

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

namespace GlobalTheory

theorem abelianScheme_end_ext_of_dense : ∀ (W : Scheme.{0}) [IsIntegral W] (G : Over W) [GrpObj G], IsAbelianScheme G → ∀ (Ω : Type) [Field Ω] (pt : Sp Ω ⟶ W), Dense (Set.range pt) → ∀ (f f' : G ⟶ G), pullback.fst G.hom pt ≫ f.left = pullback.fst G.hom pt ≫ f'.left → f = f' := by
  intro W _ G _ hG Ω _ pt hpt f f' h
  have : Smooth G.hom := hG.smooth
  have : IsProper G.hom := hG.proper
  have : IsDominant pt := ⟨hpt⟩
  have : QuasiCompact pt := inferInstance
  have := IsSchemeTheoreticallyDominant.of_isDominant pt
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom pt) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G.hom pt).flip
  exact Over.OverMorphism.ext (ext_of_schDom G.hom ((Over.w f).trans (Over.w f').symm)
    (pullback.fst G.hom pt) h)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismExtOfDensePointStatement

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

theorem _root_.GlobalTheory.T.abelianScheme_endomorphism_ext_of_dense_point : ∀ (W : Scheme.{0}) [IsIntegral W] (G : Over W) [GrpObj G], IsAbelianScheme G → ∀ (Ω : Type) [Field Ω] (pt : Sp Ω ⟶ W), Dense (Set.range pt) → ∀ (f f' : G ⟶ G), pullback.fst G.hom pt ≫ f.left = pullback.fst G.hom pt ≫ f'.left → f = f' := by
  first | exact @GlobalTheory.abelianScheme_end_ext_of_dense | exact GlobalTheory.abelianScheme_end_ext_of_dense | (intros; apply GlobalTheory.abelianScheme_end_ext_of_dense <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralPullbackRationalSaturationModelOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH

namespace GlobalTheory.UPoinc

theorem isReduced_of_flat_isPreimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hfl := Flat.stalkMap f x
    have hs := f.stalkMap_surjective x
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hfl
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
    have hi : Function.Injective (f.stalkMap x).hom :=
      FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

theorem isIntegral_pullback_toRat : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  intro o Ω _ _ _ _ M U₀ R u₀ hne hgen
  haveI := M.integral
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  haveI : Flat (spMap (toRat R)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (IsLocalization.flat (ratHull R) (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)))
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (show w ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hx := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  have w : IsOpenImmersion.lift U₀.ι M.pt hr ≫ u₀ = spMap (ratHull R).val.toRingHom ≫ spMap (toRat R) :=
    (hgen _ hx).trans (spMap_val_toRat R).symm
  let pt := pullback.lift _ _ w
  let j : pullback u₀ (spMap (toRat R)) ⟶ M.Z := pullback.fst _ _ ≫ U₀.ι
  have hpt : pt ≫ j = M.pt := by rw [← Category.assoc, pullback.lift_fst, hx]
  haveI : IsPreimmersion j := inferInstance
  haveI : Flat j := inferInstance
  haveI := isReduced_of_flat_isPreimmersion j
  have hj : ∀ y, j (pt y) = genericPoint M.Z := fun y => by
    rw [← Scheme.Hom.comp_apply, hpt]
    exact M.gen.le ⟨y, rfl⟩
  have hg : IsGenericPoint (pt default) Set.univ := by
    refine isGenericPoint_iff_specializes.2 fun z => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hj]
    exact genericPoint_specializes _
  haveI : IrreducibleSpace (pullback u₀ (spMap (toRat R)) :) :=
    (irreducibleSpace_def _).2 hg.isIrreducible
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, pt, hpt, ?_⟩
  exact Dense.mono (Set.singleton_subset_iff.2 ⟨default, rfl⟩) (dense_iff_closure_eq.2 hg)

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralPullbackRationalSaturationModelOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH

theorem _root_.GlobalTheory.T.isIntegral_pullback_rationalSaturation_model_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  first | exact @GlobalTheory.UPoinc.isIntegral_pullback_toRat | exact GlobalTheory.UPoinc.isIntegral_pullback_toRat | (intros; apply GlobalTheory.UPoinc.isIntegral_pullback_toRat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionExtendsSemiAbelianThetaModel

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

theorem GlobalTheory.UPoinc.exists_endo_of_generic {Z W : Scheme.{0}} [IsIntegral W] {G : Over Z} [GrpObj G] {G₀ : Over W}
    [GrpObj G₀] (hab : IsAbelianScheme G₀) {q : W ⟶ Z} {Φ : G₀.left ⟶ G.left} (hΦ : IsGrpPullback G₀ G q Φ)
    {Ω : Type} [Field Ω] (pt : Sp Ω ⟶ W) (hd : Dense (Set.range pt)) (m : Sp Ω ⟶ Z) (hm : pt ≫ q = m)
    (hendo : ∀ f : (Over.pullback m).obj G ⟶ (Over.pullback m).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback m).map F = f)
    (f₀ : G₀ ⟶ G₀) (hf₀ : IsMonHom f₀) : ∃ F : G ⟶ G, IsMonHom F ∧ Φ ≫ F.left = f₀.left ≫ Φ := by
  have hgen := isGrpPullback_pullback G m
  have wk : pullback.fst G.hom m ≫ G.hom = (pullback.snd G.hom m ≫ pt) ≫ q := by
    rw [Category.assoc, hm, pullback.condition]
  let k : pullback G.hom m ⟶ G₀.left := hΦ.1.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pt) wk
  have hk : IsGrpPullback ((Over.pullback m).obj G) G₀ pt k :=
    hΦ.cancel (hgen.congr hm.symm (hΦ.1.lift_fst _ _ _).symm) (hΦ.1.lift_snd _ _ _)
  obtain ⟨e, he, hek⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hk f₀ hf₀
  obtain ⟨F, ⟨hF, hFe⟩, -⟩ := hendo e he
  obtain ⟨F₀, hF₀, hF₀e⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hΦ F hF
  have wθ : (pullback.fst G₀.hom pt ≫ Φ) ≫ G.hom = pullback.snd G₀.hom pt ≫ m := by
    rw [Category.assoc, hΦ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hm]
  let θ : pullback G₀.hom pt ⟶ pullback G.hom m := pullback.lift _ _ wθ
  have hθk : θ ≫ k = pullback.fst _ _ := by
    apply hΦ.1.hom_ext
    · rw [Category.assoc, hΦ.1.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hΦ.1.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.condition]
  have hFm : ((Over.pullback m).map F).left ≫ pullback.fst G.hom m = pullback.fst G.hom m ≫ F.left := by
    first | exact pullback.lift_fst _ _ _ | (simp [Over.pullback, pullback.map]) | (erw [pullback.lift_fst])
  have key : F₀ = f₀ := by
    apply GlobalTheory.T.abelianScheme_endomorphism_ext_of_dense_point W G₀ hab Ω pt hd
    apply hΦ.1.hom_ext
    · calc (pullback.fst G₀.hom pt ≫ F₀.left) ≫ Φ = pullback.fst G₀.hom pt ≫ Φ ≫ F.left := by
            rw [Category.assoc, hF₀e]
        _ = θ ≫ pullback.fst G.hom m ≫ F.left := by rw [← Category.assoc θ, pullback.lift_fst, Category.assoc]
        _ = θ ≫ e.left ≫ pullback.fst G.hom m := by rw [← hFm, hFe]
        _ = θ ≫ e.left ≫ k ≫ Φ := by rw [hΦ.1.lift_fst]
        _ = θ ≫ k ≫ f₀.left ≫ Φ := by rw [← Category.assoc e.left, hek, Category.assoc]
        _ = (pullback.fst G₀.hom pt ≫ f₀.left) ≫ Φ := by rw [← Category.assoc θ, hθk, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w F₀, Over.w f₀]
  exact ⟨F, hF, by rw [← hF₀e, key]⟩

theorem GlobalTheory.UPoinc.act_extends_ratModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ ∀ (K : Type) [Field K] (ξ₀ : Sp K ⟶ U₀.toScheme) (y : Sp K ⟶ Xo.XF c), X₁.Lies (ξ₀ ≫ out.u₀) y → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G (ξ₀ ≫ U₀.ι) γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  haveI := X₁.ar.char
  obtain ⟨hW, pt, hpt, hd⟩ := GlobalTheory.T.isIntegral_pullback_rationalSaturation_model_open X₁.o₁ X₁.Ω₁ M U₀ X₁.S.R out.u₀ hAdm.1.ne out.u₀_gen
  haveI := hW
  obtain ⟨G₁, _, α, β, hα, hβ, hL⟩ := X₁.pulled
  let s : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Sp (ratHull X₁.S.R) := pullback.snd _ _
  let G₀ : Over (pullback out.u₀ (spMap (toRat X₁.S.R))) := (Over.pullback s).obj G₁
  have h₀ : IsGrpPullback G₀ G₁ s (pullback.fst G₁.hom s) := isGrpPullback_pullback G₁ s
  let w : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Xo.XF c := s ≫ X₁.u
  have hβ₀ : IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) (pullback.fst G₁.hom s ≫ β) :=
    (h₀.comp hβ).congr (Category.assoc _ _ _).symm rfl
  obtain ⟨f₀, hf₀, hT⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c _ w G₀ _ hβ₀
  have hα₀ := h₀.comp hα
  have wψ : (pullback.fst G₁.hom s ≫ α) ≫ X₁.ρ.P.A.hom = (G₀.hom ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ≫ out.u₀ := by
    rw [hα₀.1.w, Category.assoc, pullback.condition]
  let ψ : G₀.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift _ _ wψ
  have hψ : IsGrpPullback G₀ ((Over.pullback out.u₀).obj X₁.ρ.P.A) (pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ψ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (hα₀.congr pullback.condition.symm (pullback.lift_fst _ _ _).symm)
      (pullback.lift_snd _ _ _)
  have hΦ := hψ.comp out.cart
  have hm : pt ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R)) ≫ U₀.ι = M.pt := hpt
  have hab : IsAbelianScheme G₀ := PolPull.isAbelianScheme_of_isGrpPullback X₁.ρ.P.isAb hα₀
  choose F hF hFe using fun a => exists_endo_of_generic hab hΦ pt hd M.pt hm out.endo (f₀ a) (hf₀ a).1
  refine ⟨F, hF, ?_⟩
  intro K _ ξ₀ y hLies tK ⟨mm⟩
  obtain ⟨x', hx', hxy⟩ := hLies
  let x : Sp K ⟶ pullback out.u₀ (spMap (toRat X₁.S.R)) := pullback.lift ξ₀ x' hx'.symm
  have hxw : x ≫ w = y := by
    show x ≫ pullback.snd _ _ ≫ X₁.u = y
    rw [← Category.assoc, pullback.lift_snd, hxy]
  have mm' : SABMap tK Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _) := by rw [hxw]; exact mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hact⟩ := hT (Sp K) x tK mm'
  refine ⟨γ₀ ≫ ψ ≫ out.φ, (hγ₀.comp hΦ).congr (by rw [← Category.assoc, pullback.lift_fst]) rfl, ?_, fun a => ?_⟩
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hO := out.L.isLB
    have i1 : LBIso (out.L.L.pull out.φ) (X₁.ρ.P.L.pull (pullback.fst X₁.ρ.P.A.hom out.u₀)) := ⟨out.w, out.w_gen⟩
    have i2 : LBIso (out.L.L.pull (ψ ≫ out.φ)) (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) :=
      GenSpread.lbIso_pull_comp ψ rfl (pullback.lift_fst _ _ _).symm i1
    have i3 : LBIso (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) (Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp (pullback.fst G₁.hom s) rfl rfl hL
    have i4 := LBIso.trans (pull_isLB hO _) (pull_isLB hP _) (pull_isLB hU _) i2 i3
    have i5 : LBIso (out.L.L.pull (γ₀ ≫ ψ ≫ out.φ)) (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp γ₀ rfl rfl i4
    have i6 : LBIso (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β))
        ((Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)).pull γ₀) := GenSpread.lbIso_pull_pull hU γ₀ rfl
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hO _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB hO _) i6.symm i5.symm)
  · rw [← Category.assoc, hact a, Category.assoc, Category.assoc, ← hFe a, Category.assoc]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionExtendsSemiAbelianThetaModelStatement

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

theorem _root_.GlobalTheory.T.integerAction_extends_semiAbelian_thetaModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ ∀ (K : Type) [Field K] (ξ₀ : Sp K ⟶ U₀.toScheme) (y : Sp K ⟶ Xo.XF c), X₁.Lies (ξ₀ ≫ out.u₀) y → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G (ξ₀ ≫ U₀.ι) γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  first | exact @GlobalTheory.UPoinc.act_extends_ratModel | exact GlobalTheory.UPoinc.act_extends_ratModel | (intros; apply GlobalTheory.UPoinc.act_extends_ratModel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOpen

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

namespace GlobalTheory.UPoinc

theorem oAct_along_traits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  obtain ⟨f, hfm, H0⟩ := GlobalTheory.T.integerAction_extends_semiAbelian_thetaModel E H Dw l Xo c C X₁ M U₀ EE out hAdm
  refine ⟨f, hfm, ?_⟩
  rintro T ξ ⟨ξ₀, hξ₀, hlies⟩
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  obtain ⟨γ, hγ, hγL, hγa⟩ := H0 (FractionRing T.V) ξ₀ T.y hlies tK ⟨m₂⟩
  obtain ⟨β, hβ, hφβ, hβa⟩ := GlobalTheory.T.exists_grpPullback_completeDVR_of_generic_compat T.V T.cdvr T.t.G T.t.semi M.Z out.G out.semi ξ tK.G m₁.φ γ m₁.cart
    (hγ.congr hξ₀ rfl)
  refine ⟨β, hβ, ?_, fun a => hβa (T.t.act.act a) (f a) (tK.act.act a) (m₁.act a) (hγa a)⟩
  have h₁ : LBIso tK.PP.L (T.t.PP.L.pull m₁.φ) := by
    obtain ⟨w, hw, -⟩ := m₁.lin
    exact ⟨w, hw⟩
  have hL := out.L.isLB
  refine GlobalTheory.T.lineBundleIso_of_generic_semiAbelian_completeDVR T.V T.cdvr T.t.G T.t.semi tK.G m₁.φ m₁.cart _ _ T.t.PP.isLB (pull_isLB hL β) ?_
  exact LBIso.trans (pull_isLB T.t.PP.isLB _) tK.PP.isLB (pull_isLB (pull_isLB hL β) _) (LBIso.symm h₁)
    (LBIso.trans tK.PP.isLB (pull_isLB hL γ) (pull_isLB (pull_isLB hL β) _) hγL
      (GenSpread.lbIso_pull_pull hL m₁.φ hφβ.symm))

end GlobalTheory.UPoinc
end
end
