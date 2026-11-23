module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellationStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfTorusExtensionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMap

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

theorem GlobalTheory.Nef.RatRigidField.spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

namespace GlobalTheory.Nef

theorem isRatPath_map {F Ω : Type} [Field F] [Field Ω] (φ : F →+* Ω) {Y : Scheme.{0}}
    (ξ : Sp (PowerSeries F) ⟶ Y) (h : IsRatPath ξ) : IsRatPath (spMap (PowerSeries.map φ) ≫ ξ) := by
  obtain ⟨β, hβ⟩ := h
  have hinjP : Function.Injective
      ((algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp (PowerSeries.map φ)) :=
    (IsFractionRing.injective (PowerSeries Ω) (LaurentSeries Ω)).comp
      (PowerSeries.map_injective φ φ.injective)
  have hinjR : Function.Injective
      ((algebraMap (Polynomial Ω) (RatFunc Ω)).comp (Polynomial.mapRingHom φ)) :=
    (IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)).comp
      (Polynomial.map_injective φ φ.injective)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LaurentSeries F →+* LaurentSeries Ω, ψ.comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp (PowerSeries.map φ) :=
    by
    refine ⟨IsFractionRing.lift hinjP, ?_⟩
    ext1 x
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  obtain ⟨ρ, hρ0⟩ : ∃ ρ : RatFunc F →+* RatFunc Ω, ρ.comp (algebraMap (Polynomial F) (RatFunc F)) =
      (algebraMap (Polynomial Ω) (RatFunc Ω)).comp (Polynomial.mapRingHom φ) :=
    by
    refine ⟨IsFractionRing.lift hinjR, RingHom.ext fun x => ?_⟩
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  have hpol : ((algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp ρ).comp (algebraMap (Polynomial F) (RatFunc F)) =
      (ψ.comp (algebraMap (RatFunc F) (LaurentSeries F))).comp (algebraMap (Polynomial F) (RatFunc F)) := by
    refine RingHom.ext fun p => ?_
    have h1 : ρ (algebraMap (Polynomial F) (RatFunc F) p) =
        algebraMap (Polynomial Ω) (RatFunc Ω) (p.map φ) := by
      have := congrArg (fun f => f p) hρ0
      simpa using this
    have h2 : ψ (algebraMap (PowerSeries F) (LaurentSeries F) (p : PowerSeries F)) =
        algebraMap (PowerSeries Ω) (LaurentSeries Ω) (PowerSeries.map φ (p : PowerSeries F)) :=
      congrArg (fun f => f (p : PowerSeries F)) hψ
    have h3 : PowerSeries.map φ (p : PowerSeries F) = ((p.map φ : Polynomial Ω) : PowerSeries Ω) := by
      ext n; simp [Polynomial.coeff_map]
    have hc : ∀ (K : Type) [Field K] (q : Polynomial K),
        algebraMap (RatFunc K) (LaurentSeries K) (algebraMap (Polynomial K) (RatFunc K) q) =
          algebraMap (PowerSeries K) (LaurentSeries K) (q : PowerSeries K) :=
      fun K _ q => (RatFunc.coe_coe q).symm
    simp only [RingHom.comp_apply]
    rw [h1, hc, hc, h2, h3]
  have hρ : (algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp ρ =
      ψ.comp (algebraMap (RatFunc F) (LaurentSeries F)) :=
    IsLocalization.ringHom_ext (M := nonZeroDivisors (Polynomial F)) (S := RatFunc F) hpol
  refine ⟨spMap ρ ≫ β, ?_⟩
  have e1 : spMap (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ≫ spMap ρ =
      spMap ψ ≫ spMap (algebraMap (RatFunc F) (LaurentSeries F)) := by
    rw [← RatRigidField.spMap_comp, ← RatRigidField.spMap_comp, hρ]
  have e2 : spMap ψ ≫ spMap (algebraMap (PowerSeries F) (LaurentSeries F)) =
      spMap (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) ≫ spMap (PowerSeries.map φ) := by
    rw [← RatRigidField.spMap_comp, ← RatRigidField.spMap_comp, hψ]
  rw [← Category.assoc, e1, Category.assoc, hβ, ← Category.assoc, e2, Category.assoc]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem ratRigid_of_field_map (S : Scheme.{0}) (G : Over S) [GrpObj G] (F Ω : Type) [Field F] [Field Ω]
    (φ : F →+* Ω) (b : Sp F ⟶ S) (h : RatRigid G (spMap φ ≫ b)) : RatRigid G b := by
  intro ξ hξ hr
  have hp := ((GlobalTheory.T.formalSquaringPaths_baseChange_and_hom).1 S G F Ω φ 2 1 b ξ hξ).1
  rw [PowerSeries.rescale_one, RingHom.id_comp, map_ofNat] at hp
  have e := h _ hp (isRatPath_map φ ξ hr)
  have hC : (PowerSeries.map φ).comp (PowerSeries.C (R := F)) = (PowerSeries.C (R := Ω)).comp φ := by
    ext1 x; simp
  have ht : spMap (PowerSeries.map φ) ≫ triv G b = triv G (spMap φ ≫ b) := by
    simp only [triv]
    rw [← Category.assoc, ← RatRigidField.spMap_comp, hC, RatRigidField.spMap_comp]
    simp only [Category.assoc]
  exact (GlobalTheory.T.spec_injectiveRingMap_cancellation).1 _ _ (PowerSeries.map φ) (PowerSeries.map_injective φ φ.injective) _ _ _
    (e.trans ht.symm)

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMapStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (F Ω : Type) [Field F] [Field Ω] (φ : F →+* Ω) (b : Sp F ⟶ S), RatRigid G (spMap φ ≫ b) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_field_map | exact GlobalTheory.Nef.ratRigid_of_field_map | (intros; apply GlobalTheory.Nef.ratRigid_of_field_map <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibre

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratFunc_C_laurent (F : Type) [Field F] : (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C =
    (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  ext1 a
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

theorem sqr_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : sqr G' ≫ φ = φ ≫ sqr G := by
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e := h.2 G' (𝟙 G') (𝟙 G') x₀ x₀ rfl rfl
  have e2 : x₀ * x₀ = x₀ ≫ (𝟙 G * 𝟙 G) := by rw [comp_mul]; simp
  rw [e2] at e
  exact e.symm

theorem ratRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω]
    (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  intro S G _ Ω _ _ b hR ξ hξ ⟨β, hβ⟩
  have hp := isGrpPullback_pullback G b
  have hu : unitSec ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = b ≫ unitSec G := unitSec_comp hp
  have hs : sqr ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = pullback.fst G.hom b ≫ sqr G :=
    sqr_comp_of_isGrpPullback hp
  have hsh : sqr ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = pullback.snd G.hom b :=
    Over.w (𝟙 ((Over.pullback b).obj G) * 𝟙 ((Over.pullback b).obj G))
  have hus : unitSec ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = 𝟙 _ := sec_hom _
  let ξ' : Sp (PowerSeries Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift ξ (spMap PowerSeries.C) hξ.base
  have hξ₁ : ξ' ≫ pullback.fst G.hom b = ξ := pullback.lift_fst _ _ _
  have hξ₂ : ξ' ≫ pullback.snd G.hom b = spMap PowerSeries.C := pullback.lift_snd _ _ _
  have hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hpath : IsPath ((Over.pullback b).obj G) 2 (𝟙 (Sp Ω)) ξ' := by
    refine ⟨?_, ?_, ?_⟩
    · exact hξ₂.trans (Category.comp_id _).symm
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, hξ.zero, Category.assoc, hu, Category.id_comp]
      · rw [Category.assoc, hξ₂, Category.assoc, hus, Category.id_comp, hsp]
        have : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω := by
          ext a; simp
        rw [this]
        show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = _
        rw [CommRingCat.ofHom_id, Spec.map_id]
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, Category.assoc, hs, ← Category.assoc, hξ₁, hξ.scale]
      · rw [Category.assoc, hξ₂, Category.assoc, hsh, hξ₂, hsp]
        have : (PowerSeries.rescale (2 : Ω)).comp PowerSeries.C = PowerSeries.C := by
          ext1 a; ext n; rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
          rcases n with _ | n <;> simp
        rw [this]
  have hβb : β ≫ G.hom = spMap RatFunc.C ≫ b := by
    have cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    apply cancel (algebraMap (RatFunc Ω) (LaurentSeries Ω))
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, ← Category.assoc, ← Category.assoc, hsp, hsp,
      ratFunc_C_laurent]
  let β' : Sp (RatFunc Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift β (spMap RatFunc.C) hβb
  have hrat : IsRatPath ξ' := by
    refine ⟨β', ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hξ₁, hβ]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hξ₂, hsp, hsp, ratFunc_C_laurent]
  have e := hR ξ' hpath hrat
  rw [← hξ₁, e]
  simp only [triv, Category.assoc, hu, Category.id_comp]

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibreStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω] (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_fibre | exact GlobalTheory.Nef.ratRigid_of_fibre | (intros; apply GlobalTheory.Nef.ratRigid_of_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfIsSemiAbelian

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratRigid_of_isSemiAbelian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G →
    ∀ (F : Type) [Field F] [CharZero F] (b : Sp F ⟶ S), RatRigid G b := by
  intro S G _ hG F _ _ b
  let Ω := AlgebraicClosure F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hE : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap F Ω) ≫ b)).obj G)) :=
    hG.fibres Ω (spMap (algebraMap F Ω) ≫ b)
  have h1 := GlobalTheory.T.rationalSquaringPathsRigid_of_torusExtension Ω ((Over.pullback (spMap (algebraMap F Ω) ≫ b)).obj G) hE
  have h2 := GlobalTheory.T.rationalSquaringPathsRigid_of_fibre S G Ω (spMap (algebraMap F Ω) ≫ b) h1
  exact GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map S G F Ω (algebraMap F Ω) b h2

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfIsSemiAbelianStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_isSemiAbelian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (F : Type) [Field F] [CharZero F] (b : Sp F ⟶ S), RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_isSemiAbelian | exact GlobalTheory.Nef.ratRigid_of_isSemiAbelian | (intros; apply GlobalTheory.Nef.ratRigid_of_isSemiAbelian <;> assumption)
end
end
