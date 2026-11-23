module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickeningStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawGlueOverCoprodBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotentsStatement
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Limits
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackCoprodDescOfPiecesOverCoprod

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPullback_coprod_desc_of_pieces : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f : T ⟶ S) (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂), IsPullback v₁ f₁ f u₁ → IsPullback v₂ f₂ f u₂ → ∀ {X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂) (y : Y ⟶ T) (y₁ : Y₁ ⟶ T₁) (y₂ : Y₂ ⟶ T₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₁ ⟶ X₁) (i₂ : Y₂ ⟶ X₂), IsPullback j₁ y₁ y v₁ → IsPullback j₂ y₂ y v₂ → IsPullback i₁ y₁ x₁ f₁ → IsPullback i₂ y₂ x₂ f₂ → ∃ i : Y ⟶ X₁ ⨿ X₂, j₁ ≫ i = i₁ ≫ Limits.coprod.inl ∧ j₂ ≫ i = i₂ ≫ Limits.coprod.inr ∧ IsPullback i y (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) f := by
  intro S S₁ S₂ T T₁ T₂ u₁ u₂ hS v₁ v₂ hT f f₁ f₂ hf₁ hf₂ X₁ X₂ Y Y₁ Y₂ x₁ x₂ y y₁ y₂ j₁ j₂ i₁ i₂
    hj₁ hj₂ hi₁ hi₂
  obtain ⟨hS⟩ := hS
  obtain ⟨hT⟩ := hT
  obtain ⟨hY⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk j₁ j₂) y₁ y₂ y hj₁.w.symm hj₂.w.symm).mpr ⟨hj₁, hj₂⟩
  let x : X₁ ⨿ X₂ ⟶ S := Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)
  obtain ⟨hX₁, hX₂⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hS) (Limits.BinaryCofan.mk (Limits.coprod.inl : X₁ ⟶ X₁ ⨿ X₂)
    Limits.coprod.inr) x₁ x₂ x (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm).mp ⟨Limits.coprodIsCoprod X₁ X₂⟩
  obtain ⟨i, hi₁', hi₂'⟩ := Limits.BinaryCofan.IsColimit.desc' hY
    (i₁ ≫ Limits.coprod.inl) (i₂ ≫ Limits.coprod.inr)
  have e₁ : j₁ ≫ i = i₁ ≫ Limits.coprod.inl := hi₁'
  have e₂ : j₂ ≫ i = i₂ ≫ Limits.coprod.inr := hi₂'
  refine ⟨i, e₁, e₂, ?_⟩
  have H₁ : IsPullback (j₁ ≫ i) y₁ x (v₁ ≫ f) := by
    rw [e₁, hf₁.w]; exact hi₁.paste_horiz hX₁
  have H₂ : IsPullback (j₂ ≫ i) y₂ x (v₂ ≫ f) := by
    rw [e₂, hf₂.w]; exact hi₂.paste_horiz hX₂
  have w : i ≫ x = y ≫ f := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · change j₁ ≫ i ≫ x = j₁ ≫ y ≫ f
      rw [← Category.assoc j₁ i x, H₁.w, ← Category.assoc j₁ y f, hj₁.w, Category.assoc]
    · change j₂ ≫ i ≫ x = j₂ ≫ y ≫ f
      rw [← Category.assoc j₂ i x, H₂.w, ← Category.assoc j₂ y f, hj₂.w, Category.assoc]
  let c : Y ⟶ Limits.pullback x f := Limits.pullback.lift i y w
  have hcf : c ≫ Limits.pullback.fst x f = i := Limits.pullback.lift_fst _ _ _
  have hcs : c ≫ Limits.pullback.snd x f = y := Limits.pullback.lift_snd _ _ _
  have Q₁ : IsPullback (j₁ ≫ c) y₁ (Limits.pullback.snd x f) v₁ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₁)
      (by rw [Category.assoc, hcs]; exact hj₁.w)
      (IsPullback.of_hasPullback x f)
  have Q₂ : IsPullback (j₂ ≫ c) y₂ (Limits.pullback.snd x f) v₂ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₂)
      (by rw [Category.assoc, hcs]; exact hj₂.w)
      (IsPullback.of_hasPullback x f)
  obtain ⟨hP⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk (j₁ ≫ c) (j₂ ≫ c)) y₁ y₂ (Limits.pullback.snd x f)
    Q₁.w.symm Q₂.w.symm).mpr ⟨Q₁, Q₂⟩
  have hc : c = (hY.coconePointUniqueUpToIso hP).hom := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.left⟩).symm
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.right⟩).symm
  haveI : IsIso c := by rw [hc]; exact Iso.isIso_hom _
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) hcf hcs

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackCoprodDescOfPiecesOverCoprodStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPullback_coprodDesc_of_pieces_over_coprod : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f : T ⟶ S) (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂), IsPullback v₁ f₁ f u₁ → IsPullback v₂ f₂ f u₂ → ∀ {X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂) (y : Y ⟶ T) (y₁ : Y₁ ⟶ T₁) (y₂ : Y₂ ⟶ T₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₁ ⟶ X₁) (i₂ : Y₂ ⟶ X₂), IsPullback j₁ y₁ y v₁ → IsPullback j₂ y₂ y v₂ → IsPullback i₁ y₁ x₁ f₁ → IsPullback i₂ y₂ x₂ f₂ → ∃ i : Y ⟶ X₁ ⨿ X₂, j₁ ≫ i = i₁ ≫ Limits.coprod.inl ∧ j₂ ≫ i = i₂ ≫ Limits.coprod.inr ∧ IsPullback i y (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) f := by
  first | exact @GlobalTheory.isPullback_coprod_desc_of_pieces | exact GlobalTheory.isPullback_coprod_desc_of_pieces | (intros; apply GlobalTheory.isPullback_coprod_desc_of_pieces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSpMapQuotientSpanBaseChange

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotBaseChange

theorem isPushout_quot_span (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R)
    (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f})
    (hρ : ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π) :
    IsPushout (CommRingCat.ofHom π) (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π f}))) (CommRingCat.ofHom ρ) := by
  refine ⟨⟨by ext a; exact (congr($hρ a)).symm⟩, ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift (Ideal.span {π f}) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩
  · intro b hb
    have e : ∀ a, s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := fun a => congr($(s.condition) a)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [map_mul, e, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f), map_zero, mul_zero]
  · intro s
    ext b
    rfl
  · intro s
    ext a
    have e : s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := congr($(s.condition) a)
    have e2 : ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (π a) := congr($hρ a)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [e2, Ideal.Quotient.lift_mk, e]
  · intro s m h₁ _
    ext b
    have e : m.hom (Ideal.Quotient.mk _ b) = s.inl.hom b := congr($h₁ b)
    exact e

theorem isPullback_spMap_quot : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π → IsPullback (spMap (Ideal.Quotient.mk (Ideal.span {π f}))) (spMap ρ) (spMap π) (spMap (Ideal.Quotient.mk (Ideal.span {f}))) := by
  intro R R₀ _ _ π f ρ hρ
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot_span R R₀ π f ρ hρ)

end GlobalTheory.QuotBaseChange
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSpMapQuotientSpanBaseChangeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPullback_spMap_quotient_span_baseChange : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π → IsPullback (spMap (Ideal.Quotient.mk (Ideal.span {π f}))) (spMap ρ) (spMap π) (spMap (Ideal.Quotient.mk (Ideal.span {f}))) := by
  first | exact @GlobalTheory.QuotBaseChange.isPullback_spMap_quot | exact GlobalTheory.QuotBaseChange.isPullback_spMap_quot | (intros; apply GlobalTheory.QuotBaseChange.isPullback_spMap_quot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoprodDescOfSmoothPieces

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

theorem smooth_desc_of_isColimit : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  intro S S₁ S₂ X₁ X₂ u₁ u₂ ⟨hc⟩ x₁ x₂ h₁ h₂
  let e := Limits.IsColimit.coconePointUniqueUpToIso (Limits.coprodIsCoprod S₁ S₂) hc
  have e₁ : Limits.coprod.inl ≫ e.hom = u₁ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.left⟩
  have e₂ : Limits.coprod.inr ≫ e.hom = u₂ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.right⟩
  have i₁ : IsOpenImmersion (Limits.coprod.inl : S₁ ⟶ S₁ ⨿ S₂) := inferInstance
  have i₂ : IsOpenImmersion (Limits.coprod.inr : S₂ ⟶ S₁ ⨿ S₂) := inferInstance
  have : IsIso e.hom := Iso.isIso_hom e
  have ie : IsOpenImmersion e.hom := inferInstance
  have o₁ : IsOpenImmersion u₁ := e₁ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₁ ie)
  have o₂ : IsOpenImmersion u₂ := e₂ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₂ ie)
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (coprodOpenCover.{0, 0} X₁ X₂) ?_
  rintro (_ | _)
  · show Smooth (Limits.coprod.inl ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inl_desc]; infer_instance
  · show Smooth (Limits.coprod.inr ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inr_desc]; infer_instance

end GlobalTheory.ProdGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoprodDescOfSmoothPiecesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smooth_coprodDesc_of_smooth_pieces : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  first | exact @GlobalTheory.ProdGlue.smooth_desc_of_isColimit | exact GlobalTheory.ProdGlue.smooth_desc_of_isColimit | (intros; apply GlobalTheory.ProdGlue.smooth_desc_of_isColimit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftOfSplitRing

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLiftGlue

theorem exists_lift_of_split : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (e : R), IsIdempotentElem e → ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → (∀ f : R, (f = e ∨ f = 1 - e) → ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (B : Over (Sp (R₀ ⧸ Ideal.span {π f}))) (_ : GrpObj B) (i : B.left ⟶ A.left) (j : B.left ⟶ A₀.left) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π ∧ IsGrpPullback B A (spMap ρ) i ∧ IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) j ∧ IsAbelianScheme A) → ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  intro R R₀ _ _ I hI π hπ hk e he A₀ _ hA₀ H
  obtain ⟨A₁, gA₁, B₁, gB₁, i₁, j₁, ρ₁, hρ₁, hp₁, hq₁, hab₁⟩ := H e (Or.inl rfl)
  obtain ⟨A₂, gA₂, B₂, gB₂, i₂, j₂, ρ₂, hρ₂, hp₂, hq₂, hab₂⟩ := H (1 - e) (Or.inr rfl)
  have cS := GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents R e (1 - e) he (by ring)
  have cT := GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents R₀ (π e) (π (1 - e)) (he.map π) (by rw [← map_add (f := _)]; simp)
  obtain ⟨i, hi₁, hi₂, hpb⟩ := GlobalTheory.T.isPullback_coprodDesc_of_pieces_over_coprod _ _ cS _ _ cT (spMap π) (spMap ρ₁) (spMap ρ₂) (GlobalTheory.T.isPullback_spMap_quotient_span_baseChange R R₀ π e ρ₁ hρ₁) (GlobalTheory.T.isPullback_spMap_quotient_span_baseChange R R₀ π (1 - e) ρ₂ hρ₂)
    A₁.hom A₂.hom A₀.hom B₁.hom B₂.hom j₁ j₂ i₁ i₂ hq₁.1 hq₂.1 hp₁.1 hp₂.1
  have hsm := GlobalTheory.T.smooth_coprodDesc_of_smooth_pieces _ _ cS A₁.hom A₂.hom hab₁.smooth hab₂.smooth
  set X : Over (Sp R) := Over.mk (Limits.coprod.desc (A₁.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {e}))) (A₂.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {1 - e})))) with hX
  obtain ⟨m, hm⟩ := GlobalTheory.T.groupLaw_glue_over_coprod_base _ _ cS _ _ cT (spMap ρ₁) (spMap ρ₂) A₁ A₂ B₁ B₂ A₀ i₁ i₂ j₁ j₂ hp₁ hp₂ hq₁ hq₂ i hi₁ hi₂
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk, hI]⟩
  have hsm' : Smooth X.hom := hsm
  have hpb' : IsPullback i A₀.hom X.hom (spMap π) := hpb
  obtain ⟨e₁, he₁, he₁'⟩ := GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening R R₀ π hπ hnil X A₀ i hpb' hsm' (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left (Over.w _)
  have hw : ∀ g : A₀ ⊗ A₀ ⟶ A₀, (g.left ≫ i) ≫ X.hom = (Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π)).hom := fun g ↦ by
    simp only [Over.mk_hom, Category.assoc, hpb'.w]; rw [← Category.assoc, Over.w]
  let l : Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π) ⟶ X ⊗ X := lift (Over.homMk _ (hw (fst A₀ A₀))) (Over.homMk _ (hw (snd A₀ A₀)))
  have hl₁ : l.left ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hl₂ : l.left ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨g, hg, hab⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_smoothLift_nilpotent R R₀ π hπ hnil A₀ hA₀ X i hpb' hsm' e₁ he₁ he₁' l.left hl₁ hl₂ m (hm l.left hl₁ hl₂)
  exact ⟨X, g, i, hg, hab⟩

end GlobalTheory.AbLiftGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftOfSplitRingStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_abelianScheme_lift_of_splitRing : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (e : R), IsIdempotentElem e → ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → (∀ f : R, (f = e ∨ f = 1 - e) → ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (B : Over (Sp (R₀ ⧸ Ideal.span {π f}))) (_ : GrpObj B) (i : B.left ⟶ A.left) (j : B.left ⟶ A₀.left) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π ∧ IsGrpPullback B A (spMap ρ) i ∧ IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) j ∧ IsAbelianScheme A) → ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  first | exact @GlobalTheory.AbLiftGlue.exists_lift_of_split | exact GlobalTheory.AbLiftGlue.exists_lift_of_split | (intros; apply GlobalTheory.AbLiftGlue.exists_lift_of_split <;> assumption)
end
end
