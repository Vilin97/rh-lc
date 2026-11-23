module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChartStatement
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenVar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineBaseChangeOverFieldExtension

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem isAffineOpen_preimage_and_tensor_equiv_of_isPullback : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K)) (π : X' ⟶ X), IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))) → ∀ V : X.Opens, IsAffineOpen V → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; IsAffineOpen (π ⁻¹ᵁ V) ∧ ∃ e : K ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) ∧ ∀ c : K, e (c ⊗ₜ 1) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom c := by
  intro k K _ _ _ X X' f f' π h V hV
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  refine ⟨hV.preimage π, ?_⟩
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := π ⁻¹ᵁ V) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have hpo' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top)
      (CommRingCat.ofHom (algebraMap k K)) (π.app V)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  letI : Algebra K Γ(X', π ⁻¹ᵁ V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(X', π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  letI : Algebra k Γ(X', π ⁻¹ᵁ V) :=
    ((((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom).comp
      (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k Γ(X, V) Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun r => by
    exact (congrArg (fun φ => φ.hom r) hpo'.w).symm
  haveI : Algebra.IsPushout k K Γ(X, V) Γ(X', π ⁻¹ᵁ V) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo'.flip
  refine ⟨(Algebra.IsPushout.equiv k K Γ(X, V) Γ(X', π ⁻¹ᵁ V)).toRingEquiv, fun a => ?_, fun c => ?_⟩
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineBaseChangeOverFieldExtensionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

theorem _root_.GlobalTheory.T.affine_base_change_over_field_extension : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K)) (π : X' ⟶ X), IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))) → ∀ V : X.Opens, IsAffineOpen V → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; IsAffineOpen (π ⁻¹ᵁ V) ∧ ∃ e : K ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) ∧ ∀ c : K, e (c ⊗ₜ 1) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom c := by
  first | exact @GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback | exact GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback | (intros; apply GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem fromSpec_prime_comap_bot_lies_over_genericPoint :
    ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V →
      ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime),
        P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  intro X Y _ π V hV hW P hP h
  have e := IsAffineOpen.SpecMap_appLE_fromSpec π hV hW le_rfl
  have e2 : π (hW.fromSpec ⟨P, hP⟩) =
      hV.fromSpec (Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩) := by
    have := congrArg (fun f : Spec Γ(Y, π ⁻¹ᵁ V) ⟶ X => f (⟨P, hP⟩ : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V))) e
    exact this.symm
  set q : Spec Γ(X, V) := Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩ with hqdef
  have hq : q.asIdeal = ⊥ := by
    rw [← h, Scheme.Hom.app_eq_appLE]
    rfl
  have hne : Nonempty V := ⟨⟨hV.fromSpec q, hV.range_fromSpec.subset ⟨q, rfl⟩⟩⟩
  have hgen : q = genericPoint (Spec Γ(X, V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hq
  rw [e2, hgen, genericPoint_eq_of_isOpenImmersion]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime), P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  first | exact @GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | exact GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | (intros; apply GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptySubschemeOfPrimeCharts

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory.SubschemeIntegral

theorem isPreirreducible_univ_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)
    (hU : ∀ a, IsOpen (U a)) (hcov : ∀ x, ∃ a, x ∈ U a) (hirr : ∀ a, IsPreirreducible (U a))
    (hmeet : ∀ a b, (U a).Nonempty → (U b).Nonempty → (U a ∩ U b).Nonempty) :
    IsPreirreducible (Set.univ : Set X) := by
  intro u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩
  obtain ⟨a, hxa⟩ := hcov x
  obtain ⟨b, hyb⟩ := hcov y
  obtain ⟨z, hza, hzu, hzb⟩ := hirr a u (U b) hu (hU b) ⟨x, hxa, hxu⟩
    (by obtain ⟨w, h1, h2⟩ := hmeet a b ⟨x, hxa⟩ ⟨y, hyb⟩; exact ⟨w, h1, h2⟩)
  obtain ⟨w, _, hw⟩ := hirr b u v hu hv ⟨z, hzb, hzu⟩ ⟨y, hyb, hyv⟩
  exact ⟨w, trivial, hw⟩

theorem fromSpec_mem_support {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (hU : IsAffineOpen U.1) (P : PrimeSpectrum Γ(Y, U.1)) (h : I.ideal U ≤ P.asIdeal) :
    hU.fromSpec P ∈ (I.support : Set Y) := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨P, rfl⟩
  change hU.fromSpec P ∈ I.support
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  have : hU.fromSpec P ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(Y, U.1)) :=
    ⟨P, (PrimeSpectrum.mem_zeroLocus _ _).mpr h, rfl⟩
  rw [hU.fromSpec_image_zeroLocus] at this
  exact this.1

theorem exists_cover {Y : Scheme.{0}} (I : Y.IdealSheafData) {ι : Type} (W : ι → Y.affineOpens)
    (hW : ⨆ a, (W a).1 = ⊤) (x : I.subscheme) :
    ∃ a y, (I.subschemeCover.f (W a)) y = x := by
  have hx : I.subschemeι x ∈ (⨆ a, (W a).1) := by rw [hW]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  haveI := I.subschemeCover.map_prop (W a)
  have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact ha
  obtain ⟨y, hy⟩ := this
  exact ⟨a, y, hy⟩

theorem isEmpty_spec_top {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (h : I.ideal U = ⊤) : IsEmpty (Spec (I.subschemeCover.X U)) := by
  haveI : Subsingleton (Γ(Y, U) ⧸ I.ideal U) := Ideal.Quotient.subsingleton_iff.mpr h
  refine ⟨fun y => ?_⟩
  have : Subsingleton (I.subschemeCover.X U) := this
  exact y.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr (by rw [Subsingleton.elim (1 : I.subschemeCover.X U) 0]; exact zero_mem _))

theorem isIntegral_or_isEmpty_subscheme : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData) (ι : Type) (W : ι → Y.affineOpens), (⨆ a, (W a).1 = ⊤) → (∀ a, I.ideal (W a) = ⊤ ∨ (I.ideal (W a)).IsPrime) → (∀ a b (ha : (I.ideal (W a)).IsPrime), I.ideal (W b) ≠ ⊤ → (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ ∈ (W b).1) → IsIntegral I.subscheme ∨ IsEmpty I.subscheme := by
  intro Y I ι W hW hI hm
  by_cases hex : ∃ a, (I.ideal (W a)).IsPrime
  · left
    obtain ⟨a₀, ha₀⟩ := hex
    haveI hred : ∀ a, _root_.IsReduced (I.subschemeCover.X (W a)) := by
      intro a
      rcases hI a with h | h
      · haveI : Subsingleton (Γ(Y, W a) ⧸ I.ideal (W a)) := Ideal.Quotient.subsingleton_iff.mpr h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
      · haveI := h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
    let 𝒰 : I.subscheme.OpenCover := Scheme.Cover.mkOfCovers ι (fun a => Spec (I.subschemeCover.X (W a)))
      (fun a => I.subschemeCover.f (W a)) (exists_cover I W hW) (fun a => I.subschemeCover.map_prop (W a))
    haveI : ∀ a : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X a) := fun a => by
      change AlgebraicGeometry.IsReduced (Spec (I.subschemeCover.X (W a))); haveI := hred a; infer_instance
    haveI : AlgebraicGeometry.IsReduced I.subscheme := IsReduced.of_openCover I.subscheme 𝒰
    have hpt : ∀ a (ha : (I.ideal (W a)).IsPrime), ∃ x : I.subscheme,
        I.subschemeι x = (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ := by
      intro a ha
      have := fromSpec_mem_support I (W a) (W a).2 ⟨I.ideal (W a), ha⟩ le_rfl
      rw [← I.range_subschemeι] at this
      exact this
    have hrange : ∀ a (x : I.subscheme), I.subschemeι x ∈ (W a).1 → x ∈ Set.range (I.subschemeCover.f (W a)) := by
      intro a x hx
      haveI := I.subschemeCover.map_prop (W a)
      have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
        rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact hx
      exact this
    have hp : ∀ a, (Set.range (I.subschemeCover.f (W a))).Nonempty → (I.ideal (W a)).IsPrime := by
      rintro a ⟨_, y, _⟩
      rcases hI a with h | h
      · exact ((isEmpty_spec_top I (W a) h).false y).elim
      · exact h
    haveI : IrreducibleSpace I.subscheme := by
      obtain ⟨x₀, -⟩ := hpt a₀ ha₀
      have hpre : IsPreirreducible (Set.univ : Set I.subscheme) := by
        refine isPreirreducible_univ_of_cover (fun a => Set.range (I.subschemeCover.f (W a))) (fun a => ?_)
          (fun x => ?_) (fun a => ?_) (fun a b ha hb => ?_)
        · haveI := I.subschemeCover.map_prop (W a); exact (I.subschemeCover.f (W a)).isOpenEmbedding.isOpenMap.isOpen_range
        · obtain ⟨a, y, hy⟩ := exists_cover I W hW x; exact ⟨a, y, hy⟩
        · rcases hI a with h | h
          · haveI := isEmpty_spec_top I (W a) h
            rw [Set.range_eq_empty]; exact isPreirreducible_empty
          · haveI : IsDomain (I.subschemeCover.X (W a)) := by
              change IsDomain (Γ(Y, W a) ⧸ I.ideal (W a)); haveI := h; infer_instance
            rw [← Set.image_univ]
            exact ((IrreducibleSpace.isIrreducible_univ _).image _
              (I.subschemeCover.f (W a)).continuous.continuousOn).isPreirreducible
        · obtain ⟨x, hx⟩ := hpt a (hp a ha)
          refine ⟨x, hrange a x ?_, hrange b x ?_⟩
          · rw [hx, ← SetLike.mem_coe, ← (W a).2.range_fromSpec]; exact ⟨_, rfl⟩
          · rw [hx]; exact hm a b (hp a ha) (hp b hb).ne_top
      haveI : PreirreducibleSpace I.subscheme := ⟨hpre⟩
      exact { toNonempty := ⟨x₀⟩ }
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  · right
    refine ⟨fun x => ?_⟩
    obtain ⟨a, y, -⟩ := exists_cover I W hW x
    have h : I.ideal (W a) = ⊤ := (hI a).resolve_right (fun h => hex ⟨a, h⟩)
    exact (isEmpty_spec_top I (W a) h).false y

end GlobalTheory.SubschemeIntegral
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptySubschemeOfPrimeChartsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isIntegral_or_isEmpty_subscheme_of_prime_charts : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData) (ι : Type) (W : ι → Y.affineOpens), (⨆ a, (W a).1 = ⊤) → (∀ a, I.ideal (W a) = ⊤ ∨ (I.ideal (W a)).IsPrime) → (∀ a b (ha : (I.ideal (W a)).IsPrime), I.ideal (W b) ≠ ⊤ → (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ ∈ (W b).1) → IsIntegral I.subscheme ∨ IsEmpty I.subscheme := by
  first | exact @GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme | exact GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme | (intros; apply GlobalTheory.SubschemeIntegral.isIntegral_or_isEmpty_subscheme <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptyGenericMemberLinearSystem

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory

theorem GenericMember.isIntegral_or_isEmpty_zeroScheme : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → ∀ (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec), ⨆ i, nonzeroLocus (b i) = ⊤ → ∃ t : (L.pull π).Sec, t ≠ 0 ∧ (IsIntegral (secIdeal (LB.isLB_pull hL π) t).subscheme ∨ IsEmpty (secIdeal (LB.isLB_pull hL π) t).subscheme) := by
  intro k _ N X X' _ _ f f' π hP L hL b hb

  have loc : ∀ x : X, ∃ (V : X.Opens) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N),
      IsAffineOpen V ∧ x ∈ V ∧ IsUnit (resG X hVc ((b j).f c)) := by
    intro x
    have hx : x ∈ (⨆ i, nonzeroLocus (b i)) := hb.ge (Set.mem_univ x)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 hj
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hc
    have hVc : V ≤ L.U c := hVle.trans (X.basicOpen_le _)
    refine ⟨V, c, hVc, j, hVa, hxV, ?_⟩
    have h1 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((b j).f c)
    have h2 := h1.map (X.presheaf.map (homOfLE hVle).op).hom
    convert h2 using 1
    simp only [resG]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  choose V c hVc j hVa hxV hu using loc
  have hW : ∀ x, IsAffineOpen (π ⁻¹ᵁ V x) := fun x => (GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)).1
  have key : ∀ x, (genSec k N f' π L b).f (fun _ => c x) ≠ 0 ∧
      ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩ = ⊤ ∨
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).IsPrime ∧
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).comap
          (π.app (V x)).hom = ⊥) := fun x => by
    obtain ⟨-, e, he1, he2⟩ := GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)
    exact GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart k N X X' f f' π L hL b (V x) ⟨x, hxV x⟩ (hW x) (c x) (hVc x) (j x) (hu x) e he1 he2
  refine ⟨genSec k N f' π L b, fun h0 => ?_, ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact (key x).1 (by rw [h0]; rfl)
  · refine GlobalTheory.T.isIntegral_or_isEmpty_subscheme_of_prime_charts X' _ X (fun x => ⟨π ⁻¹ᵁ V x, hW x⟩) ?_ (fun x => ?_) (fun x y hx hy => ?_)
    · refine eq_top_iff.2 fun z _ => Opens.mem_iSup.2 ⟨π z, hxV (π z)⟩
    · rcases (key x).2 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    · rcases (key x).2 with h | h
      · exact absurd h hx.ne_top
      · have hg := GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint X X' π (V x) (hVa x) (hW x) _ hx h.2
        show π _ ∈ V y
        rw [hg]
        exact (genericPoint_spec X).mem_open_set_iff (V y).isOpen |>.2 ⟨y, trivial, hxV y⟩

end GlobalTheory
end
end
