module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsFiniteType
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescendsFg

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegelDataDescent

theorem exists_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) :
    ∃ φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  exact ⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_w {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : Geo.Tor.IsSquare φ φ₂) :
    φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  rw [← w₁, reassoc_of% h₁, w, reassoc_of% v₁]

theorem isSquare_comp {S'' S' S : Scheme.{0}} {A'' : Over S''} {A' : Over S'} {A : Over S}
    {ψ : A''.left ⟶ A'.left} {φ : A'.left ⟶ A.left} {χ : A''.left ⟶ A.left} (e : ψ ≫ φ = χ)
    {ψ₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    {χ₂ : (A'' ⊗ A'').left ⟶ (A ⊗ A).left} (hψ : Geo.Tor.IsSquare ψ ψ₂) (hφ : Geo.Tor.IsSquare φ φ₂)
    (hχ : Geo.Tor.IsSquare χ χ₂) : ψ₂ ≫ φ₂ = χ₂ := by
  have a₁ := hψ.1
  have a₂ := hψ.2
  apply pullback.hom_ext
  · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]
  · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]

theorem isPullback_of_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hA : IsPullback φ A'.hom A.hom f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A' ⊗ A').hom (A ⊗ A).hom f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have w₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨isSquare_w hA.w h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst A A).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd A A).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

end GlobalTheory.SiegelDataDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSubringModelAbelianLineBundle

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

noncomputable section

namespace GlobalTheory.SiegApproxModel

open GlobalTheory.SiegelDataDescent

theorem model_exists : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (F : Finset R), IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P₀ : LB (G2 B).left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) := by
  intro R _ A _ _ F hA P hP
  classical
  obtain ⟨S₀, B₀, _, φ₀, hF, hft₀, hab₀, hpb₀⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring_anyDim R A F hA
  have := hab₀.comm
  have := hab₀.smooth
  have := hab₀.proper
  have := hab₀.geomConnected
  obtain ⟨φ₂₀, hsq₀⟩ := exists_isSquare hpb₀.1.w
  have hpb₂₀ := isPullback_of_isSquare hpb₀.1 hsq₀
  have : IsProper (B₀ ⊗ B₀).hom := by
    change IsProper (pullback.fst B₀.hom B₀.hom ≫ B₀.hom)
    infer_instance
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ (A ⊗ A).left (B₀ ⊗ B₀).left
    (A ⊗ A).hom (B₀ ⊗ B₀).hom φ₂₀ P hpb₂₀ hP
  obtain ⟨R₁, h, hT, hft⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S₀ SP hft₀
  let t : Sp R₁ ⟶ Sp S₀ := spMap (Subring.inclusion h)
  have e : spMap R₁.subtype ≫ t = spMap S₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let A₁ : Over (Sp R₁) := (Over.pullback t).obj B₀
  have hab₁ : IsAbelianScheme A₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd B₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd B₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd B₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst B₀.hom t) A₁.hom B₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ₀ ≫ B₀.hom = (A.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, e]; exact hpb₀.1.w
  let φ : A.left ⟶ A₁.left := pullback.lift φ₀ (A.hom ≫ spMap R₁.subtype) wφ
  have hφ₁ : φ ≫ pullback.fst B₀.hom t = φ₀ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ A₁.hom = A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hφ : IsGrpPullback A A₁ (spMap R₁.subtype) φ :=
    (isGrpPullback_pullback B₀ t).cancel (hpb₀.congr e.symm hφ₁.symm) hφ₂
  obtain ⟨φ₂₁, hsq₁⟩ := exists_isSquare (A' := A₁) (A := B₀) (φ := pullback.fst B₀.hom t) hpb₁.w
  obtain ⟨φ₂, hsq⟩ := exists_isSquare hφ.1.w
  obtain ⟨P₁, hP₁, hiso⟩ := hSP R₁ h hT
    (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom φ₂₁ φ₂ (isPullback_of_isSquare hpb₁ hsq₁)
    (isSquare_comp hφ₁ hsq hsq₁ hsq₀) (isSquare_w hφ.1.w hsq)
  exact ⟨R₁, A₁, inferInstance, inferInstance, φ, φ₂, P₁, fun x hx => h (hF hx), hft, hab₁, hφ, hsq, hP₁, hiso⟩

end GlobalTheory.SiegApproxModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSubringModelAbelianLineBundleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison


theorem _root_.GlobalTheory.T.exists_finiteType_subring_model_abelian_lineBundle : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (F : Finset R), IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P₀ : LB (G2 B).left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) := by
  first | exact @GlobalTheory.SiegApproxModel.model_exists | exact GlobalTheory.SiegApproxModel.model_exists | (intros; apply GlobalTheory.SiegApproxModel.model_exists <;> assumption)
end
end
