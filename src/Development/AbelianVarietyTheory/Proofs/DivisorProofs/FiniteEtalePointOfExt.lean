module

import Mathlib
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableExtensionMultiplesOfSemistable
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointOfFiniteEtaleOverAlgClosed
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianEndomorphismSpreadSpecialise
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointOfFiniteEtaleOverAlgClosedStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_base_point_of_finite_etale_over_algClosed : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀), IsFinite p → Etale p → ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) → ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := by
  first | exact @GlobalTheory.FinEtPoints.exists_point_of_finite_etale | exact GlobalTheory.FinEtPoints.exists_point_of_finite_etale | (intros; apply GlobalTheory.FinEtPoints.exists_point_of_finite_etale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianEndomorphismSpreadSpecialiseStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_abelian_endomorphism_spread_specialise : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B, IsMonHom f → ∃ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ ∧ IsMonHom f₀ ∧ GlobalTheory.Spread.bcMap B.hom R.val ≫ Ψ.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ ∧ σ ≫ pullback.fst _ _ = 𝟙 _ ∧ σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom ∧ f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.Spread.exists_endo_spread_specialise | exact GlobalTheory.Spread.exists_endo_spread_specialise | (intros; apply GlobalTheory.Spread.exists_endo_spread_specialise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadEndomorphismTorsionSectionEqSpecialisation

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsCmp

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B]
    (x : 𝟙_ (Over S') ⟶ (Over.pullback f).obj B) (x₀ : 𝟙_ (Over S) ⟶ B)
    (hx : f ≫ x₀.left = x.left ≫ pullback.fst B.hom f) (N : ℕ) (h : x₀ ^ N = 1) : x ^ N = 1 := by
  have e : ∀ k, f ≫ (x₀ ^ k).left = (x ^ k).left ≫ pullback.fst B.hom f := fun k =>
    GlobalTheory.ZH.MultInt.pow_left_pullback f B (T := 𝟙_ (Over S')) (T₀ := 𝟙_ (Over S)) f
      (by simp) x x₀ hx k
  have e0 := e 0
  have eN := e N
  rw [h, ← pow_zero x₀, e0] at eN
  rw [← pow_zero x]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact eN.symm
  · exact (Over.w (x ^ N)).trans (Over.w (x ^ 0)).symm

end GlobalTheory.TorsCmp


open GlobalTheory.TorsCmp in
theorem GlobalTheory.TorsCmp.torsion_section_eq : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ → IsMonHom f₀ → σ ≫ pullback.fst _ _ = 𝟙 _ → σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom → f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ → ∀ (N : ℕ), (N : k₀) ≠ 0 → ∀ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 → ∀ c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)), c ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left → c ≫ pullback.snd _ _ = 𝟙 _ → c ≫ Ψ.left ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left := by
  intro k₀ K _ _ _ _ B _ hB R g Ψ f₀ σ hΨ hf₀ hσ₁ hσ₂ hf N hN y₀ hy₀ c hc₁ hc₂
  haveI := hΨ
  haveI := hf₀
  haveI : IsAbelianScheme ((Over.pullback (spMap (algebraMap k₀ R))).obj B) :=
    by
      have := hB.comm
      have := hB.smooth
      have := hB.proper
      have := hB.geomConnected
      exact
        { comm := Functor.isCommMonObj_obj
          smooth := by change Smooth (pullback.snd B.hom _); infer_instance
          proper := by change IsProper (pullback.snd B.hom _); infer_instance
          geomConnected := by change GeometricallyConnected (pullback.snd B.hom _); infer_instance }
  have hgf : spMap g.toRingHom ≫ spMap (algebraMap k₀ R) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : g.toRingHom.comp (algebraMap k₀ R) = RingHom.id k₀ := by
      ext r; exact g.commutes r
    rw [this]; exact Spec.map_id _
  have hNR : IsUnit (N : Γ(Sp R, ⊤)) := by
    have h1 : IsUnit (N : k₀) := Ne.isUnit hN
    have h2 : IsUnit (N : R) := by simpa using h1.map (algebraMap k₀ R)
    simpa using h2.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let cc : 𝟙_ (Over (Sp R)) ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B :=
    Over.homMk c (by exact hc₂)
  let bb : 𝟙_ (Over (Sp R)) ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B :=
    Over.homMk (pullback.lift (spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left) (𝟙 _) (by
      rw [Category.assoc, Category.assoc, Over.w f₀, Over.w y₀, Category.id_comp]; rfl))
      (pullback.lift_snd _ _ _)
  have hcc : cc ^ N = 1 := pow_eq_one_of_pullback _ B cc y₀ hc₁.symm N hy₀
  have ha : (cc ≫ Ψ) ^ N = 1 := by rw [← MonObj.pow_comp, hcc, MonObj.one_comp]
  have hb : bb ^ N = 1 := by
    refine pow_eq_one_of_pullback _ B bb (y₀ ≫ f₀) (pullback.lift_fst _ _ _).symm N ?_
    rw [← MonObj.pow_comp, hy₀, MonObj.one_comp]
  have hxc : spMap g.toRingHom ≫ c = y₀.left ≫ σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc₁, reassoc_of% hgf, Category.assoc, hσ₁, Category.comp_id]
    · rw [Category.assoc, hc₂, Category.assoc, hσ₂, ← Category.assoc, Over.w y₀]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hpt : spMap g.toRingHom ≫ (cc ≫ Ψ).left = spMap g.toRingHom ≫ bb.left := by
    apply pullback.hom_ext
    · change spMap g.toRingHom ≫ c ≫ Ψ.left ≫ _ = spMap g.toRingHom ≫ pullback.lift _ _ _ ≫ _
      rw [reassoc_of% hxc, ← hf, pullback.lift_fst, reassoc_of% hgf]
    · rw [Category.assoc, Category.assoc]
      exact congrArg _ ((Over.w (cc ≫ Ψ)).trans (Over.w bb).symm)
  have hab := GlobalTheory.HkFam.ListedSubgroup.section_eq _ hNR ha hb (spMap g.toRingHom) hpt
  have := congrArg (fun z => z.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ R))) hab
  simp only [cc, bb, Over.comp_left, Over.homMk_left, Category.assoc] at this
  simpa only [pullback.lift_fst] using this
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadEndomorphismTorsionSectionEqSpecialisationStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.spread_endomorphism_torsion_section_eq_specialisation : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ → IsMonHom f₀ → σ ≫ pullback.fst _ _ = 𝟙 _ → σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom → f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ → ∀ (N : ℕ), (N : k₀) ≠ 0 → ∀ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 → ∀ c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)), c ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left → c ≫ pullback.snd _ _ = 𝟙 _ → c ≫ Ψ.left ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left := by
  first | exact @GlobalTheory.TorsCmp.torsion_section_eq | exact GlobalTheory.TorsCmp.torsion_section_eq | (intros; apply GlobalTheory.TorsCmp.torsion_section_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.AlgClosedDescent

theorem finiteEtale_point_of_ext : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀), IsFinite p → Etale p → ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) → ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := GlobalTheory.T.exists_base_point_of_finite_etale_over_algClosed

theorem exists_spread_specialise : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B, IsMonHom f → ∃ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ ∧ IsMonHom f₀ ∧ GlobalTheory.Spread.bcMap B.hom R.val ≫ Ψ.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ ∧ σ ≫ pullback.fst _ _ = 𝟙 _ ∧ σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom ∧ f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ := GlobalTheory.T.exists_abelian_endomorphism_spread_specialise

theorem torsion_section_comp_eq : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ → IsMonHom f₀ → σ ≫ pullback.fst _ _ = 𝟙 _ → σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom → f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ → ∀ (N : ℕ), (N : k₀) ≠ 0 → ∀ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 → ∀ c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)), c ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left → c ≫ pullback.snd _ _ = 𝟙 _ → c ≫ Ψ.left ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left := GlobalTheory.T.spread_endomorphism_torsion_section_eq_specialisation

variable {k₀ K : Type} [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K]

theorem isUnit_natCast_gamma {k : Type} [Field k] {N : ℕ} (hN : (N : k) ≠ 0) :
    IsUnit (N : Γ(Sp k, ⊤)) := by
  have h : IsUnit (N : k) := hN.isUnit
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem torsion_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B) (N : ℕ)
    (hN : (N : k₀) ≠ 0) {t : Sp K ⟶ Sp k₀} (ht : t = spMap (algebraMap k₀ K))
    (u : Over.mk t ⟶ B) (hu : u ^ N = 1) :
    ∃ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 ∧ u.left = t ≫ y₀.left := by
  subst ht
  haveI : IsAbelianScheme B := hB
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion B (isUnit_natCast_gamma hN)
  obtain ⟨x, hx, -⟩ := LatticeTorsion.existsUnique_torsion B N u hu
  obtain ⟨x₀, hx₀, hjx⟩ := finiteEtale_point_of_ext k₀ K _ (torsion B N).hom hfin het x.left (Over.w x)
  let y₀' : 𝟙_ (Over (Sp k₀)) ⟶ torsion B N := Over.homMk x₀ hx₀
  refine ⟨y₀' ≫ torsion.ι B N, ?_, ?_⟩
  · rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
  · rw [← hx, Over.comp_left, ← hjx, Over.comp_left, Category.assoc]
    rfl

theorem hom_eq_of_lTorsion {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A : Over (Sp Ω)} [GrpObj A]
    (hA : IsAbelianScheme A) (F₁ F₂ : A ⟶ A) [IsMonHom F₁] [IsMonHom F₂] {l : ℕ} (hl : l.Prime)
    (hlk : (l : Ω) ≠ 0)
    (h : ∀ (y : 𝟙_ (Over (Sp Ω)) ⟶ A) (a : ℕ), y ^ (l ^ a) = 1 → y ≫ F₁ = y ≫ F₂) : F₁ = F₂ := by
  have := hA.comm
  have hS := isSemiAbelian_of_isAbelianScheme A hA
  have hm : IsMonHom (F₁ * F₂⁻¹) :=
    { one_hom := by
        rw [MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel,
          one_eq_one]
      mul_hom := by
        have e (z : A ⊗ A ⟶ A) : z ≫ (F₁ * F₂⁻¹) = z ≫ F₁ * (z ≫ F₂)⁻¹ := by
          rw [MonObj.comp_mul, GrpObj.comp_inv]
        rw [mul_eq_mul, e, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul,
          tensorHom_fst, tensorHom_snd, e, e, mul_inv, _root_.mul_mul_mul_comm] }
  have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one Ω A A hS hS l hl hlk (F₁ * F₂⁻¹) hm
    (fun _ _ y a hy ↦ by
      rw [MonObj.comp_mul, GrpObj.comp_inv]
      exact mul_inv_eq_one.mpr (h y a hy))
  exact mul_inv_eq_one.mp h1

theorem exists_prime_ne_zero (k : Type) [Field k] : ∃ l : ℕ, l.Prime ∧ (l : k) ≠ 0 := by
  obtain ⟨p, hp⟩ := CharP.exists k
  by_cases h2 : p = 2
  · subst h2
    refine ⟨3, Nat.prime_three, fun h3 ↦ ?_⟩
    have := (CharP.cast_eq_zero_iff k 2 3).mp (by exact_mod_cast h3)
    omega
  · refine ⟨2, Nat.prime_two, fun h3 ↦ ?_⟩
    have h4 := (CharP.cast_eq_zero_iff k p 2).mp (by exact_mod_cast h3)
    rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
    · exact CharP.char_ne_one k p h5
    · exact h2 h5

theorem endo_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B)
    (f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶
      (Over.pullback (spMap (algebraMap k₀ K))).obj B) (hf : IsMonHom f) :
    ∃! f₀ : B ⟶ B, IsMonHom f₀ ∧ (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
  obtain ⟨R, g, Ψ, f₀, σ, hΨ, hf₀, hbc, hσ₁, hσ₂, hf₀σ⟩ := exists_spread_specialise k₀ K B hB f hf
  have key : (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
    let Ω := AlgebraicClosure K
    let qΩ : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
    letI : Algebra k₀ Ω := ((algebraMap K Ω).comp (algebraMap k₀ K)).toAlgebra
    have hιj : qΩ ≫ spMap (algebraMap k₀ K) = spMap (algebraMap k₀ Ω) := by
      simp only [qΩ, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      try rfl
    haveI := hf₀
    haveI := hΨ
    apply ActDescent.pullback_map_injective qΩ
    have hBK := isAbelianScheme_pullback_obj (spMap (algebraMap k₀ K)) B hB
    have hA := isAbelianScheme_pullback_obj qΩ _ hBK
    obtain ⟨l, hl, hlk⟩ := exists_prime_ne_zero k₀
    have hlΩ : (l : Ω) ≠ 0 := by
      intro h
      apply hlk
      apply (algebraMap k₀ Ω).injective
      rw [map_natCast, h, map_zero]
    refine hom_eq_of_lTorsion hA _ _ hl hlΩ fun y a hy => ?_
    have h₁ := isGrpPullback_pullback B (spMap (algebraMap k₀ K))
    have h₂ := isGrpPullback_pullback ((Over.pullback (spMap (algebraMap k₀ K))).obj B) qΩ
    have h₁₂ := h₂.comp h₁
    let u := pushHom h₁₂ (𝟙_ _) y
    have hu : u ^ (l ^ a) = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨y₀, hy₀, huy⟩ := torsion_descent (K := Ω) B hB (l ^ a)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlk)
      (t := (𝟙_ (Over (Sp Ω))).hom ≫ qΩ ≫ spMap (algebraMap k₀ K))
      (by rw [hιj]; exact Category.id_comp _) u hu
    have hu' : y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left := by
      have e : u.left = y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) := rfl
      rw [← e, huy]
      simp
    have hy0 : y₀.left ≫ B.hom = 𝟙 _ := Over.w y₀
    let w : Sp K ⟶ pullback B.hom (spMap (algebraMap k₀ K)) :=
      pullback.lift (spMap (algebraMap k₀ K) ≫ y₀.left) (𝟙 _)
        (by rw [Category.assoc, hy0]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
    have e2 : y.left ≫ pullback.snd (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ = 𝟙 _ := Over.w y
    have hv : y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = qΩ ≫ w := by
      apply pullback.hom_ext
      · rw [Category.assoc, hu', Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.comp_id]
        have e1 : pullback.fst (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ ≫
            pullback.snd B.hom (spMap (algebraMap k₀ K)) =
            pullback.snd (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ ≫ qΩ := pullback.condition
        erw [e1]
        rw [← Category.assoc, e2, Category.id_comp]
    let c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)) :=
      pullback.lift (spMap (algebraMap k₀ R) ≫ y₀.left) (𝟙 _)
        (by rw [Category.assoc, hy0]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
    have hwc : w ≫ Spread.bcMap B.hom R.val = spMap R.val.toRingHom ≫ c := by
      apply pullback.hom_ext
      · rw [Category.assoc, Spread.bcMap_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst,
          ← Category.assoc, Spread.spMap_algHom_comp]
      · rw [Category.assoc, Spread.bcMap_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have hC := torsion_section_comp_eq k₀ K B hB R g Ψ f₀ σ hΨ hf₀ hσ₁ hσ₂ hf₀σ (l ^ a)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlk) y₀ hy₀ c (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    have m1 : ((Over.pullback qΩ).map ((Over.pullback (spMap (algebraMap k₀ K))).map f₀)).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ ((Over.pullback (spMap (algebraMap k₀ K))).map f₀).left :=
      ActDescent.pullback_map_left_fst _
    have m3 : ((Over.pullback (spMap (algebraMap k₀ K))).map f₀).left ≫
        pullback.fst B.hom (spMap (algebraMap k₀ K)) = pullback.fst B.hom (spMap (algebraMap k₀ K)) ≫ f₀.left :=
      ActDescent.pullback_map_left_fst _
    have m4 : ((Over.pullback qΩ).map f).left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ f.left :=
      ActDescent.pullback_map_left_fst _
    have hL : y.left ≫ ((Over.pullback qΩ).map ((Over.pullback (spMap (algebraMap k₀ K))).map f₀)).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left ≫ f₀.left := by
      rw [reassoc_of% m1, m3, reassoc_of% hu']
    have hR : y.left ≫ ((Over.pullback qΩ).map f).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left ≫ f₀.left := by
      rw [reassoc_of% m4, ← hbc]
      erw [reassoc_of% hv]
      rw [reassoc_of% hwc, hC, ← Spread.spMap_algHom_comp R.val]
      simp only [Category.assoc]
    apply Over.OverMorphism.ext
    apply h₁₂.1.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      exact hL.trans hR.symm
    · simp only [Over.comp_left, Category.assoc, Over.w]

  exact ⟨f₀, ⟨hf₀, key⟩, fun f₁ hf₁ =>
    ActDescent.pullback_map_injective (spMap (algebraMap k₀ K)) B B (hf₁.2.trans key.symm)⟩

theorem point_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ)
    (hn : (n : k₀) ≠ 0) (y : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B)
    (z₀ : 𝟙_ (Over (Sp k₀)) ⟶ B)
    (hz : (y ^ n).left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ z₀.left) :
    ∃! y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ n = z₀ ∧
      y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ y₀.left := by
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have hnu := isUnit_natCast_gamma hn
  have := GrpTangent.isFinite_mulN B hnu
  have := GrpTangent.etale_mulN B hnu
  have h₁ := isGrpPullback_pullback B (spMap (algebraMap k₀ K))
  have hw : (y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K))) ≫ (mulN B n).left =
      spMap (algebraMap k₀ K) ≫ z₀.left := by
    have e1 : (pushHom h₁ (𝟙_ _) y ≫ mulN B n) = pushHom h₁ (𝟙_ _) (y ^ n) := by
      rw [GrpTangent.comp_mulN, map_pow]
    have e2 := congrArg (fun z => z.left) e1
    simp only [Over.comp_left] at e2
    exact e2.trans hz
  let x : Sp K ⟶ pullback (mulN B n).left z₀.left :=
    pullback.lift (y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K))) (spMap (algebraMap k₀ K)) hw
  obtain ⟨x₀, hx₀, hjx⟩ := finiteEtale_point_of_ext k₀ K _ (pullback.snd (mulN B n).left z₀.left) inferInstance inferInstance x
    (pullback.lift_snd _ _ _)
  have hz0 : z₀.left ≫ B.hom = 𝟙 _ := Over.w z₀
  have hfB : pullback.fst (mulN B n).left z₀.left ≫ B.hom = pullback.snd (mulN B n).left z₀.left := by
    rw [← Over.w (mulN B n), ← Category.assoc, pullback.condition, Category.assoc, hz0, Category.comp_id]
  let y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B := Over.homMk (x₀ ≫ pullback.fst _ _)
    (by rw [Category.assoc, hfB, hx₀]; rfl)
  have hepi : Epi (spMap (algebraMap k₀ K)) := Flat.epi_of_flat_of_surjective _
  have hy₀ : y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ y₀.left := by
    change _ = spMap (algebraMap k₀ K) ≫ x₀ ≫ pullback.fst _ _
    rw [← Category.assoc, hjx, pullback.lift_fst]
  refine ⟨y₀, ⟨?_, hy₀⟩, fun y₁ hy₁ => ?_⟩
  · rw [← GrpTangent.comp_mulN]
    apply Over.OverMorphism.ext
    change (x₀ ≫ pullback.fst _ _) ≫ (mulN B n).left = z₀.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx₀, Category.id_comp]
  · apply Over.OverMorphism.ext
    rw [← cancel_epi (spMap (algebraMap k₀ K)), ← hy₁.2, hy₀]

end GlobalTheory.AlgClosedDescent
end
end
end
