module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNbhdSectionFibreIsPreirreducibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityComponentsSmoothGroupSchemeMulMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemConnectedComponentInFibreStatement
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitComponentMulMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponentsStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSndImageMulMemOpenGroupScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdCompOpen

theorem isOpen_snd_image : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens,
    IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  intro S G _ hG U
  have hs : Smooth (pullback.snd G.hom G.hom) := inferInstance
  have ho : UniversallyOpen (pullback.snd G.hom G.hom) := UniversallyOpen.of_flat _
  have hmap : IsOpenMap (snd G G).left := (pullback.snd G.hom G.hom).isOpenMap
  have hW : IsOpen ((fst G G).left ⁻¹' (U : Set G.left) ∩ (μ[G]).left ⁻¹' (U : Set G.left)) :=
    ((U.isOpen.preimage (fst G G).left.continuous)).inter (U.isOpen.preimage (μ[G]).left.continuous)
  convert hmap _ hW using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨w, h1, h2, h3⟩; exact ⟨w, ⟨h1, h2⟩, h3⟩
  · rintro ⟨w, ⟨h1, h2⟩, h3⟩; exact ⟨w, h1, h2, h3⟩

end GlobalTheory.IdCompOpen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSndImageMulMemOpenGroupSchemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens, IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  first | exact @GlobalTheory.IdCompOpen.isOpen_snd_image | exact GlobalTheory.IdCompOpen.isOpen_snd_image | (intros; apply GlobalTheory.IdCompOpen.isOpen_snd_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdentityComponentsOfMulInv

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem identityComponent_shear_mul {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = snd G G := by
  have h1 : lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = (fst G G)⁻¹ * (fst G G * snd G G) := by
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.inv_def]
  rw [h1, inv_mul_cancel_left]

theorem mem_identityComponents_of_mul_inv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (∀ z ∈ U, G.hom z = G.hom y → z ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hs U y hU hy
  obtain ⟨w, hf, hm, rfl⟩ := hy
  have hbf : G.hom ((fst G G).left w) = G.hom ((snd G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
  have hbm : G.hom ((μ[G]).left w) = G.hom ((snd G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
  have zf := hU _ hf hbf
  have zm := hU _ hm hbm
  have zi := GlobalTheory.T.inv_mem_identity_component_fibre S G _ zf
  set φ : G ⊗ G ⟶ G ⊗ G := lift (fst G G ≫ ι[G]) μ[G] with hφ
  have e1 : (fst G G).left (φ.left w) = (ι[G]).left ((fst G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, hφ, lift_fst]
  have e2 : (snd G G).left (φ.left w) = (μ[G]).left w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ, lift_snd]
  have key := GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem S G hs (φ.left w) (e1 ▸ zi) (e2 ▸ zm)
  have e3 : (μ[G]).left (φ.left w) = (snd G G).left w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ, identityComponent_shear_mul]
  rwa [e3] at key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdentityComponentsOfMulInvStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.mem_unitComponent_of_mul_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (∀ z ∈ U, G.hom z = G.hom y → z ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.mem_identityComponents_of_mul_inv | exact GlobalTheory.mem_identityComponents_of_mul_inv | (intros; apply GlobalTheory.mem_identityComponents_of_mul_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdCompOpen

theorem isOpen_sectionComponents_of_family (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (O : X.Opens → Set X) (hO : ∀ U, IsOpen (O U))
    (h1 : ∀ (U : X.Opens) (y : X), e (f y) ∈ U →
      y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → y ∈ O U)
    (h2 : ∀ (U : X.Opens) (y : X),
      (∀ z ∈ U, f z = f y → z ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) →
      y ∈ O U → y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  classical
  have hfe : ∀ t : S, f (e t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  refine GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces X _ (GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn X S f e hf he) ?_
  intro x hx
  obtain ⟨U, V₀, V, I, hV, hs, hU, hI, hirr⟩ := GlobalTheory.T.exists_open_nbhd_section_fiber_isPreirreducible X S f e hf he (f x)
  refine ⟨⟨O U, hO U⟩ ⊓ f ⁻¹ᵁ (V₀ ⊓ e ⁻¹ᵁ U), f ⁻¹ᵁ V, I.image (fun c => f.app V c), ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hV hy.2.1
  · exact ⟨h1 U x hU hx, hs, hU⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    rw [← Scheme.preimage_basicOpen]
    exact hI d hd
  · intro y hy hJ
    have hpre := hirr (f y) hy.2.1 (fun c hc => by
      have := hJ _ (Finset.mem_image_of_mem _ hc)
      rw [← Scheme.preimage_basicOpen] at this
      exact this)
    refine h2 U y ?_ hy.1
    intro z hz hzy
    have hsub := hpre.isPreconnected.subset_connectedComponentIn
      (x := e (f y)) (F := f ⁻¹' {f y}) ⟨hy.2.2, hfe _⟩ Set.inter_subset_right
    show z ∈ connectedComponentIn (f ⁻¹' {f z}) (e (f z))
    rw [hzy]
    exact hsub ⟨hz, hzy⟩

theorem isOpen_identityComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hG
  exact isOpen_sectionComponents_of_family G.left S G.hom (η[G]).left hG (Over.w (η[G]))
    (fun U => {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y})
    (GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme S G hG) (GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent S G hG) (GlobalTheory.T.mem_unitComponent_of_mul_mem S G hG)

end GlobalTheory.IdCompOpen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupSchemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.IdCompOpen.isOpen_identityComponent | exact GlobalTheory.IdCompOpen.isOpen_identityComponent | (intros; apply GlobalTheory.IdCompOpen.isOpen_identityComponent <;> assumption)
end
end
