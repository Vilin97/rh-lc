module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctional
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyDerivativeRelationSemilinearPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCurvatureClosednessRelationsAddStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalTwoFormEqSumWedgeGlobalOneFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveH1StructureAbelianStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyDerivativeRelationPairingWellDefined

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_vf_of_frame {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (l : Glob1 F →ₗ[R] R) :
    ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T,
      (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧
      ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  apply GlobalTheory.AbCoh.exists_vectorField_of_functional <;> assumption

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem derivClass_eq : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x y' w' → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = ∑ k, l (w' k) • y' k := by
  intro R _ C _ F hF h0 x n n' y w y' w' hd hd' l
  obtain ⟨δ, hnat, hδ⟩ := exists_vf_of_frame F hF h0 l
  obtain ⟨f, g, ω, rfl, hg, hf⟩ := hd
  obtain ⟨f', g', ω', hx, hg', hf'⟩ := hd'
  obtain ⟨b, hb⟩ := H1.mk_eq_mk.1 hx
  obtain rfl : y = fun k ↦ H1.mk F (g k) := funext fun k ↦ (hg k).symm
  obtain rfl : y' = fun k ↦ H1.mk F (g' k) := funext fun k ↦ (hg' k).symm
  have e1 : ∑ k, l (w k) • H1.mk F (g k) = H1.mk F (∑ k, l (w k) • g k) := by simp [map_sum, map_smul]
  have e2 : ∑ k, l (w' k) • H1.mk F (g' k) = H1.mk F (∑ k, l (w' k) • g' k) := by simp [map_sum, map_smul]
  rw [e1, e2, H1.mk_eq_mk]
  refine ⟨fun T ↦ δ T (ω' T - ω T - D R _ (b T)), ?_⟩
  funext T T' φ
  have hbφ : d0 F b T T' φ = f'.1 T T' φ - f.1 T T' φ := congrFun (congrFun (congrFun hb T) T') φ
  have key : D R _ (f'.1 T T' φ) - D R _ (f.1 T T' φ) = D R _ (b T') - p1 F φ (D R _ (b T)) := by
    rw [← map_sub, ← hbφ, amitsur_d0_apply, map_sub, p1_D]
  rw [hf φ, hf' φ] at key
  have e := congrArg (δ T') key

  simp only [map_sub, map_add (f := _), map_sum, LinearMap.map_smul, hnat, hδ, smul_eq_mul] at e
  simp only [amitsur_d0_apply, map_sub, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.sub_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  simp only [mul_comm (algebraMap R _ _)] at e ⊢
  linear_combination e

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyDerivativeRelationPairingWellDefinedStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cohomologyDerivativeRelation_pairing_wellDefined : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x y' w' → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = ∑ k, l (w' k) • y' k := by
  first | exact @GlobalTheory.AbCoh.derivClass_eq | exact GlobalTheory.AbCoh.derivClass_eq | (intros; apply GlobalTheory.AbCoh.derivClass_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCohomologyDerivativeRelationOfFrame

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem dRel_of_frame_exists (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    HasFrame F → ∀ x : GlobalTheory.CatCoh.H1 F, ∃ (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w := by
  rintro ⟨n, ⟨fr⟩⟩ x
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F x
  let g : Fin n → Z1 F := fun i ↦ ⟨fun T T' φ ↦ fr.δ i T' (D R (F.obj T') (f.1 T T' φ)), by
    intro T T' T'' φ ψ
    simp only
    rw [Z1.comp f φ ψ, map_add (f := _), map_add (f := _), ← p1_D, fr.nat]⟩
  refine ⟨n, fun i ↦ GlobalTheory.CatCoh.H1.mk F (g i), fr.w, f, g, 0, rfl, fun _ ↦ rfl, ?_⟩
  intro T T' φ
  simp only [Pi.zero_apply, map_zero, sub_zero, add_zero]
  exact fr.sum T' _

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCohomologyDerivativeRelationOfFrameStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_cohomologyDerivativeRelation_of_frame : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → ∀ x : GlobalTheory.CatCoh.H1 F, ∃ (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w := by
  first | exact @GlobalTheory.AbCoh.dRel_of_frame_exists | exact GlobalTheory.AbCoh.dRel_of_frame_exists | (intros; apply GlobalTheory.AbCoh.dRel_of_frame_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionOfCohomologyDerivativeRelation

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_obRel_of_dRel : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w → (∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = 0) → ∃ (m : ℕ) (u v : Fin m → Glob1 F), ObRel F x u v := by
  intro R _ C _ F hF h0 x n y w hD hy
  obtain ⟨N, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl2⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 N Φ
  obtain ⟨f, g, ω, hf, hg, hfD⟩ := hD
  have hcl : ∀ i, ∃ b : C0 F, d0 F b = (∑ k, l i (w k) • g k).1 := fun i ↦ by
    refine H1.mk_eq_zero.1 ?_

    simp only [map_sum, map_smul, hg]
    exact hy (l i)
  choose b hb using hcl
  have hb' : ∀ i ⦃T T' : C⦄ (φ : T ⟶ T'),
      b i T' - mp F φ (b i T) = ∑ k, l i (w k) • (g k).1 T T' φ := fun i T T' φ ↦ by
    have := congrFun (congrFun (congrFun (hb i) T) T') φ
    rw [amitsur_d0_apply] at this
    rw [this, Submodule.coe_sum]
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  have hw : ∀ k (T : C), (w k).1 T = ∑ i, l i (w k) • (Φ.w i).1 T := fun k T ↦ by
    have := congrArg (fun v : Glob1 F ↦ v.1 T) (hl2 (w k))
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hsum : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ∑ k, (g k).1 T T' φ • (w k).1 T' =
      ∑ i, (b i T' - mp F φ (b i T)) • (Φ.w i).1 T' := fun T T' φ ↦ by
    simp only [hb', hw, Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_comm, smul_assoc]
  let ω' : A0 F := fun T ↦ ω T + ∑ i, b i T • (Φ.w i).1 T
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω' T' = p1 F φ (ω' T) + D R (F.obj T') (f.1 T T' φ) := by
    intro T T' φ
    rw [hfD φ, hsum φ]

    simp only [ω', map_add (f := _), map_sum, oneFormsMapOfFunctorMorphism_smul, ← (Φ.w _).2 φ, sub_smul, Finset.sum_sub_distrib]
    abel
  have hglob : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'),
      dOne R (F.obj T') (ω' T') = pOm F 2 φ (dOne R (F.obj T) (ω' T)) := by
    intro T T' φ
    rw [hconn φ, map_add (f := _), dOne_D, add_zero, pOm_dOne]
  obtain ⟨m, u, v, hζ⟩ := GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms R C F ⟨N, ⟨Φ⟩⟩ h0 (fun T ↦ dOne R (F.obj T) (ω' T)) hglob
  exact ⟨m, u, v, f, ω', hf, hconn, fun T ↦ congrFun hζ T⟩

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionOfCohomologyDerivativeRelationStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_connection_of_cohomologyDerivativeRelation : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w → (∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = 0) → ∃ (m : ℕ) (u v : Fin m → Glob1 F), ObRel F x u v := by
  first | exact @GlobalTheory.AbCoh.exists_obRel_of_dRel | exact GlobalTheory.AbCoh.exists_obRel_of_dRel | (intros; apply GlobalTheory.AbCoh.exists_obRel_of_dRel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionSumWedgeCurvatureAbelianScheme

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem dRel_pO {R : Type} [CommRing R] {Y A : Over (Sp R)} (f : Y ⟶ A) (x : HO1 A.hom) {n : ℕ}
    (y : Fin n → HO1 A.hom) (w : Fin n → GlobForm A.hom) (h : DRel (OAff A.hom) x y w) :
    DRel (OAff Y.hom) (pO1 f x) (fun k ↦ pO1 f (y k)) (fun k ↦ pF f (w k)) :=
  GlobalTheory.T.cohomologyDerivativeRelation_semilinearPullback R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f) x n y w h

theorem sum_dRel_eq_zero (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) (x : HO1 A.hom) {n : ℕ} (y : Fin n → HO1 A.hom)
    (w : Fin n → GlobForm A.hom) (hx : DRel (OAff A.hom) x y w) (l : GlobForm A.hom →ₗ[R] R) :
    ∑ k, l (w k) • y k = 0 := by
  obtain ⟨-, -, hA2, hs2⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  obtain ⟨hF2, hC2, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R (A ⊗ A) (g + g) hA2 hs2
  obtain ⟨hax, hafF, -⟩ := GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A
  have hprim := GlobalTheory.T.primitive_h1_structure_abelian R A g hA hs x
  set a₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  set a₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  have hμ := dRel_pO μ[A] x y w hx
  have hfst := dRel_pO (fst A A) x y w hx
  have hsnd := dRel_pO (snd A A) x y w hx
  have hsum := (GlobalTheory.T.derivativeCurvatureClosedness_relations_add R _ (OAff (A ⊗ A).hom)).1 _ _ _ _ _ _ _ _ hfst hsnd
  rw [← hprim] at hsum
  have key := GlobalTheory.T.cohomologyDerivativeRelation_pairing_wellDefined R _ (OAff (A ⊗ A).hom) hF2 hC2 _ _ _ _ _ _ _ hμ hsum (l ∘ₗ pF a₂)
  rw [Fin.sum_univ_add] at key
  simp only [LinearMap.comp_apply, Fin.append_left, Fin.append_right] at key
  have e1 : ∀ k, l (pF a₂ (pF μ[A] (w k))) = l (w k) := fun k ↦ by rw [(hafF (w k)).2.2.2.2.2]
  have e2 : ∀ k, l (pF a₂ (pF (fst A A) (w k))) = 0 := fun k ↦ by rw [(hafF (w k)).2.2.2.1, map_zero]
  have e3 : ∀ k, l (pF a₂ (pF (snd A A) (w k))) = l (w k) := fun k ↦ by rw [(hafF (w k)).2.2.2.2.1]
  simp only [e1, e2, e3, zero_smul, Finset.sum_const_zero, zero_add] at key
  have := congrArg (pO1 a₁) key

  simp only [map_sum, map_smul] at this
  have f1 : ∀ k, pO1 a₁ (pO1 μ[A] (y k)) = y k := fun k ↦ (hax (y k)).2.2.1
  have f2 : ∀ k, pO1 a₁ (pO1 (snd A A) (y k)) = 0 := fun k ↦ (hax (y k)).2.1
  simp only [f1, f2, smul_zero, Finset.sum_const_zero] at this
  exact this

theorem exists_obRel_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, ∃ (m : ℕ) (u v : Fin m → GlobForm A.hom),
      ObRel (OAff A.hom) x u v := by
  intro R _ A _ g hA hs x
  obtain ⟨hF, hC, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  obtain ⟨n, y, w, hx⟩ := GlobalTheory.T.exists_cohomologyDerivativeRelation_of_frame R _ (OAff A.hom) hF x
  exact GlobalTheory.T.exists_connection_of_cohomologyDerivativeRelation R _ (OAff A.hom) hF hC x n y w hx
    (fun l ↦ sum_dRel_eq_zero R A g hA hs x y w hx l)

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionSumWedgeCurvatureAbelianSchemeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_connection_sumWedgeCurvature_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, ∃ (m : ℕ) (u v : Fin m → GlobForm A.hom), ObRel (OAff A.hom) x u v := by
  first | exact @GlobalTheory.AbCoh.exists_obRel_abelian | exact GlobalTheory.AbCoh.exists_obRel_abelian | (intros; apply GlobalTheory.AbCoh.exists_obRel_abelian <;> assumption)
end
end
