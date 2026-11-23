module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealMapCompleteDvrEqProdLifts
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPointAffineHomSectionsRingHom

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.AffinePointLift

theorem specMap_fromSpec_appLE {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{0}}
    (g : Γ(X, U) ⟶ R) (h : ⊤ ≤ (Spec.map g ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map g ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom = g := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e0 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have e : (Spec.map g ≫ hU.fromSpec).appLE U ⊤ h = hU.fromSpec.appLE U ⊤ h0 ≫ (Spec.map g).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e, e0, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem specMap_appLE_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{0}}
    (ξ : Spec R ⟶ X) (h : ⊤ ≤ ξ ⁻¹ᵁ U) :
    Spec.map (ξ.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom) ≫ hU.fromSpec = ξ := by
  rw [Spec.map_comp, Category.assoc, hU.SpecMap_appLE_fromSpec ξ (isAffineOpen_top _), IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem exists_lift : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsAffineHom π], ∀ (U : Z.affineOpens) (V V' : Type) [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (ξ : Sp V ⟶ Z) (hξ : ⊤ ≤ ξ ⁻¹ᵁ U.1) (f : V →+* V')
    (ρ : Γ(Y, π ⁻¹ᵁ U.1) →+* V'),
    ρ.comp (π.app U.1).hom = f.comp (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom).hom →
    ∃ ψ : Sp V' ⟶ Y, ψ ≫ π = spMap f ≫ ξ ∧
      ∀ I : Y.IdealSheafData, idlAlong I ψ = (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map ρ := by
  intro Y Z π _ U V V' _ _ _ _ ξ hξ f ρ h
  have hW : IsAffineOpen (π ⁻¹ᵁ U.1) := U.2.preimage π
  let g : Γ(Y, π ⁻¹ᵁ U.1) ⟶ CommRingCat.of V' := CommRingCat.ofHom ρ
  refine ⟨Spec.map g ≫ hW.fromSpec, ?_, fun I => ?_⟩
  · have e : π.appLE U.1 (π ⁻¹ᵁ U.1) le_rfl ≫ g =
        (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom) ≫ CommRingCat.ofHom f := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact CommRingCat.hom_ext h
    rw [Category.assoc, ← U.2.SpecMap_appLE_fromSpec π hW le_rfl, ← Spec.map_comp_assoc, e, Spec.map_comp,
      Category.assoc, specMap_appLE_fromSpec U.2 ξ hξ]
  · have hle : ⊤ ≤ (Spec.map g ≫ hW.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U.1) :=
      fun q _ => hW.fromSpec_preimage_self.ge (x := Spec.map g q) trivial
    rw [GlobalTheory.TraitOrder.idlAlong_eq_map I _ ⟨π ⁻¹ᵁ U.1, hW⟩ hle]
    exact congrArg (fun k : Γ(Y, π ⁻¹ᵁ U.1) ⟶ CommRingCat.of V' => Ideal.map k.hom _)
      (specMap_fromSpec_appLE hW g hle)

end GlobalTheory.AffinePointLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPointAffineHomSectionsRingHomStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

theorem _root_.GlobalTheory.T.exists_lift_point_affineHom_sections_ringHom : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsAffineHom π], ∀ (U : Z.affineOpens) (V V' : Type) [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (ξ : Sp V ⟶ Z) (hξ : ⊤ ≤ ξ ⁻¹ᵁ U.1) (f : V →+* V')
    (ρ : Γ(Y, π ⁻¹ᵁ U.1) →+* V'),
    ρ.comp (π.app U.1).hom = f.comp (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom).hom →
    ∃ ψ : Sp V' ⟶ Y, ψ ≫ π = spMap f ≫ ξ ∧
      ∀ I : Y.IdealSheafData, idlAlong I ψ = (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map ρ := by
  first | exact @GlobalTheory.AffinePointLift.exists_lift | exact GlobalTheory.AffinePointLift.exists_lift | (intros; apply GlobalTheory.AffinePointLift.exists_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealMapCompleteDvrEqProdLiftsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

theorem _root_.GlobalTheory.T.normCoefficientIdeal_map_complete_dvr_eq_prod_lifts : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ → ∀ (J : Ideal B)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ψ : Fin (Module.finrank K L) → (B →+* V')), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ (∀ j, (ψ j).comp φ = f.comp h) ∧
      (GlobalTheory.NormSheaf.normIdeal A K L B J).map (f.comp h) = ∏ j, J.map (ψ j) := by
  first | exact @GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts | exact GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts | (intros; apply GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImage

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheaf

theorem normDescentSheaf : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z), IsFinite π → IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) →
    CharZero Γ(Y, ⊤) → ∀ I : Y.IdealSheafData, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ ξ : Sp V ⟶ Z, ξ (closedPoint V) ∈ Set.range π →
        ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
          (f : V →+* V') (ψ : Fin d → (Sp V' ⟶ Y)), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧
          IsLocalHom f ∧ (∀ j, ψ j ≫ π = spMap f ≫ ξ) ∧ (idlAlong J ξ).map f = ∏ j, idlAlong I (ψ j) := by
  intro Y Z π hπ hY hYn hYN hZN hopen hchar I
  haveI : IsAffineHom π := hπ.toIsAffineHom
  obtain ⟨K, L, _, _, _, _, hK, J, hsupp, hJ⟩ := GlobalTheory.T.exists_descended_normIdealSheaf_finite_normal Y Z π hY hYn hYN hZN hopen hchar I
  refine ⟨Module.finrank K L, J, Module.finrank_pos, hsupp, ?_⟩
  intro V _ _ _ _ hV ξ hξ
  obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens
    (show ξ (closedPoint V) ∈ (⟨Set.range π, hopen⟩ : Z.Opens) from hξ)
  have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hxU).ge
  let U' : Z.affineOpens := ⟨U, hU⟩
  obtain ⟨_, _, hA, hAc, hB, hfin, hKf, hLf, hsq, hJU⟩ := hJ U' hUW ⟨_, hxU⟩
  obtain ⟨V', _, _, _, _, f, ψ', hV', hf, hfl, hψc, hprod⟩ := GlobalTheory.T.normCoefficientIdeal_map_complete_dvr_eq_prod_lifts Γ(Z, U') Γ(Y, π ⁻¹ᵁ U) K L (π.app U).hom
    hfin hsq (I.ideal ⟨π ⁻¹ᵁ U, U'.2.preimage π⟩) V hV (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of V)).hom).hom
  choose ψ hψ hψI using fun j => GlobalTheory.T.exists_lift_point_affineHom_sections_ringHom Y Z π U' V V' ξ hle f (ψ' j) (hψc j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hfl, hψ, ?_⟩
  have hidl : idlAlong J ξ = (J.ideal U').map
      (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of V)).hom).hom := by
    have hx : ξ (closedPoint V) ∈ U := hle trivial
    unfold idlAlong
    rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map J U' _ hx, Ideal.map_map, ← CommRingCat.hom_comp,
      Scheme.germ_stalkClosedPointTo]
    congr 2
  rw [hidl, hJU, Ideal.map_map]
  simp only [hψI]
  exact hprod

end GlobalTheory.NormSheaf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImageStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

theorem _root_.GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z), IsFinite π → IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) →
    CharZero Γ(Y, ⊤) → ∀ I : Y.IdealSheafData, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ ξ : Sp V ⟶ Z, ξ (closedPoint V) ∈ Set.range π →
        ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
          (f : V →+* V') (ψ : Fin d → (Sp V' ⟶ Y)), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧
          IsLocalHom f ∧ (∀ j, ψ j ≫ π = spMap f ≫ ξ) ∧ (idlAlong J ξ).map f = ∏ j, idlAlong I (ψ j) := by
  first | exact @GlobalTheory.NormSheaf.normDescentSheaf | exact GlobalTheory.NormSheaf.normDescentSheaf | (intros; apply GlobalTheory.NormSheaf.normDescentSheaf <;> assumption)
end
end
