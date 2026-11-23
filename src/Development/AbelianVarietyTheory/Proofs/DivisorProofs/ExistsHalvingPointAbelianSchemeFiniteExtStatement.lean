module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHomStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjective
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjectiveStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor


theorem _root_.GlobalTheory.T.semiAbelian_mul_nat_surjective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ m : ℕ, m ≠ 0 → Surjective ((𝟙 G) ^ m : G ⟶ G).left := by
  first | exact @GlobalTheory.SemiAbSurj.surjective_pow | exact GlobalTheory.SemiAbSurj.surjective_pow | (intros; apply GlobalTheory.SemiAbSurj.surjective_pow <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianSchemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFinite_and_flat_mul_abelianScheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 A) ^ k : A ⟶ A).left ∧ Flat ((𝟙 A) ^ k : A ⟶ A).left := by
  first | exact @GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul | exact GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul | (intros; apply GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalvingPointAbelianSchemeFiniteExt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfPt

theorem exists_spec_of_finite_surjective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsFinite f] [Surjective f] :
    ∃ (C : Type) (_ : CommRing C) (φ : R →+* C) (g : Sp C ⟶ X),
      Function.Injective φ ∧ φ.Finite ∧ g ≫ f = spMap φ := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f)
  have hψ : Spec.map ψ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, X.isoSpec.inv, ?_, ?_, ?_⟩
  · have hs : Surjective (Spec.map ψ) := by rw [hψ]; infer_instance
    have hd : DenseRange (PrimeSpectrum.comap ψ.hom) := hs.1.denseRange
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, nilradical_eq_zero] at hd
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    simpa using hd hx
  · have hf : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (IsFinite.SpecMap_iff ψ).1 hf
  · exact hψ.symm

end GlobalTheory.HalfPt

namespace GlobalTheory.HalfPt

theorem exists_half_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (a : 𝟙_ (Over (Sp R)) ⟶ B), IsCN R → IsAbelianScheme B → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (b : Over.mk (spMap ρ) ⟶ B), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ b ^ 2 = toUnit _ ≫ a := by
  intro R _ _ _ B _ _ a hCN hAb
  haveI : IsNoetherianRing R := hCN.1
  obtain ⟨hfin, -⟩ := GlobalTheory.T.isFinite_and_flat_mul_abelianScheme (Sp R) B hAb 2 (by norm_num)
  have hsurj := GlobalTheory.T.semiAbelian_mul_nat_surjective (Sp R) B (GlobalTheory.isSemiAbelian_of_isAbelianScheme B hAb) 2 two_ne_zero
  let m : B.left ⟶ B.left := ((𝟙 B) ^ 2 : B ⟶ B).left
  let s : Sp R ⟶ B.left := a.left
  haveI : IsFinite m := hfin
  haveI : Surjective m := hsurj
  haveI : IsFinite (pullback.snd m s) := inferInstance
  haveI : Surjective (pullback.snd m s) := inferInstance
  obtain ⟨C, _, φ, g, hinj, hφf, hg⟩ := exists_spec_of_finite_surjective (pullback.snd m s)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρi, hρf, hρl, hσ⟩ := GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R C φ hCN hinj hφf
  have hsB : s ≫ B.hom = 𝟙 (Sp R) := Over.w a
  have hmB : m ≫ B.hom = B.hom := Over.w ((𝟙 B) ^ 2 : B ⟶ B)
  have hfst : pullback.fst m s ≫ B.hom = pullback.snd m s := by
    rw [← hmB, ← Category.assoc, pullback.condition, Category.assoc, hsB, Category.comp_id]
  have hρ : spMap σ ≫ spMap φ = spMap ρ := by
    rw [← hσ, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let c : Over.mk (spMap ρ) ⟶ B :=
    Over.homMk (spMap σ ≫ g ≫ pullback.fst m s) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hfst, hg, hρ])
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, c, hCN', hρi, hρf, hρl, ?_⟩
  have hc : c ^ 2 = c ≫ (𝟙 B) ^ 2 := by rw [comp_pow, Category.comp_id]
  rw [hc]
  ext
  simp only [c, Over.comp_left, Over.homMk_left, Category.assoc]
  show spMap σ ≫ g ≫ pullback.fst m s ≫ m = _
  rw [pullback.condition, ← Category.assoc g, hg, ← Category.assoc, hρ]
  rfl

end GlobalTheory.HalfPt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalvingPointAbelianSchemeFiniteExtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_halving_point_abelianScheme_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (a : 𝟙_ (Over (Sp R)) ⟶ B), IsCN R → IsAbelianScheme B → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (b : Over.mk (spMap ρ) ⟶ B), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ b ^ 2 = toUnit _ ≫ a := by
  first | exact @GlobalTheory.HalfPt.exists_half_point | exact GlobalTheory.HalfPt.exists_half_point | (intros; apply GlobalTheory.HalfPt.exists_half_point <;> assumption)
end
end
