module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqOfIsUnitFinrank

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep


open Module in
theorem comap_map_eq_of_isUnit_finrank : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing V'] [IsDomain V'] [Algebra V V'] [Module.Finite V V'], Function.Injective (algebraMap V V') → IsUnit ((Module.finrank V V' : ℕ) : V) → ∀ I : Ideal V, (I.map (algebraMap V V')).comap (algebraMap V V') = I := by
  intro V V' _ _ _ _ _ _ _ hinj hunit I
  refine le_antisymm ?_ Ideal.le_comap_map
  let K := FractionRing V
  let L := FractionRing V'
  have hinjL : Function.Injective (algebraMap V L) := by
    rw [IsScalarTower.algebraMap_eq V V' L]
    exact (IsFractionRing.injective V' L).comp hinj
  haveI : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr hinjL
  letI : Algebra K L := FractionRing.liftAlgebra V L
  haveI : IsScalarTower V K L := FractionRing.isScalarTower_liftAlgebra V L
  have hrank : finrank K L = finrank V V' := IsFractionRing.finrank_eq V K V' L
  have hn0 : finrank K L ≠ 0 := by
    intro h
    rw [← hrank, h, Nat.cast_zero] at hunit
    exact not_isUnit_zero hunit
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hn0)
  haveI : Module.Free K L := Module.Free.of_divisionRing K L
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'

  have htrV : ∀ z : V', ∃ t : V, algebraMap V K t = Algebra.trace K L (algebraMap V' L z) := by
    intro z
    have hz : IsIntegral V (algebraMap V' L z) :=
      (Algebra.IsIntegral.isIntegral (R := V) z).map (IsScalarTower.toAlgHom V V' L)
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hz)
  have hmul : ∀ (i : V) (w : L), Algebra.trace K L (algebraMap V L i * w) =
      algebraMap V K i * Algebra.trace K L w := by
    intro i w
    rw [IsScalarTower.algebraMap_apply V K L, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have key : ∀ y ∈ I.map (algebraMap V V'), ∀ z : V', ∃ c ∈ I,
      algebraMap V K c = Algebra.trace K L (algebraMap V' L (z * y)) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩ z
      obtain ⟨t, ht⟩ := htrV z
      refine ⟨i * t, I.mul_mem_right t hi, ?_⟩
      rw [map_mul, ht, mul_comm z, map_mul, ← IsScalarTower.algebraMap_apply V V' L, hmul]
    · intro z
      exact ⟨0, I.zero_mem, by simp⟩
    · intro x y _ _ hx hy z
      obtain ⟨c, hc, hcx⟩ := hx z
      obtain ⟨d, hd, hdy⟩ := hy z
      exact ⟨c + d, I.add_mem hc hd, by rw [map_add (f := _), hcx, hdy, mul_add, map_add (f := _), map_add (f := _)]⟩
    · intro w x _ hx z
      obtain ⟨c, hc, hcx⟩ := hx (z * w)
      exact ⟨c, hc, by rw [hcx, smul_eq_mul, _root_.mul_assoc]⟩
  intro a ha
  obtain ⟨c, hc, hca⟩ := key _ ha 1
  rw [_root_.one_mul, ← IsScalarTower.algebraMap_apply V V' L, IsScalarTower.algebraMap_apply V K L,
    Algebra.trace_algebraMap, hrank, nsmul_eq_mul, ← map_natCast (algebraMap V K), ← map_mul] at hca
  have hc' : c = (finrank V V' : V) * a := IsFractionRing.injective V K hca
  obtain ⟨u, hu⟩ := hunit
  have : a = ↑u⁻¹ * c := by rw [hc', ← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [this]
  exact I.mul_mem_left _ hc

end GlobalTheory.Poinc.Sep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegree

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory.LocExt

theorem exists_isCN_integralClosure_of_isUnit_finrank : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.TorRef.IsCN V → ∀ (K' : Type) [Field K'] [Algebra (FractionRing V) K'] [FiniteDimensional (FractionRing V) K'], IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (j : V' →+* K'), GlobalTheory.TorRef.IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ Function.Injective j ∧ j.comp io = (algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V)) ∧ ∀ x : K', (∃ P : Polynomial V, P.Monic ∧ P.eval₂ ((algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V))) x = 0) → ∃ y, j y = x := by
  intro V _ _ _ hV K' _ _ _ hunit
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hV
  let K := FractionRing V
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := integralClosure V K'
  haveI hWf : Module.Finite V W := IsIntegralClosure.finite V K K' W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
  have hVL : Function.Injective (algebraMap V K') :=
    (algebraMap K K').injective.comp (IsFractionRing.injective V K)
  have hinjW : Function.Injective (algebraMap V W) := fun x y h => hVL (congrArg Subtype.val h)
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have h1 : (maximalIdeal W).comap (algebraMap V W) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal W))
  have hlocW : IsLocalHom (algebraMap V W) := ((local_hom_tfae _).out 1 5).2 h1
  haveI : IsFractionRing W K' := IsIntegralClosure.isFractionRing_of_finite_extension V K K' W
  have hrank : Module.finrank V W = Module.finrank K K' := (IsFractionRing.finrank_eq V K W K').symm
  have hunit' : IsUnit ((Module.finrank V W : ℕ) : V) := by rw [hrank]; exact hunit
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, (integralClosure V K').val.toRingHom,
    ⟨IsNoetherianRing.of_finite V W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      CompleteFiniteExtension.isAdicComplete_of_finite_local V W, inferInstance⟩, hinjW,
    RingHom.finite_algebraMap.2 hWf, hlocW,
    GlobalTheory.Poinc.Sep.comap_map_eq_of_isUnit_finrank V W hinjW hunit',
    Subtype.val_injective, RingHom.ext fun _ => rfl, ?_⟩
  rintro x ⟨P, hmon, hP⟩
  exact ⟨⟨x, P, hmon, hP⟩, rfl⟩

end GlobalTheory.LocExt
end
end
