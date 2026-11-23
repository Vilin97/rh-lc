module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselianStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.CechLevels
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.DescentSteps
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.EquivalenceQuasiAffine
public import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.HenselianIdempotents
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SpecAbsolutelyIntegrallyClosedCohomology
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyDescentOfCechCover

-- Source module: Development.EtaleCohomology.EtaleSheaves.CoverIntegralClosure

section

@[expose] public section

noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.CoverIntegralClosure

theorem inj_sub (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) :=
  Subtype.val_injective

theorem aic_integralClosure (P : Type) [CommRing P] [IsDomain P] :
    AIC (integralClosure P (AlgebraicClosure (FractionRing P))) := by
  apply GlobalTheory.aic_integralClosure_algebraicClosure <;> assumption

theorem inj_P (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap P (integralClosure P (AlgebraicClosure (FractionRing P)))) := by
  have h : Function.Injective (algebraMap P (AlgebraicClosure (FractionRing P))) := by
    rw [IsScalarTower.algebraMap_eq P (FractionRing P) (AlgebraicClosure (FractionRing P))]
    exact (algebraMap (FractionRing P) _).injective.comp (IsFractionRing.injective P _)
  rw [IsScalarTower.algebraMap_eq P (integralClosure P (AlgebraicClosure (FractionRing P)))
    (AlgebraicClosure (FractionRing P))] at h
  exact fun x y hxy => h (by simp only [RingHom.comp_apply, hxy])

theorem Cover_of : LateralTheory.E.t_E1Cut.Cover := by
  intro A _
  let π : MvPolynomial A ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) id
  have hπ : Function.Surjective π := fun a => ⟨MvPolynomial.X a, by simp [π]⟩
  let T := integralClosure (MvPolynomial A ℤ) (AlgebraicClosure (FractionRing (MvPolynomial A ℤ)))
  let I : Ideal T := (RingHom.ker π).map (algebraMap (MvPolynomial A ℤ) T)
  let ψ : MvPolynomial A ℤ ⧸ RingHom.ker π →+* T ⧸ I :=
    Ideal.quotientMap I (algebraMap (MvPolynomial A ℤ) T) Ideal.le_comap_map
  let φ : A →+* T ⧸ I := ψ.comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hcomp : φ.comp π = (Ideal.Quotient.mk I).comp (algebraMap (MvPolynomial A ℤ) T) := by
    apply RingHom.ext
    intro x
    simp [φ, ψ, Ideal.quotientMap_mk]
  refine ⟨T ⧸ I, inferInstance, φ, ?_, ?_, ?_⟩
  · apply RingHom.IsIntegral.tower_top π φ
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x)
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  · intro p
    have : (Ideal.comap π p.asIdeal).IsPrime := Ideal.comap_isPrime π p.asIdeal
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := T)
      (Ideal.comap π p.asIdeal) (⊥ : Ideal T) (by
        rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (inj_P _)]
        exact bot_le)
    rw [Ideal.under_def] at hQc
    have hIQ : I ≤ Q := by
      apply Ideal.map_le_iff_le_comap.2
      rw [hQc]
      intro x hx
      simp [RingHom.mem_ker.1 hx]
    have hQ' : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨⟨Q.map (Ideal.Quotient.mk I), hQ'⟩, ?_⟩
    ext1
    apply Ideal.comap_injective_of_surjective π hπ
    simp only [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hIQ, hQc]
  · exact ⟨T, inferInstance, inferInstance, Ideal.Quotient.mk I, aic_integralClosure _,
      Ideal.Quotient.mk_surjective⟩

end LateralTheory.E.CoverIntegralClosure
end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.EtaleCovers

section

@[expose] public section

namespace UpperTheory.Et.EtaleCovers

theorem a0 : LateralTheory.E.t_E1Cut.Cover := LateralTheory.E.CoverIntegralClosure.Cover_of

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.Cover := a0

end UpperTheory.Et.EtaleCovers
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AffineProperBaseChange

section

@[expose] public section

namespace UpperTheory.Et

theorem affine_proper_base_change : GlobalTheory.EtC.E1 :=
  UpperTheory.etaleCohomology_descent_of_cech_cover GlobalTheory.T.quasiIso_hypercohomology_bijective GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf GlobalTheory.T.integralSurjection_cechDescent_tateTwist EtaleCovers.intersectionNumber_baseChange HenselianIdempotents.intersectionNumber_baseChange QuasiAffineEquivalence.intersectionNumber_baseChange EtaleDescentEtaleAxioms.intersectionNumber_baseChange CechLevelsEtaleAxioms.intersectionNumber_baseChange

theorem proper_base_change : GlobalTheory.EtC.E2 :=
  E2.main ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover, GlobalTheory.T.etaleCohomology_coefficient_longExactSequence, GlobalTheory.T.etaleCohomology_coefficientRing_invariance, GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero, GlobalTheory.T.etaleCohomology_bijective_of_support_bijective, GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity, GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf, GlobalTheory.T.etC_b3, GlobalTheory.T.integralSurjection_cechDescent_tateTwist, GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic, affine_proper_base_change⟩

end UpperTheory.Et
end
end
