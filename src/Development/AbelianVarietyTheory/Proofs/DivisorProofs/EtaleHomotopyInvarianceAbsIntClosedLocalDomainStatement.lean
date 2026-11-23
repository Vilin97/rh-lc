module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistAcyclicSpectrumPolynomialOfIsAlgClosed

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem acyc_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K],
    IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  intro q _ K _ _ hq n i hn
  have hqA : IsUnit (q : Polynomial K) := by
    simpa using hq.map (Polynomial.C : K →+* Polynomial K)
  by_cases h2 : 2 ≤ n
  · exact GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (Polynomial K) hq n i h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hζ : ∃ ζ : Polynomial K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
      have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
        rw [Polynomial.degree_cyclotomic]
        have := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
        exact_mod_cast this.ne'
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
      refine ⟨Polynomial.C z, ?_⟩
      have hz' : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
        exact hz
      have hC : Polynomial.C z = algebraMap K (Polynomial K) z := rfl
      rw [hC, Polynomial.aeval_algebraMap_apply, hz', map_zero]
    obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (Polynomial K) hqA hζ 1 i 1
    have hs : Subsingleton (Ht q (sp (Polynomial K)) 1 1) := by
      refine GlobalTheory.T.kummer_etale_vanishing q (Polynomial K) hqA ?_ ?_
      · intro u
        obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
        obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq r (Nat.pos_of_ne_zero (NeZero.ne q))
        have hv0 : v ≠ 0 := by
          rintro rfl
          rw [zero_pow (NeZero.ne q)] at hv
          exact hr.ne_zero hv.symm
        refine ⟨Units.map (Polynomial.C : K →+* Polynomial K).toMonoidHom (Units.mk0 v hv0), ?_⟩
        ext
        simp [← hru, ← hv]
      · intro c _
        exact Subsingleton.elim _ _
    exact e.toEquiv.subsingleton

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistAcyclicSpectrumPolynomialOfIsAlgClosedStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  first | (exact @GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (exact GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (intros; apply GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsIntClosedLocalDomain

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.HtpyLine

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem pull_bijective_of_ringEquiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  have h2 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h1, pull_id]
  · rw [← pull_comp, h2, pull_id]

theorem bijective_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (f : M →+ N) : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end GlobalTheory.EtC.HtpyLine

namespace GlobalTheory.EtC.HtpyLine

open Polynomial

theorem exists_cyclotomic_root_of_AIC (q : ℕ) [NeZero q] (T : Type) [CommRing T] [Nontrivial T] (hA : AIC T) :
    ∃ ζ : T, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨a, ha⟩ := hA (cyclotomic q T) (cyclotomic.monic q T)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
  refine ⟨a, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact ha

theorem htpy_AIC : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  intro q _ T _ _ _ hA hq i n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hneg : ∀ E : Spc, Subsingleton (H (ZMod q) E (tw q i) n) := by
      intro E
      have hz : ∀ α : CochainComplex.HomComplex.Cochain ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n, α = 0 := by
        intro α
        apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 α 0
        intro p s h U x
        have hs : s < 0 := by omega
        haveI := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q i) U).2.2.2 s hs)
        exact Subsingleton.elim _ _
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := a.mk_surjective
      obtain ⟨b, rfl⟩ := b.mk_surjective
      have : a = b := CochainComplex.HomComplex.Cocycle.ext (by rw [hz a.1, hz b.1])
      rw [this]
    haveI := hneg (sp T)
    haveI := hneg (sp (Polynomial T))
    exact bijective_of_subsingleton _
  · exact GlobalTheory.T.h_zero_pullback_twist_bijective q T (Polynomial T) Polynomial.C hq (exists_cyclotomic_root_of_AIC q T hA) inferInstance
      (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) i
  · haveI hT : Subsingleton (Ht q (sp T) n i) := GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic q T hA hq n i hn
    haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
    have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
    haveI hKt : Subsingleton (Ht q (sp (Polynomial (FractionRing T))) n i) := GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed q (FractionRing T) hqK n i hn
    let e : TensorProduct T (FractionRing T) (Polynomial T) ≃+* Polynomial (FractionRing T) :=
      (polyEquivTensor T (FractionRing T)).symm.toRingEquiv
    haveI hTens : Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) (Polynomial T))) n i) :=
      (pull_bijective_of_ringEquiv e (tw q i) n).1.subsingleton
    have hC3 := GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq (Polynomial T) i n
    haveI : Subsingleton (Ht q (sp (Polynomial T)) n i) := hC3.1.subsingleton
    exact bijective_of_subsingleton _

end GlobalTheory.EtC.HtpyLine
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsIntClosedLocalDomainStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  first | (exact @GlobalTheory.EtC.HtpyLine.htpy_AIC) | (exact GlobalTheory.EtC.HtpyLine.htpy_AIC) | (intros; apply GlobalTheory.EtC.HtpyLine.htpy_AIC  <;> assumption)
end
end
