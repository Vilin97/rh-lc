module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarRamificationIdxEqOne
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarResidueFieldIsSeparableStatement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFiniteStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Flat.TorsionFree

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarRamificationIdxEqOneStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.abhyankar_ramificationIdx_eq_one_alt : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Q.ramificationIdx D = 1 := by
  first | (exact @GlobalTheory.abhyankar_ramificationIdx_eq_one) | (exact GlobalTheory.abhyankar_ramificationIdx_eq_one) | (intros; apply GlobalTheory.abhyankar_ramificationIdx_eq_one  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootUniformiserIsDVR

section

@[expose] public section

open IsLocalRing



namespace GlobalTheory

open Polynomial

theorem adjoinRoot_uniformiser_isDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  intro R _ _ _ π e hπ he _
  set f : R[X] := X ^ e - C π with hf
  have hmon : f.Monic := monic_X_pow_sub_C π he.ne'
  have hdeg : f.natDegree = e := natDegree_X_pow_sub_C _
  haveI : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hmon).finite
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R _
  haveI : IsNoetherianRing (AdjoinRoot f) := IsNoetherianRing.of_finite R _
  set x : AdjoinRoot f := AdjoinRoot.root f with hx
  have hxe : x ^ e = algebraMap R (AdjoinRoot f) π := by
    have h0 : AdjoinRoot.mk f f = 0 := AdjoinRoot.mk_self
    rw [hf, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    exact h0
  have hinj : Function.Injective (algebraMap R (AdjoinRoot f)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (by
      rw [degree_eq_natDegree hmon.ne_zero, hdeg]; exact_mod_cast he.ne')

  have hdec : ∀ a : AdjoinRoot f, ∃ r : R, ∃ y : AdjoinRoot f, a = algebraMap R _ r + x * y := by
    intro a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    refine ⟨p.coeff 0, AdjoinRoot.mk f p.divX, ?_⟩
    conv_lhs => rw [← X_mul_divX_add p]
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, add_comm]
    rfl
  have hπm : π ∈ maximalIdeal R := (mem_maximalIdeal _).2 hπ.not_isUnit

  have hcomap : ∀ M : Ideal (AdjoinRoot f), M.IsMaximal →
      M.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R := by
    intro M hM
    letI : M.IsMaximal := hM
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap R (AdjoinRoot f))
        (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R (AdjoinRoot f))) M)
  have hxM : ∀ M : Ideal (AdjoinRoot f), M.IsMaximal → x ∈ M := by
    intro M hM
    have : algebraMap R _ π ∈ M := by
      rw [← Ideal.mem_comap, hcomap M hM]; exact hπm
    rw [← hxe] at this
    exact hM.isPrime.mem_of_pow_mem e this
  have hle : ∀ M N : Ideal (AdjoinRoot f), M.IsMaximal → N.IsMaximal → M ≤ N := by
    intro M N hM hN a ha
    obtain ⟨r, y, rfl⟩ := hdec a
    have hr : algebraMap R _ r ∈ M := by
      have := M.sub_mem ha (M.mul_mem_right y (hxM M hM))
      simpa using this
    have hr' : r ∈ maximalIdeal R := by rw [← hcomap M hM]; exact hr
    have hrN : algebraMap R _ r ∈ N := by
      rw [← Ideal.mem_comap, hcomap N hN]; exact hr'
    exact N.add_mem hrN (N.mul_mem_right y (hxM N hN))
  haveI : IsLocalRing (AdjoinRoot f) :=
    IsLocalRing.of_unique_max_ideal (by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (AdjoinRoot f)
      exact ⟨M, hM, fun N hN => le_antisymm (hle N M hN hM) (hle M N hM hN)⟩)
  have hmax : maximalIdeal (AdjoinRoot f) = Ideal.span {x} := by
    apply le_antisymm
    · intro a ha
      obtain ⟨r, y, rfl⟩ := hdec a
      have hr : algebraMap R _ r ∈ maximalIdeal (AdjoinRoot f) := by
        have := Ideal.sub_mem (maximalIdeal (AdjoinRoot f)) ha
          (Ideal.mul_mem_right y (maximalIdeal (AdjoinRoot f)) (hxM _ (maximalIdeal.isMaximal _)))
        simpa using this
      have hr' : r ∈ maximalIdeal R := by
        rw [← hcomap _ (maximalIdeal.isMaximal _)]; exact hr
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at hr'
      obtain ⟨s, rfl⟩ := hr'
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      rw [map_mul, ← hxe, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (dvd_pow_self x he.ne') _
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hxM _ (maximalIdeal.isMaximal _)
  have hx0 : x ≠ 0 := by
    intro h0
    have : algebraMap R (AdjoinRoot f) π = 0 := by rw [← hxe, h0, zero_pow he.ne']
    exact hπ.ne_zero (hinj (by rw [this, map_zero]))
  have hnf : ¬ IsField (AdjoinRoot f) := by
    intro hF
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hx0
    exact (mem_maximalIdeal x).1 (hxM _ (maximalIdeal.isMaximal _)) (IsUnit.of_mul_eq_one b hb)
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 5 1).1 (show (maximalIdeal (AdjoinRoot f)).IsPrincipal from ⟨⟨x, hmax⟩⟩)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootUniformiserIsDVRStatement

section

@[expose] public section

open IsLocalRing



theorem _root_.GlobalTheory.T.isDVR_adjoinRoot_X_pow_sub_C_of_irreducible : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  first | (exact @GlobalTheory.adjoinRoot_uniformiser_isDVR) | (exact GlobalTheory.adjoinRoot_uniformiser_isDVR) | (intros; apply GlobalTheory.adjoinRoot_uniformiser_isDVR  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootXPowSubUniformizerIsDomain

section

@[expose] public section

open IsLocalRing



namespace GlobalTheory


open Polynomial in
theorem adjoinRoot_X_pow_sub_C_uniformizer_isDomain :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ),
      Irreducible π → 0 < e → IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  intro R _ _ _ π e hπ he
  have hπp : Prime π := hπ.prime
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπp.ne_zero).2 hπp
  have hmon : (X ^ e - C π : R[X]).Monic := monic_X_pow_sub_C _ he.ne'
  have hdeg : (X ^ e - C π : R[X]).natDegree = e := natDegree_X_pow_sub_C _
  have hirr : Irreducible (X ^ e - C π : R[X]) := by
    refine Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive (by rw [hdeg]; exact he)
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro n hn
      rw [hdeg] at hn
      rw [coeff_sub, coeff_X_pow, if_neg hn.ne, zero_sub, coeff_C]
      split_ifs
      · exact neg_mem (Ideal.mem_span_singleton_self _)
      · rw [neg_zero]; exact zero_mem _
    · rw [coeff_sub, coeff_X_pow, if_neg he.ne, zero_sub, coeff_C_zero, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h1 : π * (1 + π * c) = 0 := by linear_combination -hc
      have h2 := (mul_eq_zero.1 h1).resolve_left hπp.ne_zero
      exact hπ.not_isUnit (IsUnit.of_mul_eq_one (-c) (by linear_combination -h2))
  exact AdjoinRoot.isDomain_of_prime hirr.prime

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootXPowSubUniformizerIsDomainStatement

section

@[expose] public section

open IsLocalRing



theorem _root_.GlobalTheory.T.adjoinRoot_X_pow_sub_uniformizer_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  first | (exact @GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain) | (exact GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain) | (intros; apply GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarDvrOfIsSeparable

section

@[expose] public section

open IsLocalRing



namespace GlobalTheory

theorem isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsMaximal]
    [q.LiesOver p] [Algebra.EssFiniteType R S] (h : q.ramificationIdx R = 1)
    (hs : Algebra.IsSeparable (R ⧸ p) (S ⧸ q)) :
    Algebra.IsUnramifiedAt R q := by
  rw [Ideal.ramificationIdx_eq p q, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : Algebra.IsSeparable p.ResidueField q.ResidueField := inferInstance
  exact ⟨this, h⟩

theorem abhyankar_dvr_of_isSeparable : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale D (integralClosure D (TensorProduct S D L)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he hram hsep
  obtain ⟨φ⟩ := hD
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he
    · exact h
  haveI hAd := GlobalTheory.T.adjoinRoot_X_pow_sub_uniformizer_isDomain S π e hπ he0
  haveI hAv := GlobalTheory.T.isDVR_adjoinRoot_X_pow_sub_C_of_irreducible S π e hπ he0
  haveI : IsDomain D := φ.toMulEquiv.isDomain
  haveI : IsPrincipalIdealRing D :=
    IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
  haveI : IsLocalRing D := IsLocalRing.of_surjective' φ.symm.toRingHom φ.symm.surjective
  haveI : IsDiscreteValuationRing D :=
    { not_a_field' := by
        intro h
        apply IsDiscreteValuationRing.not_isField (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π))
        refine MulEquiv.isField ?_ φ.symm.toMulEquiv
        exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 h }
  haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite
  haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv
  haveI : FaithfulSMul S D := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 : algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) a =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) b := by
      rw [← φ.commutes, ← φ.commutes, hab]
    set pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne') with hpb
    have hd : 0 < pb.dim := by
      rw [hpb, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C _]; exact he0
    have h0 : pb.basis ⟨0, hd⟩ = 1 := by rw [PowerBasis.coe_basis]; simp
    have key : ∀ s : S, pb.basis.repr (algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) s)
        ⟨0, hd⟩ = s := by
      intro s
      rw [Algebra.algebraMap_eq_smul_one, ← h0, map_smul, Module.Basis.repr_self]
      simp
    rw [← key a, ← key b, h1]
  haveI : Module.Finite D (integralClosure D (TensorProduct S D L)) := GlobalTheory.T.normalisation_dvr_tensor_separable_finite S K L D
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  haveI : Module.Flat D (integralClosure D (TensorProduct S D L)) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have hinj : Function.Injective (LinearMap.rTensor L (LinearMap.mulLeft S (a : D))) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun y z h => (mul_right_injective₀ (nonZeroDivisors.ne_zero a.2)) h)
    have hsmul : ∀ z : TensorProduct S D L,
        (a : D) • z = LinearMap.rTensor L (LinearMap.mulLeft S (a : D)) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul y l => simp [TensorProduct.smul_tmul']
      | add u v hu hv => rw [smul_add, map_add (f := _), hu, hv]
    have h1 : (a : D) • (x : TensorProduct S D L) = 0 := congrArg Subtype.val hax
    rw [hsmul, ← map_zero (LinearMap.rTensor L (LinearMap.mulLeft S (a : D)))] at h1
    simp only [Submodule.mem_bot]
    exact Subtype.ext (hinj h1)
  haveI : Algebra.FinitePresentation D (integralClosure D (TensorProduct S D L)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hmax : ∀ (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
      Algebra.IsUnramifiedAt D Q := by
    intro Q hQ
    have hQu : Q.under D = maximalIdeal D :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap D
          (integralClosure D (TensorProduct S D L)))
          (algebraMap_isIntegral_iff.mpr inferInstance) Q)
    haveI : Q.LiesOver (maximalIdeal D) := ⟨hQu.symm⟩
    exact isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable (maximalIdeal D) Q
      (GlobalTheory.T.abhyankar_ramificationIdx_eq_one_alt S K L π e D ⟨φ⟩ hπ he hram hsep Q) (GlobalTheory.T.abhyankar_residueField_isSeparable_alt S K L π e D ⟨φ⟩ hπ he hram hsep Q)
  haveI : Algebra.FormallyUnramified D (integralClosure D (TensorProduct S D L)) := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    obtain ⟨Q, hQ, hqQ⟩ := Ideal.exists_le_maximal q.1 q.2.ne_top
    haveI := hQ
    have hU := hmax Q
    have hopen := Algebra.isOpen_unramifiedLocus (R := D)
      (A := integralClosure D (TensorProduct S D L))
    exact hopen.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes q ⟨Q, hQ.isPrime⟩).mp hqQ) hU
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory
end
end
