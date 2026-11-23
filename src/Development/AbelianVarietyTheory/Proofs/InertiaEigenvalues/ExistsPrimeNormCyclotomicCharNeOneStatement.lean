module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Frobenius
public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.NumberTheory.Cyclotomic.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardPrimesOverEqFinrankOfTrivialFrobenius

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem natCard_le_of_forall_pow_eq_self (F : Type*) [CommRing F] [IsDomain F] [Finite F]
    (q : ℕ) (hq : 1 < q) (h : ∀ x : F, x ^ q = x) : Nat.card F ≤ q := by
  classical
  haveI := Fintype.ofFinite F
  have hne : (X ^ q - X : F[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
    rw [natDegree_X_pow, natDegree_X] at h1
    omega
  have hdeg : (X ^ q - X : F[X]).natDegree ≤ q := by
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_X_pow, natDegree_X]
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans ?_ hdeg
  refine Polynomial.card_le_degree_of_subset_roots ?_
  intro x _
  rw [mem_roots hne]
  simp [h x]

theorem exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
        (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) →
        (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧
          ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ _
  have hD : differentIdeal (𝓞 K) (𝓞 M) ≠ ⊥ := differentIdeal_ne_bot
  refine ⟨(fun P : HeightOneSpectrum (𝓞 M) => P.under (𝓞 K)) ''
    {P | P.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}, (Ideal.finite_factors hD).image _, ?_⟩
  intro v hv hx
  haveI := v.isPrime
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  have hf : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.inertiaDeg (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    have hle : Nat.card (𝓞 M ⧸ P) ≤ Ideal.absNorm v.asIdeal := by
      refine natCard_le_of_forall_pow_eq_self _ _ hq fun y => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, Ideal.Quotient.eq]
      exact hx P hP x
    have hN : Ideal.absNorm P = Nat.card (𝓞 M ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal P
    rw [← hN, ← h] at hle
    have hpos : 0 < P.inertiaDeg (𝓞 K) := P.inertiaDeg_pos (𝓞 K)
    have h2 : P.inertiaDeg (𝓞 K) ≤ 1 := by
      rw [← Nat.pow_le_pow_iff_right hq, pow_one]; exact hle
    omega
  have he : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.ramificationIdx (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    have hn : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 M) := by
      intro hd
      refine hv ⟨⟨P, hP.1, hP0⟩, hd, ?_⟩
      ext1
      exact (Ideal.over_def P v.asIdeal).symm
    haveI : Algebra.IsUnramifiedAt (𝓞 K) P := not_dvd_differentIdeal_iff.1 hn
    exact Ideal.ramificationIdx_eq_one P (𝓞 K)
  refine ⟨?_, fun P hP => ?_⟩
  · obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
    haveI := P.2.1
    haveI := P.2.2
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M)
      Gal(M/K)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.1 Gal(M/K),
      Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.1 Gal(M/K), he P.1 P.2, hf P.1 P.2,
      IsGalois.card_aut_eq_finrank] at h
    simpa using h
  · haveI := hP.1
    haveI := hP.2
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P, hf P hP, pow_one]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardPrimesOverEqFinrankOfTrivialFrobeniusStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) → (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧ ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem | exact GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem | (intros; apply GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotForallExistsTwoLiesOverAbsNormEq

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ S hS h
  choose P P' hne hP hP' hNP hNP' using h
  have key : ∀ {Q : HeightOneSpectrum (𝓞 M)} {v w : HeightOneSpectrum (𝓞 K)},
      Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.LiesOver w.asIdeal → v = w :=
    fun h₁ h₂ => HeightOneSpectrum.ext (h₁.over.trans h₂.over.symm)
  let f : {v // v ∉ S} × Bool → HeightOneSpectrum (𝓞 M) :=
    fun x => if x.2 then P x.1 x.1.2 else P' x.1 x.1.2
  have lies : ∀ x, (f x).asIdeal.LiesOver x.1.1.asIdeal := by
    rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hP' v hv, hP v hv]
  refine _root_.GlobalTheory.Mem.ZetaPole.not_injective_double_primes K M S hS f ?_ ?_
  · rintro ⟨⟨v, hv⟩, b⟩ ⟨⟨w, hw⟩, c⟩ hfe
    have hvw : v = w := key (lies (⟨v, hv⟩, b)) (by rw [hfe]; exact lies _)
    subst hvw
    cases b <;> cases c
    · rfl
    · exact absurd hfe.symm (hne v hv)
    · exact absurd hfe (hne v hv)
    · rfl
  · rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hNP' v hv, hNP v hv]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotForallExistsTwoLiesOverAbsNormEqStatement

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem _root_.GlobalTheory.T.not_forall_exists_two_degree_one_primes_over : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  exact @GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeNormCyclotomicCharNeOne

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.NormChar

theorem split_trivial (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M,
      x ^ Ideal.absNorm v.asIdeal - x ∈ P) : Module.finrank K M = 1 := by
  by_contra h1
  have h2 : 1 < Module.finrank K M := by have := Module.finrank_pos (R := K) (M := M); omega
  obtain ⟨T, hT, hc⟩ := GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius K M
  refine GlobalTheory.T.not_forall_exists_two_degree_one_primes_over K M (S ∪ T) (hS.union hT) fun v hv => ?_
  simp only [Set.mem_union, not_or] at hv
  obtain ⟨hn, hN⟩ := hc v hv.2 (h v hv.1)
  rw [← hn] at h2
  have := v.isMaximal
  obtain ⟨P, P', hP, hP', hne⟩ := (Set.one_lt_ncard_iff (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M))).1 h2
  have := hP.2
  have := hP'.2
  exact ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ⟨P', hP'.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P'⟩,
    fun e => hne (congrArg HeightOneSpectrum.asIdeal e), hP.2, hP'.2, hN P hP, hN P' hP'⟩


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.NormChar.smulComm (K L : Type) [Field K] [Field L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := by
  refine ⟨fun σ a x => ?_⟩
  apply RingOfIntegers.ext
  have h1 : ((a • x : 𝓞 L) : L) = algebraMap K L a * x := by
    rw [Algebra.smul_def]; rfl
  have h3 : ((σ • (a • x) : 𝓞 L) : L) = σ ((a • x : 𝓞 L) : L) := rfl
  rw [h3, h1, Algebra.smul_def]
  push_cast
  rw [map_mul, AlgEquiv.commutes]
  rfl

attribute [local instance] smulComm

theorem eq_top_of_frob (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
      ∀ σ : L ≃ₐ[K] L, IsArithFrobAt (𝓞 K) σ Q → σ ∈ H) : H = ⊤ := by
  set M := IntermediateField.fixedField H with hM
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have h1 : Module.finrank K M = 1 := by
    refine split_trivial K M S hS fun v hv P hP x => ?_
    have := hP.1
    have := hP.2
    obtain ⟨Q, hQ, hQ'⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 L)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) Q
    have hH := h v hv Q hQ hQv σ hσ
    have h5 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
      rw [← hQv.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h6 := hσ (algebraMap (𝓞 M) (𝓞 L) x)
    rw [h5] at h6
    have h7 : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) σ) (algebraMap (𝓞 M) (𝓞 L) x) = algebraMap (𝓞 M) (𝓞 L) x := by
      apply RingOfIntegers.ext
      exact (x : M).2 ⟨σ, hH⟩
    rw [h7] at h6
    rw [hQ'.over, Ideal.mem_comap, map_sub, map_pow, ← neg_mem_iff, neg_sub]
    exact h6
  have h2 : M = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  rw [← IntermediateField.fixingSubgroup_fixedField H, ← hM, h2, IntermediateField.fixingSubgroup_bot]

theorem exists_prime_norm_char_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by
  intro K _ _ m hm hirr χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero m := ⟨hm.ne_zero⟩
  let L := CyclotomicField m K
  have : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  let e := IsCyclotomicExtension.autEquivPow L hirr
  have hz := IsCyclotomicExtension.zeta_spec m K L
  have hm0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hH := eq_top_of_frob K L (χ.comp e.toMonoidHom).ker {v | v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}}
    (Ideal.finite_factors hm0) (fun v hv Q hQ hQv σ hσ => by
      have hζ := hz.toInteger_isPrimitiveRoot
      have hmQ : (m : 𝓞 L) ∉ Q := by
        intro hmQ
        apply hv
        rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton, hQv.over, Ideal.mem_comap, map_natCast]
        exact hmQ
      have h3 := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hζ.pow_eq_one hmQ
      have h5 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
        rw [← hQv.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h5] at h3
      have h4 : σ (IsCyclotomicExtension.zeta m K L) =
          IsCyclotomicExtension.zeta m K L ^ Ideal.absNorm v.asIdeal := by
        have := congrArg (fun y : 𝓞 L => (y : L)) h3
        exact this
      have h6 := hz.autToPow_spec K σ
      rw [h4] at h6
      have h7 : ((hz.autToPow K σ : (ZMod m)ˣ) : ZMod m).val ≡ Ideal.absNorm v.asIdeal [MOD m] := by
        have := (hz.isOfFinOrder hm.ne_zero).pow_eq_pow_iff_modEq.1 h6
        rwa [← hz.eq_orderOf] at this
      refine hcon v (e σ) ?_
      rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h7, ZMod.natCast_zmod_val]
      rfl)
  apply hχ
  ext1 u
  have : e.symm u ∈ (χ.comp e.toMonoidHom).ker := hH ▸ Subgroup.mem_top _
  simpa using this

end GlobalTheory.NormChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeNormCyclotomicCharNeOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem _root_.GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by
  exact @GlobalTheory.NormChar.exists_prime_norm_char_ne_one
end
end
