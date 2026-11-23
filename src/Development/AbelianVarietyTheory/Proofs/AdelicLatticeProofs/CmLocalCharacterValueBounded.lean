module

public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmExtensionAdelesStandardModelDictionaryStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdeleIdemPrimeCriterion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmConjugationOnPrimesProperties
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeIdempotentCMField

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.PrimeIdemExists

theorem exists_indicator (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ a : FiniteAdeleRing (𝓞 K) K, a v = 1 ∧ ∀ w, w ≠ v → a w = 0 := by
  refine ⟨(⟨fun w => if w = v then 1 else 0, ?_⟩ :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite), ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun w => ?_
    beta_reduce
    by_cases h : w = v
    · rw [if_pos h]; exact one_mem (w.adicCompletionIntegers K)
    · rw [if_neg h]; exact zero_mem (w.adicCompletionIntegers K)
  · exact if_pos rfl
  · intro w hw; exact if_neg hw

theorem cA_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ε : AF F) :
    cA σ (algebraMap (AF F) (AE F E) ε) = algebraMap (AF F) (AE F E) ε := by
  change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (ε ⊗ₜ[F] (1 : E)) = ε ⊗ₜ[F] (1 : E)
  simp

theorem cA_incA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : E) :
    cA σ (incA F E x) = incA F E (σ x) := by
  change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] (σ x)
  simp

theorem prod_ext {K : Type} [Field K] [NumberField K] {M : Type} {a b : M × FiniteAdeleRing (𝓞 K) K}
    (h1 : a.1 = b.1) (h2 : ∀ P, a.2 P = b.2 P) : a = b :=
  Prod.ext h1 (DFunLike.ext _ _ h2)

theorem exists_isPrimeIdem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  intro F E _ _ _ _ _ σ hσ P
  obtain ⟨c, hcc, -, hcmem, hcund, -, hcint, -⟩ := GlobalTheory.cmConjugation_on_primes_adeles_idempotents F E σ hσ
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, -, -⟩ := GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ
  have crit := GlobalTheory.adele_idem_prime_criterion F E Φ hΦ1 hΦ2 hΦ3
  obtain ⟨α, hα1, hα0⟩ := exists_indicator F (P.under (𝓞 F))
  have hε : IsPlaceIdem F (P.under (𝓞 F)) (pairA F 0 α) := ⟨α, rfl, hα1, hα0⟩
  set ε := pairA F 0 α with hεdef
  set η := algebraMap (AF F) (AE F E) ε with hη
  obtain ⟨hη1, hη2⟩ := hΦ3 _ _ hε
  rw [← hη] at hη1 hη2
  have hη3 : ∀ Q, (Φ η).2 Q = if Q = P ∨ Q = c P then 1 else 0 := by
    intro Q
    rw [hη2 Q]
    exact if_congr (eq_comm.trans (hcund P Q)) rfl rfl
  have mulap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a * b).2 Q = a.2 Q * b.2 Q :=
    fun _ _ _ => rfl
  have addap : ∀ (a b : mixedSpace E × FiniteAdeleRing (𝓞 E) E) Q, (a + b).2 Q = a.2 Q + b.2 Q :=
    fun _ _ _ => rfl
  by_cases hP : c P = P
  · have hηη : η * η = η := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, hη1, mul_zero]
      · rw [mulap, hη3]; split_ifs <;> simp
    refine ⟨η, η, Or.inr ⟨rfl, ⟨_, ε, hε, rfl⟩, ?_⟩⟩
    refine (crit η P _ ε hε hηη hηη).2 ⟨hη1, ?_, fun Q hQ => ?_⟩
    · rw [hη3, if_pos (Or.inl rfl)]
    · rw [hη3, if_neg]
      rw [hP]; simpa using hQ
  · obtain ⟨β, hβ1, hβ0⟩ := exists_indicator E P
    set e : AE F E := Φ.symm (0, β) with he
    have hΦe : Φ e = (0, β) := Φ.apply_symm_apply _
    have he1 : (Φ e).1 = 0 := by rw [hΦe]
    have heP : (Φ e).2 P = 1 := by rw [hΦe]; exact hβ1
    have he0 : ∀ Q, Q ≠ P → (Φ e).2 Q = 0 := by rw [hΦe]; exact hβ0
    have hee : e * e = e := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, mul_zero]
      · rw [mulap]
        by_cases hQ : Q = P
        · subst hQ; rw [heP, mul_one]
        · rw [he0 Q hQ, mul_zero]
    have heη : e * η = e := by
      apply Φ.injective
      rw [map_mul]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, zero_mul]
      · rw [mulap]
        by_cases hQ : Q = P
        · rw [hη3, if_pos (Or.inl hQ), mul_one]
        · rw [he0 Q hQ, zero_mul]
    have hcr := (crit e P _ ε hε hee heη).2 ⟨he1, heP, he0⟩
    have hσσ : ∀ x : E, σ (σ x) = x := by
      intro x
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      apply τ.injective
      rw [hσ.2.2.2, hσ.2.2.2, star_star]
    have hcr' : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ (c P).asIdeal ↔
        finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
      intro x hx
      have hint : IsIntegral ℤ (σ (x : E)) :=
        (RingOfIntegers.isIntegral_coe x).map (σ.toRingHom.toIntAlgHom)
      let y : 𝓞 E := ⟨σ (x : E), hint⟩
      have hy : (y : E) = σ (x : E) := rfl
      have hxy : (x : E) = σ (y : E) := by rw [hy, hσσ]
      have hy0 : y ≠ 0 := by
        intro h0
        apply hx
        apply RingOfIntegers.ext
        rw [hxy, h0]; simp
      rw [(hcmem P y x hxy).1, hcr y hy0, ← hcint, map_mul (cA σ), cA_incA, map_inv₀, ← hxy]
    have hee' : cA σ e * cA σ e = cA σ e := by rw [← map_mul, hee]
    have heη' : cA σ e * η = cA σ e := by
      have := congrArg (cA σ) heη
      rwa [map_mul, hη, cA_algebraMap] at this
    obtain ⟨hc1, hcP, hc0⟩ := (crit (cA σ e) (c P) _ ε hε hee' heη').1 hcr'
    refine ⟨e, e + cA σ e, Or.inl ⟨⟨⟨hee, ?_, _, ε, hε, ?_⟩, hcr⟩, rfl⟩⟩
    · apply Φ.injective
      rw [map_mul, map_zero]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_mul, he1, zero_mul]; rfl
      · rw [mulap]
        by_cases hQ : Q = P
        · rw [hc0 Q (by rw [hQ]; exact fun h => hP h.symm), mul_zero]; rfl
        · rw [he0 Q hQ, zero_mul]; rfl
    · apply Φ.injective
      rw [map_add (f := _), ← hη]
      refine prod_ext ?_ fun Q => ?_
      · rw [Prod.fst_add, he1, hc1, hη1, add_zero]
      · rw [addap, hη3]
        by_cases hQ : Q = P
        · subst hQ
          rw [heP, hc0 _ (fun h => hP h.symm), add_zero, if_pos (Or.inl rfl)]
        · by_cases hQ' : Q = c P
          · subst hQ'
            rw [he0 _ hQ, hcP, zero_add, if_pos (Or.inr rfl)]
          · rw [he0 _ hQ, hc0 _ hQ', add_zero, if_neg (by tauto)]

end GlobalTheory.PrimeIdemExists
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeIdempotentCMFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_primeIdempotent_CMField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ P : HeightOneSpectrum (𝓞 E), ∃ e f, IsPrimeIdem σ P e f := by
  first | exact @GlobalTheory.PrimeIdemExists.exists_isPrimeIdem | exact GlobalTheory.PrimeIdemExists.exists_isPrimeIdem | (intros; apply GlobalTheory.PrimeIdemExists.exists_isPrimeIdem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeIdempotentEqIndicatorPrime

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.isPrimeIdem_eq_indicator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  intro F E _ _ _ _ _ σ Φ hΦ hint hplace P e f hprime
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem at hprime
  rcases hprime with ⟨hat, -⟩ | ⟨-, ⟨v, ε, hε, rfl⟩, hcrit⟩
  · unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsIdemAt _root_.HeckeCharacterZeroLocus.ThmBIn.IsSplitIdem at hat
    obtain ⟨⟨he, hce, v, ε, hε, hsum⟩, hcrit⟩ := hat
    have heε : e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e := by
      rw [← hsum, mul_add, he, hce, add_zero]
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace e P v ε hε he heε).mp hcrit
  · obtain ⟨h0, hind⟩ := hplace v ε hε
    have he : algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε =
        algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε := by
      apply Φ.injective
      rw [map_mul]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, h0, mul_zero]
      · ext Q : 1
        change (Φ _).2 Q * (Φ _).2 Q = (Φ _).2 Q
        rw [hind Q]
        split_ifs <;> simp
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace _ P v ε hε he he).mp hcrit

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeIdempotentEqIndicatorPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.primeIdempotent_eq_indicator_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  first | exact @GlobalTheory.isPrimeIdem_eq_indicator | exact GlobalTheory.isPrimeIdem_eq_indicator | (intros; apply GlobalTheory.isPrimeIdem_eq_indicator <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmLocalCharacterValueBounded

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.HeckeUnif

theorem idem_glue_mul {R : Type*} [CommRing R] {e : R} (he : e * e = e) (a b : R) :
    (e * a + (1 - e)) * (e * b + (1 - e)) = e * (a * b) + (1 - e) := by
  linear_combination (a * b - a - b + 1) * he

theorem intValuation_of_mem_notMem_sq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : HeightOneSpectrum R) {a : R} (h1 : a ∈ P.asIdeal) (h2 : a ∉ P.asIdeal ^ 2) :
    P.intValuation a = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; simpa using h1
  have k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact h2
  have h0 : P.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero P a ha
  rw [← WithZero.exp_log h0] at k1 k2 ⊢
  rw [WithZero.exp_le_exp] at k1 k2
  congr 1
  omega

theorem unifIdele_exists_chiAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)), (∃ x, IsUnifIdele σ P x) ∧ (IsUnramAt σ χ P → ∀ x, IsUnifIdele σ P x → chiAt σ χ P = (χ x : ℂ)) ∧ ‖chiAt σ χ P‖ ≤ 1 := by
  intro F E _ _ _ _ _ σ hσ χ P
  obtain ⟨Φ, h1, h2, h3, -, -⟩ := GlobalTheory.T.cmExtension_adeles_standardModel_dictionary F E σ hσ
  have hu := GlobalTheory.T.primeIdempotent_eq_indicator_prime F E σ Φ h1 h2 h3 P
  obtain ⟨e, f, hef⟩ := GlobalTheory.T.exists_primeIdempotent_CMField F E σ hσ P
  obtain ⟨ea, eb, ec⟩ := hu e f hef
  have huniq : ∀ e' f', IsPrimeIdem σ P e' f' → e' = e := by
    intro e' f' h'
    obtain ⟨ea', eb', ec'⟩ := hu e' f' h'
    apply Φ.injective
    refine Prod.ext (by rw [ea, ea']) ?_
    ext Q
    by_cases hQ : Q = P
    · subst hQ; rw [eb, eb']
    · rw [ec Q hQ, ec' Q hQ]
  let ψ : ∀ Q : HeightOneSpectrum (𝓞 E), AE F E →+* Q.adicCompletion E := fun Q =>
    ((evalV E Q).toRingHom.comp (RingHom.snd _ _)).comp Φ.toRingHom
  have hψ : ∀ Q y, (Φ y).2 Q = ψ Q y := fun _ _ => rfl
  have he : e * e = e := by
    apply Φ.injective
    refine Prod.ext (by rw [map_mul, Prod.fst_mul, ea, mul_zero]) ?_
    ext Q
    rw [hψ, hψ, map_mul, ← hψ]
    by_cases hQ : Q = P
    · subst hQ; rw [eb, mul_one]
    · rw [ec Q hQ, mul_zero]
  have hint : ∀ c : E, P.valuation E c ≤ 1 →
      finPart F E (e * incA F E c + (1 - e)) ∈ intAE F E := by
    intro c hc
    rw [h2]
    intro Q
    rw [hψ, map_add (f := _), map_sub, map_mul, map_one, ← hψ, ← hψ]
    by_cases hQ : Q = P
    · subst hQ
      rw [eb, h1, one_mul, sub_self, add_zero]
      have : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) c) Q) = Q.valuation E c :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q c
      exact this.le.trans hc
    · rw [ec Q hQ]; simp
  have hex : ∃ x, IsUnifIdele σ P x := by
    obtain ⟨ϖ, m1, m2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
    have hϖ : (ϖ : E) ≠ 0 := by
      intro h
      have : ϖ = 0 := by exact_mod_cast h
      exact m2 (this ▸ zero_mem _)
    have hm : (e * incA F E (ϖ : E) + (1 - e)) * (e * incA F E (ϖ : E)⁻¹ + (1 - e)) = 1 := by
      rw [idem_glue_mul he, ← map_mul, mul_inv_cancel₀ hϖ, map_one]; ring
    exact ⟨⟨_, _, hm, by rw [mul_comm, hm]⟩, e, f, ϖ, hef, by simpa using m1, m2, rfl⟩
  have hq : ∀ x y : (AE F E)ˣ, IsUnifIdele σ P x → IsUnifIdele σ P y →
      ∃ c : E, P.valuation E c ≤ 1 ∧
        ((x * y⁻¹ : (AE F E)ˣ) : AE F E) = e * incA F E c + (1 - e) := by
    rintro x y ⟨e1, f1, a, p1, a1, a2, hx⟩ ⟨e2, f2, b, p2, b1, b2, hy⟩
    rw [huniq _ _ p1] at hx
    rw [huniq _ _ p2] at hy
    have hb : (b : E) ≠ 0 := by
      intro h
      have : b = 0 := by exact_mod_cast h
      exact b2 (this ▸ zero_mem _)
    refine ⟨(a : E) / (b : E), ?_, ?_⟩
    · have va : P.valuation E (a : E) = WithZero.exp (-1 : ℤ) := by
        rw [← intValuation_of_mem_notMem_sq P a1 a2]
        exact HeightOneSpectrum.valuation_of_algebraMap P a
      have vb : P.valuation E (b : E) = WithZero.exp (-1 : ℤ) := by
        rw [← intValuation_of_mem_notMem_sq P b1 b2]
        exact HeightOneSpectrum.valuation_of_algebraMap P b
      rw [map_div₀, va, vb, div_self WithZero.exp_ne_zero]
    · rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hx, hy, idem_glue_mul he, ← map_mul,
        div_mul_cancel₀ _ hb]
  refine ⟨hex, ?_, ?_⟩
  · intro hun x hx
    have hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x := ⟨hun, hex⟩
    rw [chiAt, dite_eq_left hc]
    have hy := hc.2.choose_spec
    set y := hc.2.choose
    obtain ⟨e', f', p', hχ⟩ := hun
    rw [huniq _ _ p'] at hχ
    obtain ⟨c, c1, c2⟩ := hq y x hy hx
    obtain ⟨d, d1, d2⟩ := hq x y hx hy
    have := hχ (y * x⁻¹) (by rw [c2]; linear_combination (1 - incA F E c) * he)
      (by rw [c2]; exact hint c c1)
      (by rw [mul_inv_rev, inv_inv, d2]; exact hint d d1)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    rw [this]
  · rw [chiAt]
    split_ifs
    · exact (Circle.norm_coe _).le
    · simp

end GlobalTheory.HeckeUnif
end
end
