module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AlgStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.NormCyclotomicPrimeLayerEqNrmGenerator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationComapIsEquivOfLtOneIffMemPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationKummerElementAtConjugatePrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationKummerElementEqOneOfNotOver
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.DegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsTer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.RedRoot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XJacPowNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XMulConjIMul
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XMulConjIMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XNormDiv
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmissiblePrimeNotDvdOrderOfAndNotDvdLevel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level :
    ∀ (l F r d : ℕ), F ≠ 0 → l.Prime → r.Prime → r ≡ 1 [MOD F] → ML.admitted l F r d → ¬ l ∣ orderOf (r : ZMod (F * d)) ∧ ¬ r ∣ F * d := by
  intro l F r d _ hl hr hrF hd
  obtain ⟨hsq, hq⟩ := hd
  have hone : ∀ p : ℕ, p.Prime → p ≡ 1 [MOD F] → ¬ p ∣ F := fun p hp h hpF => by
    have h1 : p ≡ 1 [MOD p] := h.of_dvd hpF
    have h2 : p ∣ 1 := (h1.dvd_iff dvd_rfl).1 dvd_rfl
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  refine ⟨?_, ?_⟩
  · set n := ∏ q ∈ d.primeFactors, orderOf (r : ZMod q) with hn
    have hln : ¬ l ∣ n := by
      intro h
      obtain ⟨q, hqm, hlq⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 h
      exact (hq q (Nat.prime_of_mem_primeFactors hqm) (Nat.dvd_of_mem_primeFactors hqm)).2.2.2 hlq
    have hcop : Nat.Coprime F d := by
      apply Nat.coprime_of_dvd
      intro k hk hkF hkd
      exact hone k hk (hq k hk hkd).2.1 hkF
    have hpos : 1 ≤ r ^ n := Nat.one_le_pow _ _ hr.pos
    have hF : r ^ n ≡ 1 [MOD F] := by simpa using hrF.pow n
    have hD : r ^ n ≡ 1 [MOD d] := by
      have h1 : ∏ q ∈ d.primeFactors, q ∣ r ^ n - 1 := by
        apply Finset.prod_primes_dvd
        · intro a ha
          exact (Nat.prime_of_mem_primeFactors ha).prime
        · intro a ha
          have h2 : (r : ZMod a) ^ n = 1 :=
            orderOf_dvd_iff_pow_eq_one.1 (Finset.dvd_prod_of_mem (fun q : ℕ => orderOf (r : ZMod q)) ha)
          have h3 : r ^ n ≡ 1 [MOD a] := by
            rw [← ZMod.natCast_eq_natCast_iff]
            simpa using h2
          exact (Nat.modEq_iff_dvd' hpos).1 h3.symm
      rw [Nat.prod_primeFactors_of_squarefree hsq] at h1
      exact ((Nat.modEq_iff_dvd' hpos).2 h1).symm
    have hFD : r ^ n ≡ 1 [MOD F * d] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hF, hD⟩
    have h4 : (r : ZMod (F * d)) ^ n = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hFD
      simpa using this
    exact fun h => hln (h.trans (orderOf_dvd_of_pow_eq_one h4))
  · intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hone r hr hrF h
    · exact (hq r hr h).2.2.1 rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.RelNormCyclotomicPrimeEqPowDvdOrderOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf :
    ∀ (N r : ℕ) [NeZero N] (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K'], r.Prime → ¬ r ∣ N → ∀ (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 K')), (r : 𝓞 K') ∈ v'.asIdeal → (∀ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 K') y ∈ v'.asIdeal ↔ y ∈ v.asIdeal) → ∃ s : ℕ, s ∣ orderOf (r : ZMod N) ∧ Ideal.relNorm (𝓞 K) v'.asIdeal = v.asIdeal ^ s := by
  intro N r _ K K' _ _ _ _ _ _ hp hN v v' hr hvv
  have : Fact r.Prime := ⟨hp⟩
  have hvp : v'.asIdeal.IsPrime := v'.isPrime
  have hm : v.asIdeal.IsMaximal := v.isMaximal
  have hm' : v'.asIdeal.IsMaximal := v'.isMaximal
  have hmax : (Ideal.span {(r : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hlo : v'.asIdeal.LiesOver (Ideal.span {(r : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hr
  have hl2 : v'.asIdeal.LiesOver v.asIdeal := ⟨by
    ext y
    rw [Ideal.under_def, Ideal.mem_comap]
    exact (hvv y).symm⟩
  have h3 := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal v'.asIdeal
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd r K' v'.asIdeal hN] at h3
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_, ?_⟩
  · rw [h3]; exact Dvd.intro_left _ rfl
  · exact Ideal.relNorm_eq_pow_of_isMaximal v'.asIdeal v.asIdeal
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XEx

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.xEx :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ) (𝔞 : Ideal (𝓞 K)), b < M → 𝔞 ≠ ⊥ → ∃ X : K, IsX M K b 𝔞 X := by
  intro M _ K _ _ _ b 𝔞 hb h𝔞
  have h𝔞0 : 𝔞 ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔞
  set S : Set (HeightOneSpectrum (𝓞 K)) := {v | v.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 K)}}
  have hM0 : Ideal.span {((M : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne M
  have hS : S.Finite := Ideal.finite_factors hM0
  obtain ⟨v, hvS, hprime, hvc⟩ := degOne K S hS (ClassGroup.mk0 ⟨𝔞, h𝔞0⟩)⁻¹
  haveI : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hprime⟩
  obtain ⟨π, hπ⟩ := (red K (Ideal.absNorm v.asIdeal) v.asIdeal).1 rfl
  have hpv := ((red K (Ideal.absNorm v.asIdeal) v.asIdeal).2 π hπ).2.2.2
  have hcop : (Ideal.absNorm v.asIdeal).Coprime M := by
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    rintro ⟨k, hk⟩
    apply hvS
    show v.asIdeal ∣ _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv
  have hζ := (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨hπζ, hdvd⟩ := redRoot (𝓞 K) _ π M _ hcop hζ
  obtain ⟨χ, hχ, -⟩ := teich (𝓞 K) _ π M ((Ideal.absNorm v.asIdeal - 1) / M) _ hζ hπζ (Nat.mul_div_cancel' hdvd)
  have hXv := xJac M K b _ π χ hcop hb hχ
  rw [hπ] at hXv
  have hv0 : v.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  have hprin : (𝔞 * v.asIdeal).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (mul_mem h𝔞0 hv0)]
    have hm : ClassGroup.mk0 ⟨𝔞 * v.asIdeal, mul_mem h𝔞0 hv0⟩ =
        ClassGroup.mk0 ⟨𝔞, h𝔞0⟩ * ClassGroup.mk0 ⟨v.asIdeal, hv0⟩ := by
      rw [← map_mul]
      rfl
    rw [hm]
    change _ * UpperTheory.V.Kum.primeCl v = 1
    rw [hvc, mul_inv_cancel]
  obtain ⟨y, hy⟩ := hprin
  have hy' : Ideal.span {y} = 𝔞 * v.asIdeal := hy.symm
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hy'
    exact (mul_ne_zero h𝔞 v.ne_bot) hy'.symm
  have hXy := (xMul M K b).2.2.2.2 y hy0
  rw [hy'] at hXy
  exact ⟨_, (xMul M K b).2.1 𝔞 v.asIdeal _ _ h𝔞 v.ne_bot hXy hXv⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceEmb

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have e : f.toRatAlgHom = g.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact h _ hζ.pow_eq_one
  exact RingHom.ext fun x => DFunLike.congr_fun e x

private theorem lift_sg {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (b : (ZMod N)ˣ) (g : G ℚ Ω) (hg : Lifts N b g) (x : K) :
    g (ι x) = ι (sg N K b x) := by
  refine DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) (ι.comp (sg N K b).toRingEquiv.toRingHom)
    fun y hy => ?_) x
  change g (ι y) = ι (sg N K b y)
  rw [hg _ (by rw [← map_pow, hy, map_one]), sg_apply N K b hy, map_pow]

private theorem fix_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (g : G ℚ Ω) (hg : g ∈ fixMu ℚ Ω N) (x : K) :
    g (ι x) = ι x :=
  DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) ι
    fun y hy => hg _ (by rw [← map_pow, hy, map_one])) x

private theorem inv_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N q : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (u : (ZMod N)ˣ) (hu : (u : ZMod N) = q) (g : G ℚ Ω)
    (hg : Pows N q g) (x : K) : g⁻¹ (ι x) = ι ((sg N K u)⁻¹ x) := by
  have h : Lifts N u g := fun y hy => by rw [hg y hy, hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hy]
  apply g.injective
  rw [lift_sg N ι u g h]
  change g (g.symm _) = ι (sg N K u ((sg N K u).symm x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

private theorem place_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : K →+* Ω) (A : ValuationSubring Ω) (hA : A ≠ ⊤) :
    ∃ w : HeightOneSpectrum (𝓞 K), ∀ y : 𝓞 K, A.valuation (ι (y : K)) < 1 ↔ y ∈ w.asIdeal := by
  letI : Algebra K Ω := ι.toAlgebra
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq fun q => by simp
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact (UpperTheory.V.Kum.placeDict K Ω).2.1 A hA

private theorem ne_top {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {n : ℕ} (hn : n ≠ 0)
    (h : Over A n) : A ≠ ⊤ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rintro rfl
  have h1 : (⊤ : ValuationSubring Ω).valuation (n : Ω)⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), map_one] at h2
  exact lt_irrefl _ h2

private theorem val_top {Ω : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) : (⊤ : ValuationSubring Ω).valuation x = 1 := by
  have h (y : Ω) : (⊤ : ValuationSubring Ω).valuation y ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  refine le_antisymm (h x) ?_
  have h1 := h x⁻¹
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h1

private theorem tower {K K' Ω : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field Ω] (M N : ℕ)
    [NeZero M] [NeZero N] [IsCyclotomicExtension {M} ℚ K] [IsCyclotomicExtension {N} ℚ K'] (h : M ∣ N)
    (ι : K →+* Ω) (ι' : K' →+* Ω) : ∃ j : K →+* K', ∀ x, ι' (j x) = ι x := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  have hζ' := (IsCyclotomicExtension.zeta_spec N ℚ K').map_of_injective ι'.injective
  have key : ∀ x : K, ι x ∈ ι'.fieldRange := fun x => by
    have hx : x ∈ Algebra.adjoin ℚ {IsCyclotomicExtension.zeta M ℚ K} := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := h
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one (ξ := ι x)
        (by rw [Set.mem_singleton_iff.1 hx, pow_mul, ← map_pow, hζ.pow_eq_one, map_one, one_pow])
      exact ⟨_, (map_pow ι' _ i).trans hi⟩
    | algebraMap x => exact ⟨(x : K'), by simp⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  choose j hj using key
  exact ⟨{ toFun := j
           map_one' := ι'.injective (by rw [hj, map_one, map_one])
           map_mul' := fun x y => ι'.injective (by rw [map_mul, hj, hj, hj, map_mul])
           map_zero' := ι'.injective (by rw [hj, map_zero, map_zero])
           map_add' := fun x y => ι'.injective (by rw [map_add (f := _), hj, hj, hj, map_add (f := _)]) }, hj⟩

private def XO {Ω : Type} [Field Ω] (N b : ℕ) (A₀ : ValuationSubring Ω) (x : Ω) : Prop :=
  ∃ (_ : NeZero N) (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCyclotomicExtension {N} ℚ K) (ι : K →+* Ω)
    (v : HeightOneSpectrum (𝓞 K)) (X : K), (∀ y : 𝓞 K, A₀.valuation (ι (y : K)) < 1 ↔ y ∈ v.asIdeal) ∧
    IsX N K b v.asIdeal X ∧ x = ι X

private theorem xo_ex {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N b : ℕ) (hb : b < N)
    (A₀ : ValuationSubring Ω) (hA : A₀ ≠ ⊤) : ∃ x, XO N b A₀ x := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let K := CyclotomicField N ℚ
  haveI : @IsCyclotomicExtension {N} ℚ K _ _ DivisionRing.toRatAlgebra := by
    have h := CyclotomicField.isCyclotomicExtension N ℚ
    have e : (DivisionRing.toRatAlgebra : Algebra ℚ K) = CyclotomicField.algebra N ℚ := Subsingleton.elim _ _
    rw [e]
    exact h
  let ι : K →+* Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom
  obtain ⟨v, hv⟩ := place_emb ι A₀ hA
  obtain ⟨X, hX⟩ := xEx N K b v.asIdeal hb v.ne_bot
  exact ⟨ι X, inferInstance, K, inferInstance, inferInstance, inferInstance, ι, v, X, hv, hX, rfl⟩

private theorem xo_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {N b r : ℕ} {A₀ : ValuationSubring Ω}
    (hr : Over A₀ r) {x : Ω} (h : XO N b A₀ x) :
    x ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g x = x) ∧ ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1 := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  have h0 : ι X ≠ 0 := (map_ne_zero ι).2 (left_ne_zero_of_mul_eq_one hX.1)
  refine ⟨h0, fun g hg => fix_emb N ι g hg X, fun A hA => ?_⟩
  by_cases ht : A = ⊤
  · rw [ht]; exact val_top h0
  obtain ⟨w, hw⟩ := place_emb ι A ht
  have h1 := UpperTheory.valuation_kummerElement_eq_one_of_not_over N K b r v w X hX ((hv r).1 (by simpa using hr))
    fun h => hA (by simpa using (hw r).2 h)
  exact (UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω ι A w hw).eq_one_iff_eq_one.2 h1

private theorem xo_ord {Ω : Type} [Field Ω] [Algebra ℚ Ω] {F b r : ℕ} (hp : r.Prime) (h1 : r ≡ 1 [MOD F])
    {A₀ : ValuationSubring Ω} (hr : Over A₀ r) {x : Ω} (h : XO F b A₀ x) : HasOrd F r A₀ x fun t => th F b t := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  intro t σ hσ
  let w : HeightOneSpectrum (𝓞 K) := v.comap (sgO F K t).toRingHom (sgO F K t).surjective
  have hw : ∀ y : 𝓞 K, A₀.valuation ((σ.toRingEquiv.toRingHom.comp ι) (y : K)) < 1 ↔ y ∈ w.asIdeal := fun y => by
    change A₀.valuation (σ (ι y)) < 1 ↔ sgO F K t y ∈ v.asIdeal
    rw [lift_sg F ι t σ hσ, ← hv]
    rfl
  have h2 := UpperTheory.valuation_kummerElement_at_conjugate_prime F K b r v w X t hp h1 hX ((hv r).1 (by simpa using hr)) rfl
  rw [← map_zpow₀] at h2
  have h3 := ((UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω _ A₀ w hw).eq_iff).2 h2
  simpa using h3

private theorem xo_pair {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {M q b r : ℕ} (hp : r.Prime)
    (hq : q.Prime) (hco : q.Coprime M) (hr' : ¬ r ∣ q * M) (hbM : b < M) (hbq : b < q)
    {A₀ : ValuationSubring Ω} (hr : Over A₀ r) {x x' : Ω} (h : XO M b A₀ x) (h' : XO (q * M) b A₀ x') :
    ∃ s : ℕ, s ∣ orderOf (r : ZMod (q * M)) ∧
      (∀ τ ∈ fixMu ℚ Ω M, GenAt q τ → ∀ φ : G ℚ Ω, Pows M q φ →
        ∃ ζ : Ω, ζ ^ (2 * (q * M)) = 1 ∧ nrm q τ x' = ζ * (x / φ⁻¹ x) ^ s) ∧
      ∀ φ : G ℚ Ω, Pows M q φ → ∃ ζ : Ω, ζ ^ (2 * (q * M)) = 1 ∧
        ∀ A : ValuationSubring Ω, Over A q → A.valuation (x' - ζ * φ⁻¹ x ^ s) < 1 := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  obtain ⟨_, K', _, _, _, ι', v', X', hv', hX', rfl⟩ := h'
  obtain ⟨j, hj⟩ := tower M (q * M) (dvd_mul_left M q) ι ι'
  letI : Algebra K K' := j.toAlgebra
  have hj' : ∀ x, ι' (algebraMap K K' x) = ι x := hj
  obtain ⟨s, hs, hn⟩ := UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf (q * M) r K K' hp hr' v v' ((hv' r).1 (by simpa using hr)) fun y => by
    rw [← hv, ← hv', ← hj']
    rfl
  have hXs := (xMul M K b).2.2.1 v.asIdeal X s v.ne_bot hX
  rw [← hn] at hXs
  have hu : ((ZMod.unitOfCoprime q hco : (ZMod M)ˣ) : ZMod M) = q := ZMod.coe_unitOfCoprime q hco
  refine ⟨s, hs, fun τ hτ hg φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨ζ, hζ, he⟩ := xNormDiv M q K K' hq _ hu b hbq v'.asIdeal X' (X ^ s) v'.ne_bot hX' hXs
    refine ⟨ι ζ, ?_, ?_⟩
    · rw [show 2 * (q * M) = 2 * M * q by ring, pow_mul, ← map_pow, hζ, map_one, one_pow]
    · rw [UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator Ω M q K K' ι' hq hco τ hτ hg, hj', he, inv_emb M q ι _ hu φ hφ]
      simp only [map_mul, map_div₀, map_pow, div_pow]
  · have hqr : r.Coprime q := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hr' (h.mul_right M)
    have hq' : (q : 𝓞 K') ∉ v'.asIdeal := fun h =>
      (placeBasic Ω).2.2.2.1 A₀ r q hqr hr (by simpa using (hv' q).2 h)
    have hc : IsCoprime v'.asIdeal (Ideal.span {(q : 𝓞 K')}) := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hq' ((v'.isMaximal.eq_of_le hne le_sup_left).ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    obtain ⟨ζ, hζ, he⟩ := xCong M q K K' hq _ hu b hbM hbq v'.asIdeal X' (X ^ s) hc hX' hXs
    refine ⟨ι' ζ, by rw [← map_pow, hζ, map_one], fun A hA => ?_⟩
    obtain ⟨w, hw⟩ := place_emb ι' A (ne_top hq.ne_zero hA)
    have h3 := (UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K' Ω ι' A w hw).lt_one_iff_lt_one.2 (he w ((hw q).1 (by simpa using hA)))
    rw [Valuation.comap_apply, map_sub, map_mul, hj', map_pow, map_pow, ← inv_emb M q ι _ hu φ hφ] at h3
    exact h3

theorem UpperTheory.V.ML.laxEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l F r b : ℕ) [NeZero F], l.Prime → r.Prime → r ≡ 1 [MOD F] → b < F → ∀ A₀ : ValuationSubring Ω, Over A₀ r →
    ∃ (X : ℕ → Ω) (s : ℕ → ℕ → ℕ), Lax l F r X s ∧ HasOrd F r A₀ (X 1) fun t => th F b t := by
  intro Ω _ _ _ l F r b _ hl hr h1 hb A₀ hA
  have hlt : ∀ d, d ≠ 0 → b < F * d := fun d hd => hb.trans_le (Nat.le_mul_of_pos_right F (Nat.pos_of_ne_zero hd))
  have hX : ∀ d : ℕ, ∃ x : Ω, d ≠ 0 → XO (F * d) b A₀ x := fun d => by
    by_cases hd : d = 0
    · exact ⟨0, fun h => absurd hd h⟩
    · obtain ⟨x, hx⟩ := xo_ex (F * d) b (hlt d hd) A₀ (ne_top hr.ne_zero hA)
      exact ⟨x, fun _ => hx⟩
  choose X hX using hX
  have hs : ∀ d q : ℕ, ∃ s : ℕ, q.Prime → ML.admitted l F r (q * d) → ¬ l ∣ s ∧
      (∀ τ ∈ fixMu ℚ Ω (F * d), GenAt q τ → ∀ φ : G ℚ Ω, Pows (F * d) q φ →
        ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧ nrm q τ (X (q * d)) = ζ * (X d / φ⁻¹ (X d)) ^ s) ∧
      ∀ φ : G ℚ Ω, Pows (F * d) q φ → ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧
        ∀ A : ValuationSubring Ω, Over A q → A.valuation (X (q * d) - ζ * φ⁻¹ (X d) ^ s) < 1 := fun d q => by
    by_cases h : q.Prime ∧ ML.admitted l F r (q * d)
    swap
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ h⟩
    obtain ⟨hq, ha⟩ := h
    have h0 : q * d ≠ 0 := ha.1.ne_zero
    have hd : d ≠ 0 := right_ne_zero_of_mul h0
    have he : F * (q * d) = q * (F * d) := by ring
    have hqF : q ≡ 1 [MOD F] := (ha.2 q hq (dvd_mul_right q d)).2.1
    have hco : q.Coprime (F * d) := Nat.Coprime.mul_right
      (by rw [Nat.Coprime, hqF.gcd_eq]; exact Nat.gcd_one_left F) (Nat.coprime_of_squarefree_mul ha.1)
    have hFq : F < q := by
      have h2 := Nat.le_of_dvd (by have := hq.two_le; omega) ((Nat.modEq_iff_dvd' hq.one_le).1 hqF.symm)
      have := hq.two_le
      omega
    obtain ⟨hc1, hc2⟩ := UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level l F r (q * d) (NeZero.ne F) hl hr h1 ha
    have hx' := hX (q * d) h0
    rw [he] at hc1 hc2 hx'
    obtain ⟨s, hs, h2, h3⟩ := xo_pair hr hq hco hc2 (hlt d hd) (hb.trans hFq) hA (hX d hd) hx'
    rw [show 2 * (q * (F * d)) = 2 * F * (q * d) by ring] at h2 h3
    exact ⟨s, fun _ _ => ⟨fun h => hc1 (h.trans hs), h2, h3⟩⟩
  choose s hs using hs
  refine ⟨X, s, ⟨fun d hd => (xo_one hA (hX d hd.1.ne_zero)).1, fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.1,
    fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.2, fun d q hq ha => (hs d q hq ha).1,
    fun d q hq ha => (hs d q hq ha).2.1, fun d q hq ha => (hs d q hq ha).2.2⟩, ?_⟩
  have h := hX 1 one_ne_zero
  rw [mul_one] at h
  exact xo_ord hr h1 hA h
end
end
