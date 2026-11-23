module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
import Formalism.LocalRingCardinality.SpanPowerMembership.GatRing
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemPowHeightOneIdealIffDvdEmbedding

section

@[expose] public section

open NumberField IsDedekindDomain WithZero

namespace GlobalTheory

theorem ordIdeal_of_ringHom {R W : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (P : HeightOneSpectrum R) (p : W) (hp : Irreducible p) (f : R →+* W)
    (hP : ∀ x : R, x ∈ P.asIdeal ↔ p ∣ f x)
    (hd : ∀ (y : W) (n : ℕ), ∃ (x : R) (z : W), f x = y + p ^ n * z)
    (x : R) (k : ℕ) : x ∈ P.asIdeal ^ k ↔ p ^ k ∣ f x := by

  have hpp : Prime p := hp.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨π, z, hπ⟩ := hd p 2
  have hπP : π ∈ P.asIdeal := (hP π).2 ⟨1 + p * z, by rw [hπ]; ring⟩
  set Q : Ideal R := Ideal.comap f (Ideal.span {p ^ k}) with hQdef
  have hQ : ∀ y : R, y ∈ Q ↔ p ^ k ∣ f y := fun y => by
    rw [hQdef, Ideal.mem_comap, Ideal.mem_span_singleton]
  have hle : P.asIdeal ^ k ≤ Q := by
    have h1 : P.asIdeal ≤ Ideal.comap f (Ideal.span {p}) := fun y hy => by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact (hP y).1 hy
    calc P.asIdeal ^ k ≤ (Ideal.comap f (Ideal.span {p})) ^ k := Ideal.pow_right_mono h1 k
      _ ≤ Ideal.comap f ((Ideal.span {p}) ^ k) := Ideal.le_comap_pow f k
      _ = Q := by rw [Ideal.span_singleton_pow]
  obtain ⟨j, hj, hassoc⟩ := (dvd_prime_pow P.prime k).1 (Ideal.dvd_iff_le.2 hle)
  have hQj : Q = P.asIdeal ^ j := associated_iff_eq.1 hassoc
  have hjk : j = k := by
    by_contra hne
    have hjk' : j ≤ k - 1 := by omega
    have hmem : π ^ (k - 1) ∈ Q := by
      rw [hQj]
      exact Ideal.pow_le_pow_right hjk' (Ideal.pow_mem_pow hπP _)
    rw [hQ, map_pow, hπ] at hmem
    have hfac : (p + p ^ 2 * z) ^ (k - 1) = p ^ (k - 1) * (1 + p * z) ^ (k - 1) := by
      rw [← mul_pow]; ring
    have hk' : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hfac, hk'] at hmem
    have hdiv := (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hp0)).1 hmem
    have hdiv' := hpp.dvd_of_dvd_pow hdiv
    have hone : p ∣ 1 := (dvd_add_left (dvd_mul_right p z)).1 hdiv'
    exact hp.not_isUnit (isUnit_of_dvd_one hone)
  rw [← hQ, hQj, hjk]

theorem ordIdeal_of_embedding {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ) : ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by

  intro hxy
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  choose F hF using h1
  let f : 𝓞 E →+* W :=
    { toFun := F
      map_one' := hinj (by rw [← (hF 1).1]; simp)
      map_mul' := fun a b => hinj (by
        rw [map_mul, ← (hF (a * b)).1, ← (hF a).1, ← (hF b).1]; simp)
      map_zero' := hinj (by rw [← (hF 0).1]; simp)
      map_add' := fun a b => hinj (by
        rw [map_add (f := _), ← (hF (a + b)).1, ← (hF a).1, ← (hF b).1]; simp) }
  have hfx : ∀ a : 𝓞 E, algebraMap W Qq (f a) = ρ a := fun a => ((hF a).1).symm
  have hP : ∀ a : 𝓞 E, a ∈ P.asIdeal ↔ (p : W) ∣ f a := fun a => (hF a).2
  have hd : ∀ (b : W) (n : ℕ), ∃ (a : 𝓞 E) (c : W), f a = b + (p : W) ^ n * c := by
    intro b n
    obtain ⟨a, c, hac⟩ := h2 b n
    exact ⟨a, c, hinj (by rw [hfx, hac])⟩
  have hy : f x = y := hinj (by rw [hfx, hxy])
  rw [ordIdeal_of_ringHom P (p : W) hp f hP hd x k, hy]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemPowHeightOneIdealIffDvdEmbeddingStatement

section

@[expose] public section

open NumberField IsDedekindDomain WithZero

theorem _root_.GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ), ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by
  first | exact @GlobalTheory.ordIdeal_of_embedding | exact GlobalTheory.ordIdeal_of_embedding | (intros; apply GlobalTheory.ordIdeal_of_embedding <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SurjectiveAlgebraMapAdicCompletionCompleteDvr

section

@[expose] public section

open NumberField IsDedekindDomain WithZero

namespace GlobalTheory.DenseCompl

theorem exists_eq_algebraMap_of_valued_le_one {W Qq : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] {π : W}
    (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W)
    {a : v.adicCompletion Qq} (ha : Valued.v a ≤ 1) :
    ∃ L : W, a = algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq L) := by
  choose r hr using fun n : ℕ => GlobalTheory.Idele.exists_valued_sub_le v ha n
  have hle : ∀ m n : ℕ, m ≤ n → exp (-(n : ℤ)) ≤ exp (-(m : ℤ)) := fun m n h => by
    rw [exp_le_exp]; omega
  have hdiv : ∀ m n : ℕ, m ≤ n → π ^ m ∣ r n - r m := by
    intro m n hmn
    have h1 : v.valuation Qq (algebraMap W Qq (r n - r m)) ≤ exp (-(m : ℤ)) := by
      rw [← GlobalTheory.Idele.valued_algebraMap, map_sub, map_sub]
      have he : algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n)) -
          algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r m)) =
          (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r m))) -
          (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n))) := by ring
      rw [he]
      exact (Valuation.map_sub _ _ _).trans (max_le (hr m) ((hr n).trans (hle m n hmn)))
    obtain ⟨w, hw⟩ := (exists_eq_pow_mul_iff hπ v _ m).2 h1
    exact ⟨w, IsFractionRing.injective W Qq hw⟩
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := r) (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact (dvd_sub_comm).1 (hdiv m n hmn))
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero, ← Valuation.zero_iff Valued.v]
  refine eq_zero_of_forall_le_exp fun n => ?_
  have h2 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h2
  obtain ⟨w, hw⟩ := h2
  have h3 : Valued.v (algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n - L))) ≤
      exp (-(n : ℤ)) := by
    rw [GlobalTheory.Idele.valued_algebraMap]
    exact (exists_eq_pow_mul_iff hπ v _ n).1 ⟨w, by rw [hw]⟩
  have he : a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq L) =
      (a - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n))) +
      algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq (r n - L)) := by
    rw [map_sub, map_sub]; ring
  rw [he]
  exact (Valuation.map_add _ _ _).trans (max_le (hr n) h3)

theorem surjective_algebraMap_adicCompletion : ∀ {W Qq : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (π : W)
    (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W),
    Function.Surjective (algebraMap Qq (v.adicCompletion Qq)) := by
  intro W Qq _ _ _ _ _ _ π hπ hc v a
  by_cases ha : Valued.v a ≤ 1
  · obtain ⟨L, hL⟩ := exists_eq_algebraMap_of_valued_le_one hπ hc v ha
    exact ⟨_, hL.symm⟩
  have ha0 : Valued.v a ≠ 0 := fun h => ha (h ▸ zero_le')
  set p := algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq π) with hpdef
  have hp : Valued.v p = exp (-1) := by
    rw [hpdef, GlobalTheory.Idele.valued_algebraMap, valuation_uniformiser hπ v]
  have hp0 : p ≠ 0 := fun h => exp_ne_zero (by rw [← hp, h, map_zero] : exp (-1 : ℤ) = 0)
  set m := (log (Valued.v a)).toNat
  have hva : Valued.v a = exp (log (Valued.v a)) := (exp_log ha0).symm
  have hle : Valued.v (a * p ^ m) ≤ 1 := by
    rw [map_mul, map_pow, hva, hp, ← exp_nsmul, ← exp_add, ← exp_zero, exp_le_exp]
    have := Int.self_le_toNat (log (Valued.v a))
    simp only [smul_neg, nsmul_eq_mul, mul_one]
    omega
  obtain ⟨L, hL⟩ := exists_eq_algebraMap_of_valued_le_one hπ hc v hle
  refine ⟨algebraMap W Qq L / algebraMap W Qq π ^ m, ?_⟩
  rw [map_div₀, map_pow, ← hL, ← hpdef, mul_div_cancel_right₀ _ (pow_ne_zero _ hp0)]

end GlobalTheory.DenseCompl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SurjectiveAlgebraMapAdicCompletionCompleteDvrStatement

section

@[expose] public section

open NumberField IsDedekindDomain WithZero

theorem _root_.GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (π : W) (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W), Function.Surjective (algebraMap Qq (v.adicCompletion Qq)) := by
  first | exact @GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | exact GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | (intros; apply GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramified

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
open WithZero

namespace GlobalTheory.DenseCompl

theorem completion_ringEquiv_of_dense : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (hc : IsAdicComplete (Ideal.span {(p : W)}) W) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)), ∃ φ : P.adicCompletion E ≃+* Qq, (∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) ∧ (∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) ∧ ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U := by
  intro E _ _ P W Qq _ _ _ _ _ _ p hp hc ρ h1 h2
  classical
  set v := closedPoint W
  have hint : ∀ x : 𝓞 E, v.valuation Qq (ρ x) = P.valuation E x := by
    intro x
    obtain ⟨y, hy, -⟩ := h1 x
    have hx : (x : E) = algebraMap (𝓞 E) E x := rfl
    rw [hy, hx, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    have key : ∀ k : ℕ, P.intValuation x ≤ exp (-(k : ℤ)) ↔ v.intValuation y ≤ exp (-(k : ℤ)) := by
      intro k
      rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
        asIdeal_eq_span hp v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding P p hp ρ h1 h2 x y k hy
    exact le_antisymm (le_of_forall_le_exp (P.intValuation_le_one x) fun k hk => (key k).1 hk)
      (le_of_forall_le_exp (v.intValuation_le_one y) fun k hk => (key k).2 hk)
  have hval : ∀ x : E, v.valuation Qq (ρ x) = P.valuation E x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hint a) (hint b)
  have hf : ∀ x : E, Valued.v (((algebraMap Qq (v.adicCompletion Qq)).comp ρ) x) = P.valuation E x :=
    fun x => by rw [RingHom.comp_apply, GlobalTheory.Idele.valued_algebraMap, hval]
  obtain ⟨ψ, -, hψ, hψv⟩ := exists_extension P v _ hf
  have hψW : ∀ y : W, algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) ∈ Set.range ψ := by
    intro y
    choose x z hxz using fun n : ℕ => h2 y n
    let u : ℕ → P.adicCompletion E := fun n => algebraMap E _ (x n : E)
    have hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ)) := by
      intro m n hnm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      simp only [u]
      rw [← map_sub, GlobalTheory.Idele.valued_algebraMap, ← hval, map_sub, hxz, hxz, ← map_sub]
      refine (exists_eq_pow_mul_iff hp v _ n).1 ⟨(p : W) ^ k * z (n + k) - z n, ?_⟩
      congr 1
      ring
    obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit P u hu
    refine ⟨t, ?_⟩
    rw [← sub_eq_zero]
    refine Valued.v.zero_iff.1 (eq_zero_of_forall_le_exp fun n => ?_)
    have e : ψ t - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) =
        ψ (t - u n) + algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq ((p : W) ^ n * z n)) := by
      rw [map_sub, hψ, RingHom.comp_apply, hxz, map_add (f := _), map_add (f := _)]
      ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [hψv]
      exact ht n
    · rw [GlobalTheory.Idele.valued_algebraMap]
      exact (exists_eq_pow_mul_iff hp v _ n).1 ⟨z n, rfl⟩
  have hι := GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr (Qq := Qq) (p : W) hp hc v
  have hsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨q, rfl⟩ := hι a
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) q
    obtain ⟨s, hs⟩ := hψW a
    obtain ⟨t, ht⟩ := hψW b
    exact ⟨s / t, by rw [map_div₀, hs, ht, map_div₀]⟩
  let eψ := RingEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩
  let eι := RingEquiv.ofBijective (algebraMap Qq (v.adicCompletion Qq))
    ⟨(algebraMap Qq (v.adicCompletion Qq)).injective, hι⟩
  have hφ : ∀ z, algebraMap Qq (v.adicCompletion Qq) ((eψ.trans eι.symm) z) = ψ z :=
    fun z => eι.apply_symm_apply (ψ z)
  have hS : ∀ (n : ℕ) (z : P.adicCompletion E),
      (∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)) ↔ Valued.v z ≤ exp (-(n : ℤ)) := by
    intro n z
    rw [exists_eq_pow_mul_iff hp v, ← GlobalTheory.Idele.valued_algebraMap v, hφ, hψv]
  refine ⟨eψ.trans eι.symm, fun x => ?_, fun n => ?_, fun U hU => ?_⟩
  · apply (algebraMap Qq (v.adicCompletion Qq)).injective
    rw [hφ, hψ]
    rfl
  · have e : {z : P.adicCompletion E | ∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)} =
        {z | Valued.v z ≤ exp (-(n : ℤ))} := Set.ext fun z => hS n z
    rw [e]
    exact GlobalTheory.Idele.isOpen_valued_le P (-(n : ℤ))
  · obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
    obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt
      (γ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)
    refine ⟨n, fun z hz => hγ ?_⟩
    have hz' := (hS n z).1 hz
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact hz'.trans_lt hn

end GlobalTheory.DenseCompl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramifiedStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem _root_.GlobalTheory.T.numberField_completion_ringEquiv_of_dense_unramified : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (hc : IsAdicComplete (Ideal.span {(p : W)}) W) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)), ∃ φ : P.adicCompletion E ≃+* Qq, (∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) ∧ (∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) ∧ ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U := by
  first | exact @GlobalTheory.DenseCompl.completion_ringEquiv_of_dense | exact GlobalTheory.DenseCompl.completion_ringEquiv_of_dense | (intros; apply GlobalTheory.DenseCompl.completion_ringEquiv_of_dense <;> assumption)
end
end
