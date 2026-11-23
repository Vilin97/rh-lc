module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
public import Mathlib.NumberTheory.RamificationInertia.Galois
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NcardPlacesOverEqOfPrimeDegree

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem ncard_places_over_eq_of_prime_degree :
    ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [IsGalois F E], p.Prime → Module.finrank F E = p →
      ∀ (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)), w ≠ w' →
        w.under (𝓞 F) = v → w'.under (𝓞 F) = v →
        Set.ncard {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} = p := by
  intro p F E _ _ _ _ _ _ hp hdeg v w w' hne hw hw'
  have : IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ F E
  have hv := v.isMaximal
  have himg : (fun u : HeightOneSpectrum (𝓞 E) => u.asIdeal) ''
      {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} = v.asIdeal.primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : u.under (𝓞 F) = v := hu
      exact ⟨u.isPrime, ⟨by rw [← hu']; rfl⟩⟩
    · rintro ⟨hP, hPv⟩
      refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ?_, rfl⟩
      exact HeightOneSpectrum.ext hPv.over.symm
  have hcard : Set.ncard {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v}
      = (v.asIdeal.primesOver (𝓞 E)).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 E)
    (E ≃ₐ[F] E)
  rw [IsGalois.card_aut_eq_finrank, hdeg, ← hcard] at hf
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ hf) with h1 | h1
  · exfalso
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have h2 : w ∈ {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} := hw
    have h3 : w' ∈ {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} := hw'
    rw [ha] at h2 h3
    exact hne (h2.trans h3.symm)
  · exact h1

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPlacesOfEmbeddings

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem two_places_of_embeddings : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (ψ ψ' : E →ₐ[F] v.adicCompletion F), ψ ≠ ψ' → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  intro F E _ _ _ _ _ v ψ ψ' hne
  let V : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  let u : Valuation E ℤᵐ⁰ := V.comap (ψ : E →+* v.adicCompletion F)
  let u' : Valuation E ℤᵐ⁰ := V.comap (ψ' : E →+* v.adicCompletion F)
  have hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ _) = _
    rw [AlgHom.commutes]
    exact v.valuedAdicCompletion_eq_valuation' a
  have hu' : ∀ a : F, u' (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ' _) = _
    rw [AlgHom.commutes]
    exact v.valuedAdicCompletion_eq_valuation' a
  obtain ⟨w, hw, hwm⟩ := exists_centre_over v u hu
  obtain ⟨w', hw', hwm'⟩ := exists_centre_over v u' hu'
  refine ⟨w, w', ?_, hw, hw'⟩
  rintro rfl
  obtain ⟨z, hz⟩ : ∃ z, ψ z ≠ ψ' z := by
    by_contra hc
    push Not at hc
    exact hne (AlgHom.ext hc)
  obtain ⟨d, hd⟩ : ∃ d, d = ψ z - ψ' z := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by rw [hd]; exact sub_ne_zero.2 hz
  have hVd : V d ≠ 0 := (Valuation.ne_zero_iff _).2 hd0
  obtain ⟨ρ, hρ⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    (ψ z) d⁻¹
  obtain ⟨c, hc⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    d d⁻¹
  set t := (ψ z - algebraMap F (v.adicCompletion F) ρ) * d⁻¹ with ht
  set s := (d - algebraMap F (v.adicCompletion F) c) * d⁻¹ with hs
  have e1 : ψ z - algebraMap F (v.adicCompletion F) ρ = d * t := by
    rw [ht]; field_simp
  have e2 : ψ' z - algebraMap F (v.adicCompletion F) ρ = -(d * (1 - t)) := by
    linear_combination e1 + hd
  have e3 : algebraMap F (v.adicCompletion F) c = d * (1 - s) := by
    rw [hs]; field_simp; ring
  obtain ⟨y, hy⟩ : ∃ y, y = (z - algebraMap F E ρ) / algebraMap F E c := ⟨_, rfl⟩
  have huy : u y < 1 := by
    change V (ψ y) < 1
    rw [hy, map_div₀, map_sub, AlgHom.commutes, AlgHom.commutes, e1, e3, map_div₀,
      map_mul _ _ t, map_mul _ _ (1 - s), Valuation.map_one_sub_of_lt _ hc, mul_one,
      mul_div_cancel_left₀ _ hVd]
    exact hρ
  have huy' : u' y = 1 := by
    change V (ψ' y) = 1
    rw [hy, map_div₀, map_sub, AlgHom.commutes, AlgHom.commutes, e2, e3, map_div₀,
      Valuation.map_neg, map_mul _ _ (1 - t), map_mul _ _ (1 - s),
      Valuation.map_one_sub_of_lt _ hc, Valuation.map_one_sub_of_lt _ hρ, div_self]
    rwa [mul_one]
  obtain ⟨n, ⟨m, hm⟩, hnd | hnd⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
  · have hd1 : 1 ≤ u' (algebraMap (𝓞 E) E m) := not_lt.1 fun a => hm ((hwm' m).2 a)
    have h1 : u (algebraMap (𝓞 E) E n) < 1 := by
      rw [← hnd, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u m)) huy
    have h2 := (hwm' n).1 ((hwm n).2 h1)
    rw [← hnd, map_mul, huy', one_mul] at h2
    exact absurd h2 (not_lt.2 hd1)
  · have hd1 : 1 ≤ u (algebraMap (𝓞 E) E m) := not_lt.1 fun a => hm ((hwm m).2 a)
    rw [← hnd, map_mul] at hd1
    exact absurd (lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u n)) huy)
      (not_lt.2 hd1)

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeMulCardPlacesLeCardOverKummer

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem prime_mul_card_le_card_over : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → p * S.card ≤ SE.card + (p - 1) * tNon p F δ S := by
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE
  classical
  have hp := hq.prime
  obtain ⟨-, hrk, hgal, -, -, -, hemb⟩ := kummer_galois p F E ζ δ θ σ hq
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tNon p F δ S
      = ∑ v ∈ S, if (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ)
        then 1 else 0 := by
    rw [← Finset.card_filter, tNon, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega
  · rw [if_neg hs]
    push Not at hs
    obtain ⟨r, hr⟩ := hs
    have hδ : δ ≠ 0 := fun h0 => hq.nonpow 0 (by rw [h0, zero_pow hp.ne_zero])
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at hr
      exact hδ hr
    obtain ⟨ψ, hψ⟩ := hemb (v.adicCompletion F) r hr
    obtain ⟨ψ', hψ'⟩ := hemb (v.adicCompletion F) (algebraMap F (v.adicCompletion F) ζ * r)
      (by rw [mul_pow, ← map_pow, hq.root.pow_eq_one, map_one, one_mul, hr])
    have hne : ψ ≠ ψ' := by
      intro h
      rw [← h, hψ, eq_comm, mul_eq_right₀ hr0,
        ← map_one (algebraMap F (v.adicCompletion F))] at hψ'
      exact hq.root.ne_one hp.one_lt ((algebraMap F (v.adicCompletion F)).injective hψ')
    obtain ⟨w, w', hww, hw, hw'⟩ := two_places_of_embeddings F E v ψ ψ' hne
    have h3 := ncard_places_over_eq_of_prime_degree p F E hp hrk v w w' hww hw hw'
    have h4 : (SE.filter (fun w => w.under (𝓞 F) = v)).card = p := by
      rw [← h3, ← Set.ncard_coe_finset]
      congr 1
      ext u
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨(hSE u).2 (h ▸ hv), h⟩⟩
    omega

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeMulCardPlacesLeCardOverKummerStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.prime_mul_card_places_le_card_over_kummer : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → p * S.card ≤ SE.card + (p - 1) * tNon p F δ S := by
  first | exact @GlobalTheory.CNorm.prime_mul_card_le_card_over | exact GlobalTheory.CNorm.prime_mul_card_le_card_over | (intros; apply GlobalTheory.CNorm.prime_mul_card_le_card_over <;> assumption)
end
end
