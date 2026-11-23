module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90Statement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HerbrandPrimeOrderStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsKummerStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowsSubgroupOfSelfSPow
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeMulCardPlacesLeCardOverKummerStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceValuationAut

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_place_valuation_aut (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧
      ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = σ (x : E) := fun x => rfl
  have hfix : ∀ a : 𝓞 F, e (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hc]
    exact σ.commutes (a : F)
  refine ⟨w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective, ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    ext a
    change e (algebraMap (𝓞 F) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ w.asIdeal
    rw [hfix]
  · intro y
    exact valuation_of_eq_comap σ.toRingEquiv w _ rfl y

theorem sUnits_over_and_aut : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ (τ : E ≃ₐ[F] E) (y : Eˣ), y ∈ sUnits E SE → Units.map (τ : E →* E) y ∈ sUnits E SE := by
  intro F E _ _ _ _ _ _ S SE hS
  obtain ⟨-, hup, hval⟩ := places_over F E
  refine ⟨fun x => ⟨fun h => ?_, fun h => ?_⟩, fun σ y hy => ?_⟩
  · rw [mem_sUnits] at h ⊢
    intro v hv
    obtain ⟨w, rfl⟩ := hup v
    obtain ⟨e, he, hx⟩ := hval w
    have h1 : w.valuation E (algebraMap F E (x : F)) = 1 := h w (fun a => hv ((hS w).1 a))
    rw [hx] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le he.ne').1 h1
  · rw [mem_sUnits] at h ⊢
    intro w hw
    obtain ⟨e, he, hx⟩ := hval w
    change w.valuation E (algebraMap F E (x : F)) = 1
    rw [hx, h _ (fun a => hw ((hS w).2 a)), one_pow]
  · rw [mem_sUnits] at hy ⊢
    intro w hw
    obtain ⟨w', hu, hv⟩ := exists_place_valuation_aut F E σ w
    change w.valuation E (σ (y : E)) = 1
    rw [← hv]
    exact hy w' (fun a => hw ((hS w).2 (hu ▸ (hS w').1 a)))

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegree

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

private theorem pIdx_range_eq (p : ℕ) {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    pIdx p j.range = (pows p (⊤ : Subgroup U)).index := by
  unfold pIdx
  rw [← Subgroup.index_comap]
  congr 1
  ext x
  simp only [pows, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap,
    powMonoidHom_apply, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨y, hj (by simpa using h)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨j y, ⟨y, rfl⟩, by simp⟩

private theorem index_pows_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    (pows p (⊤ : Subgroup U)).index = pIdx p U := by
  rw [← pIdx_range_eq p U.subtype U.subtype_injective, Subgroup.range_subtype]

private theorem pIdx_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pIdx p (⊤ : Subgroup U) = pIdx p U := by
  rw [← index_pows_top_eq p U, pIdx, Subgroup.relIndex_top_right]

private theorem pTor_range_eq (p : ℕ) {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    pTor p j.range = pTor p (⊤ : Subgroup U) := by
  unfold pTor
  symm
  refine Nat.card_eq_of_bijective
    (fun x => ⟨j x.1, ⟨x.1, rfl⟩, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨⟨y, Subgroup.mem_top _, hj (by rw [map_pow, h, map_one])⟩, rfl⟩

private theorem pTor_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p (⊤ : Subgroup U) = pTor p U := by
  rw [← pTor_range_eq p U.subtype U.subtype_injective, Subgroup.range_subtype]

private theorem arith_first_ineq (p m n c e r t : ℕ) (hp : p.Prime) (hd : m ∣ n) (hn : n ≠ 0)
    (h : n ^ (p - 1) * p ^ (e + p * r) * p ^ p = 1 ^ (p - 1) * p * (p ^ (c + r)) ^ p)
    (hs : p * c ≤ e + (p - 1) * t) : m ≠ 0 ∧ p * m ≤ p ^ t := by
  refine ⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have hq : q ≠ 0 := by have := hp.two_le; omega
  simp only [Nat.add_sub_cancel, one_pow, one_mul] at h hs
  set p := q + 1 with hpq
  have hpos : 0 < p := hp.pos
  have h1 : (p * p ^ (e + p * r)) * (p * n) ^ q ≤ (p * p ^ (e + p * r)) * (p ^ t) ^ q := by
    calc (p * p ^ (e + p * r)) * (p * n) ^ q
        = n ^ q * p ^ (e + p * r) * p ^ (q + 1) := by rw [mul_pow, pow_succ]; ring
      _ = p * (p ^ (c + r)) ^ p := h
      _ = p * p ^ (p * c + p * r) := by rw [← pow_mul]; congr 2; ring
      _ ≤ p * p ^ (e + q * t + p * r) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (by omega))
      _ = (p * p ^ (e + p * r)) * (p ^ t) ^ q := by
        rw [← pow_mul, mul_assoc, ← pow_add]; congr 2; ring
  have h2 : (p * n) ^ q ≤ (p ^ t) ^ q := Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 : p * n ≤ p ^ t := (Nat.pow_le_pow_iff_left hq).1 h2
  exact le_trans (Nat.mul_le_mul_left _ hmn) h3

theorem first_inequality_sUnits_prime :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ)
      (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S →
      δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) →
      (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        p * (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ p ^ tNon p F δ S := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns
  obtain ⟨E, _, _, θ, σ, hq⟩ := exists_isKum p F ζ δ hp hζ hns
  obtain ⟨hfd, hrk, hper, hfix, -, -, hnorm⟩ := GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p F E ζ δ θ σ hq
  obtain ⟨-, -, hgal, -⟩ := kummer_galois p F E ζ δ θ σ hq
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  obtain ⟨hup, hσ⟩ := sUnits_over_and_aut F E S SE hSE
  have h90 := GlobalTheory.T.hilbert90_sUnits_kummer' p F E ζ δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)
  have hcf := GlobalTheory.T.prime_mul_card_places_le_card_over_kummer p F E ζ δ θ σ hq S SE hSE
  have hζE : IsPrimitiveRoot (algebraMap F E ζ) p := hζ.map_of_injective (algebraMap F E).injective
  obtain ⟨htF, hiF⟩ := pTor_pIdx_sUnits p F ζ S hp hζ
  obtain ⟨htE, hiE⟩ := pTor_pIdx_sUnits p E _ SE hp hζE
  have hinf : Fintype.card (InfinitePlace E) = p * Fintype.card (InfinitePlace F) := by
    have h1 := IsTotallyComplex.finrank F
    have h2 := IsTotallyComplex.finrank E
    have h3 := Module.finrank_mul_finrank ℚ F E
    have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h5 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at h4 h5
    rw [h4, h5]
    rw [h1, h2, hrk] at h3
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    rw [← h3]; ring
  let τ : sUnits E SE →* sUnits E SE :=
    ((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ σ y y.2)
  have hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E) :=
    fun _ => rfl
  have hτi : ∀ (i : ℕ) (y : sUnits E SE),
      (((τ^[i] y : sUnits E SE) : Eˣ) : E) = σ^[i] ((y : Eˣ) : E) := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]
  have hN : ∀ y : sUnits E SE, (((nrm τ p y : sUnits E SE) : Eˣ) : E) =
      ∏ i ∈ Finset.range p, σ^[i] ((y : Eˣ) : E) := by
    intro y
    rw [nrm_apply]
    change ((sUnits E SE).subtype (∏ i ∈ Finset.range p, τ^[i] y) : E) = _
    rw [map_prod, Units.coe_prod]
    exact Finset.prod_congr rfl (fun i _ => hτi i y)
  let j : sUnits F S →* sUnits E SE :=
    ((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _
      (fun y => (hup y).2 y.2)
  have hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F) :=
    fun _ => rfl
  have hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b :=
    fun a b h => Subtype.ext (Units.ext h)
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  have hrange : fix τ = j.range := by
    ext y
    rw [MonoidHom.mem_range, mem_fix]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hfix ((y : Eˣ) : E) (by rw [← hτ, h])
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact (y : Eˣ).ne_zero (by simpa using ha)
      have hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y :=
        Units.ext (by simpa using ha.symm)
      refine ⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩
      rw [hj, ha]; rfl
    · rintro ⟨x, rfl⟩
      apply hext
      rw [hτ, hj, AlgEquiv.commutes]
  have hone : (dif τ).range.relIndex (nrm τ p).ker = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro a ha
    have h1 : ∏ i ∈ Finset.range p, σ^[i] ((a : Eˣ) : E) = 1 := by
      rw [← hN, MonoidHom.mem_ker.1 ha]; rfl
    obtain ⟨y, hy, h⟩ := h90 a a.2 h1
    refine ⟨⟨y, hy⟩, hext _ _ ?_⟩
    rw [h, dif_apply, Subgroup.coe_div, Units.val_div_eq_div_val, hτ]
  obtain ⟨h0, -, -, -, key⟩ := GlobalTheory.T.herbrand_prime_order' p (sUnits E SE) τ hp
    (fun a => hext _ _ (by rw [hτi, hper]))
    (by rw [pIdx_top_eq, hiE]; exact pow_ne_zero _ hp.ne_zero)
    (by rw [pTor_top_eq, htE]; exact hp.ne_zero)
  rw [hone, hrange, pIdx_range_eq p j hjinj, pTor_range_eq p j hjinj, index_pows_top_eq,
    pIdx_top_eq, pTor_top_eq, pTor_top_eq, htF, htE, hiF, hiE, hinf,
    ← Subgroup.index_comap] at key
  rw [hrange, ← Subgroup.index_comap] at h0
  refine arith_first_ineq p _ _ _ _ _ _ hp ?_ h0 key hcf
  apply Subgroup.index_dvd_of_le
  rintro x ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, hnorm]
  exact ⟨((y : Eˣ) : E), by rw [← hN, hy, hj]⟩

end GlobalTheory.CNorm
end
end
