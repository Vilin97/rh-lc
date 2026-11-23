module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolateMaximalAmongPrimesContainingEtaleStatement
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationResidueApproximation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentApproximationSurjective
import Mathlib.RingTheory.Etale.Weakly

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximal

section

@[expose] public section

namespace GlobalTheory

theorem etale_prime_le_map_of_unique (B A : Type) [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.Etale B A] (P : Ideal B) (hP : P.IsMaximal) (Q : Ideal A)
    (hQ : ∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) :
    Q ≤ P.map (algebraMap B A) := by
  set I := P.map (algebraMap B A) with hI
  by_cases htop : I = ⊤
  · rw [htop]; exact le_top

  have hrad : I.radical = Q := by
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop
    have hMQ : M = Q := hQ M hM.isPrime hIM
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hMQ ▸ hIM, hMQ ▸ hM.isPrime⟩
    · refine le_sInf ?_
      rintro J ⟨hJ1, hJ2⟩
      exact (hQ J hJ2 hJ1).ge

  haveI := hP
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FormallyUnramified B (A ⧸ I) :=
    Algebra.FormallyUnramified.comp B A (A ⧸ I)
  haveI : Algebra.FormallyUnramified (B ⧸ P) (A ⧸ I) :=
    Algebra.FormallyUnramified.of_restrictScalars B (B ⧸ P) (A ⧸ I)
  haveI : Algebra.EssFiniteType B (A ⧸ I) := Algebra.EssFiniteType.comp B A (A ⧸ I)
  haveI : Algebra.EssFiniteType (B ⧸ P) (A ⧸ I) := Algebra.EssFiniteType.of_comp B (B ⧸ P) (A ⧸ I)
  haveI : IsReduced (A ⧸ I) := Algebra.FormallyUnramified.isReduced_of_field (B ⧸ P) (A ⧸ I)
  intro x hx
  rw [← hrad] at hx
  obtain ⟨n, hn⟩ := hx
  have h0 : (Ideal.Quotient.mk I x) ^ n = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn
  have : Ideal.Quotient.mk I x = 0 := IsReduced.eq_zero _ ⟨n, h0⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximalStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.etale_unique_prime_le_map_maximal : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.Etale B A] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal A), (∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) → Q ≤ P.map (algebraMap B A) := by
  first | (exact @GlobalTheory.etale_prime_le_map_of_unique) | (exact GlobalTheory.etale_prime_le_map_of_unique) | (intros; apply GlobalTheory.etale_prime_le_map_of_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorInvolutionAlgebraProperties

section

@[expose] public section

namespace GlobalTheory

open IsLocalization in
theorem localFlat_dvd_descends : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ Q _ f b h
  set P : Ideal B := Q.comap (algebraMap B D) with hP
  let φ : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (algebraMap B D) rfl
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := φ.toAlgebra
  have hφ : ∀ x : B, φ (algebraMap B (Localization.AtPrime P) x) = algebraMap B (Localization.AtPrime Q) x := by
    intro x
    simp [φ, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
  have hfl : φ.Flat := RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) Q P rfl
  haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime Q) := hfl
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) :=
    (inferInstance : IsLocalHom φ)
  haveI : Module.FaithfullyFlat (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have key : algebraMap B (Localization.AtPrime P) b ∈
      (Ideal.span {f}).map (algebraMap B (Localization.AtPrime P)) := by
    rw [Ideal.map_span, Set.image_singleton,
      ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Localization.AtPrime Q)
        (Ideal.span {algebraMap B (Localization.AtPrime P) f}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton]
    change φ _ ∈ Ideal.span {φ _}
    rw [hφ, hφ]; exact h
  obtain ⟨s, hs, h2⟩ := (algebraMap_mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P) _ b).1 key
  exact ⟨s, hs, h2⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalizationMembership

section

@[expose] public section


theorem _root_.GlobalTheory.T.flat_localization_membership : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.localFlat_dvd_descends) | (exact GlobalTheory.localFlat_dvd_descends) | (intros; apply GlobalTheory.localFlat_dvd_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresUniqueAe

section

@[expose] public section

namespace GlobalTheory

theorem unitsMod_away_of_unique_prime (B D : Type) [CommRing B] [CommRing D] [Algebra B D]
    (f : B) (P : Ideal B) (Q : Ideal D) (g : D)
    (hQP : Q.comap (algebraMap B D) = P)
    (huniq : ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) :
    ∀ s : B, s ∉ P → ∃ t : Localization.Away g,
      algebraMap B (Localization.Away g) s * t - 1 ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
  intro s hs
  set A := Localization.Away g
  by_cases hI : Ideal.span {algebraMap B A s, algebraMap B A f} = ⊤
  · have h1 : (1 : A) ∈ Ideal.span {algebraMap B A s, algebraMap B A f} := by
      rw [hI]; exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h1
    refine ⟨a, ?_⟩
    have : algebraMap B A s * a - 1 = (-b) * algebraMap B A f := by
      rw [← hab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exfalso
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
    have hMp : (M.comap (algebraMap D A)).IsPrime := Ideal.comap_isPrime _ _
    have hf : algebraMap B D f ∈ M.comap (algebraMap D A) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hIM (Ideal.subset_span (by simp))
    have hg : g ∉ M.comap (algebraMap D A) := by
      intro hgM
      rw [Ideal.mem_comap] at hgM
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hgM
        (IsLocalization.Away.algebraMap_isUnit g))
    have hEq := huniq _ hMp hf hg
    apply hs
    rw [← hQP, Ideal.mem_comap, ← hEq, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hIM (Ideal.subset_span (by simp))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationInverseModF

section

@[expose] public section


theorem _root_.GlobalTheory.T.localization_inverse_mod_f : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (f : B) (P : Ideal B) (Q : Ideal D) (g : D), Q.comap (algebraMap B D) = P → (∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) → ∀ s : B, s ∉ P → ∃ t : Localization.Away g, algebraMap B (Localization.Away g) s * t - 1 ∈ Ideal.span {algebraMap B (Localization.Away g) f} := by
  first | (exact @GlobalTheory.unitsMod_away_of_unique_prime) | (exact GlobalTheory.unitsMod_away_of_unique_prime) | (intros; apply GlobalTheory.unitsMod_away_of_unique_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalization

section

@[expose] public section

namespace GlobalTheory

theorem etale_away_quotient_eq_localization :
    ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D]
      (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime →
      Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) →
      ∃ g : D, (∀ a : Localization.Away g, ∃ b : B,
          a - algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f}) ∧
        ∀ b : B, algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f} ↔
          ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ _ f hf P hP hfP Q hQ hQP hres

  have hQmax : Q.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => ?_, fun J x hQJ hx hxJ => ?_⟩
    · have : (1 : B) ∈ Q.comap (algebraMap B D) := by simpa using h1
      rw [hQP] at this
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
    · obtain ⟨b, hb⟩ := hres x
      have hbP : b ∉ P := by
        intro hbP
        apply hx
        have : algebraMap B D b ∈ Q := by
          rw [← Ideal.mem_comap, hQP]; exact hbP
        simpa using Q.add_mem hb this
      obtain ⟨c, hc⟩ : ∃ c : B, c * b - 1 ∈ P := by
        obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbP
        refine ⟨c, ?_⟩
        have : c * b - 1 = -i := by rw [← hci]; ring
        rw [this]; exact P.neg_mem hi
      have h1 : algebraMap B D (c * b - 1) ∈ Q := by
        rw [← Ideal.mem_comap, hQP]; exact hc
      have h2 : algebraMap B D c * x - 1 ∈ Q := by
        have : algebraMap B D c * x - 1 =
            algebraMap B D c * (x - algebraMap B D b) + algebraMap B D (c * b - 1) := by
          simp only [map_sub, map_mul, map_one]; ring
        rw [this]
        exact Q.add_mem (Q.mul_mem_left _ hb) h1
      have h3 : algebraMap B D c * x ∈ J := J.mul_mem_left _ hxJ
      have : (1 : D) = algebraMap B D c * x - (algebraMap B D c * x - 1) := by ring
      rw [this]
      exact J.sub_mem h3 (hQJ h2)
  obtain ⟨g, hgQ, hQ'⟩ := GlobalTheory.T.isolate_maximal_among_primes_containing_etale B D f hf Q hQmax
  refine ⟨g, ?_⟩
  haveI : Algebra.Etale D (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale B (Localization.Away g) := Algebra.Etale.comp B D (Localization.Away g)
  have hφ : ∀ b : B, algebraMap B (Localization.Away g) b =
      algebraMap D (Localization.Away g) (algebraMap B D b) := fun b =>
    IsScalarTower.algebraMap_apply B D (Localization.Away g) b

  have hunit := GlobalTheory.T.localization_inverse_mod_f B D f P Q g hQP hQ'

  have hker : ∀ b : B, (∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) →
      algebraMap B (Localization.Away g) b ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
    rintro b ⟨s, hs, hsb⟩
    obtain ⟨t, ht⟩ := hunit s hs
    have h1 : algebraMap B (Localization.Away g) (s * b) ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.mem_span_singleton] at hsb ⊢
      obtain ⟨c, hc⟩ := hsb
      exact ⟨algebraMap B _ c, by rw [hc, map_mul]⟩
    have : algebraMap B (Localization.Away g) b = algebraMap B _ (s * b) * t -
        (algebraMap B _ s * t - 1) * algebraMap B (Localization.Away g) b := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ ht)
  refine ⟨?_, fun b => ⟨fun hb => ?_, hker b⟩⟩
  ·
    obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
    have hPN : (P ^ N).map (algebraMap B (Localization.Away g)) ≤
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      exact hker b (hN b hb)
    have hfib : ∀ Q' : Ideal (Localization.Away g), Q'.IsPrime →
        P.map (algebraMap B (Localization.Away g)) ≤ Q' →
        Q' = Q.map (algebraMap D (Localization.Away g)) := by
      intro Q' hQ'p hPQ'
      have hc : Q'.comap (algebraMap D (Localization.Away g)) = Q := by
        apply hQ' _ (Ideal.comap_isPrime _ _)
        · rw [Ideal.mem_comap, ← hφ]
          exact hPQ' (Ideal.mem_map_of_mem _ hfP)
        · intro hg
          rw [Ideal.mem_comap] at hg
          exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hg
            (IsLocalization.Away.algebraMap_isUnit g))
      rw [← hc]
      exact (IsLocalization.map_under (Submonoid.powers g) (Localization.Away g) Q').symm
    have hle := GlobalTheory.T.etale_unique_prime_le_map_maximal B (Localization.Away g) P hP
      (Q.map (algebraMap D (Localization.Away g))) hfib
    have hres' := GlobalTheory.T.localization_residue_approximation B D P hP Q g hgQ hQP hres
    refine GlobalTheory.T.nilpotent_approximation_surjective B (Localization.Away g) P _ N (fun a => ?_) hPN
    obtain ⟨b, hb⟩ := hres' a
    exact ⟨b, Ideal.mem_sup_left (hle hb)⟩
  ·
    have hgu : IsUnit (algebraMap D (Localization.AtPrime Q) g) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨g, hgQ⟩ : Q.primeCompl)
    let ρ : Localization.Away g →+* Localization.AtPrime Q := IsLocalization.Away.lift g hgu
    have hρ : ∀ d : D, ρ (algebraMap D (Localization.Away g) d) =
        algebraMap D (Localization.AtPrime Q) d :=
      fun d => IsLocalization.Away.lift_eq g hgu d
    have e : ∀ x : B, algebraMap B (Localization.AtPrime Q) x =
        ρ (algebraMap B (Localization.Away g) x) := by
      intro x
      rw [hφ, hρ, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
    have hloc : algebraMap B (Localization.AtPrime Q) b ∈
        Ideal.span {algebraMap B (Localization.AtPrime Q) f} := by
      rw [Ideal.mem_span_singleton] at hb ⊢
      obtain ⟨c, hc⟩ := hb
      exact ⟨ρ c, by rw [e, e, hc, map_mul]⟩
    obtain ⟨s, hs, hsb⟩ := GlobalTheory.T.flat_localization_membership B D Q f b hloc
    rw [hQP] at hs
    exact ⟨s, hs, hsb⟩

end GlobalTheory
end
end
