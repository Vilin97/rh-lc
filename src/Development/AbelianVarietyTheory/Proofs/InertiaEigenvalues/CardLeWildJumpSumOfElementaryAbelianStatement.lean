module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMemStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.RamificationStructure
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.LocalFields.UpperNumbering
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ringChar_residue_eq_of_ordIs (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e : ℕ) (hp : p.Prime) (he : 0 < e) (h : OrdIs F p e) :
    ringChar 𝓀[F] = p := by
  have hnu : ¬ IsUnit (p : 𝒪[F]) := by
    intro hu
    have := (IsDiscreteValuationRing.addVal_eq_zero_of_unit (hu.unit))
    unfold OrdIs at h
    simp at this
    rw [this] at h
    norm_cast at h
    omega
  have hm : (p : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := hnu
  have h0 : ((p : ℕ) : 𝓀[F]) = 0 := by
    rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
    exact hm
  have hd : ringChar 𝓀[F] ∣ p := (ringChar.spec 𝓀[F] p).mp h0
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem upperRamificationGroup_one_eq_top_of_exponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M]
      [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M]
      [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e →
      upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e hp he hord h0 hexp
  rw [upperRamificationGroup_zero] at h0
  have hchar := ringChar_residue_eq_of_ordIs F p e hp he hord
  have hcop := coprime_card_lowerRamificationGroup_zero_quotient F M
  rw [hchar] at hcop
  have h1 : lowerRamificationGroup F M 1 = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have hσ0 : σ ∈ lowerRamificationGroup F M 0 := by rw [h0]; trivial
    set q : lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0) :=
      QuotientGroup.mk ⟨σ, hσ0⟩ with hq
    have hqp : q ^ p = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨σ, hσ0⟩ : lowerRamificationGroup F M 0) ^ p = 1 := Subtype.ext (by simpa using hexp σ)
      rw [this, QuotientGroup.mk_one]
    have hqc : q ^ Nat.card (lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0)) = 1 := pow_card_eq_one'
    have hg : q ^ Nat.gcd _ p = 1 := pow_gcd_eq_one.mpr ⟨hqc, hqp⟩
    rw [hcop, pow_one, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg
    exact hg
  have hphi0 : herbrandPhi F M 0 = 0 := by simp [herbrandPhi]
  have hphi1 : herbrandPhi F M 1 = 1 := by
    have := herbrandPhi_of_mem_Icc (K := F) (L := M) 0 (u := 1) (by norm_num)
    have h1' : lowerRamificationGroup F M (((0 : ℕ) : ℤ) + 1) = ⊤ := by simpa using h1
    rw [h1', Subgroup.relIndex_top_left] at this
    simpa [hphi0] using this
  rw [← hphi1, upperRamificationGroup_herbrandPhi, ← Nat.cast_one, lowerRamificationGroupReal_natCast]
  simpa using h1
end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.upperRamificationGroup_one_eq_top_of_exponent_prime : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e → upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  first | exact @GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent | exact GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent | (intros; apply GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumTotallyRamified

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_jumpSum_wild_of_exponent :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E →
      lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) →
      (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ B) → B ≠ ⊤ → Nat.card (L ≃ₐ[F] L) ≤ jumpSum (wild F L) ⊤ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B hp hE h0 hord hcomm hpow hB
  have hBn : B.Normal := ⟨fun b hb σ => by
    have h := B.mul_mem (hcomm σ b) hb
    simpa [mul_assoc] using h⟩
  set M := IntermediateField.fixedField B
  have hker : (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) M).ker = B := by
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) L
  obtain ⟨e, hordF, hEe, -⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hord
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    · exact h
  have hM0 : upperRamificationGroup F M 0 = ⊤ := by
    rw [← map_upperRamificationGroup M 0, upperRamificationGroup_zero, h0, Subgroup.map_top_of_surjective _ hsurj]
  have hMexp : ∀ s : M ≃ₐ[F] M, s ^ p = 1 := by
    intro s
    obtain ⟨σ, rfl⟩ := hsurj s
    rw [← map_pow, ← MonoidHom.mem_ker, hker]
    exact hpow σ
  have hM1 := GlobalTheory.T.upperRamificationGroup_one_eq_top_of_exponent_prime F M p e hp he hordF hM0 hMexp
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ ∉ B := by
    by_contra h
    push_neg at h
    exact hB (eq_top_iff.mpr fun x _ => h x)
  have hmem : AlgEquiv.restrictNormalHom M σ₀ ∈ (upperRamificationGroup F L 1).map (AlgEquiv.restrictNormalHom M) := by
    rw [map_upperRamificationGroup M 1, hM1]; trivial
  obtain ⟨σ, hσ, hσe⟩ := hmem
  have hσB : σ ∉ B := by
    intro hσB
    apply hσ₀
    rw [← hker, MonoidHom.mem_ker, ← hσe, ← MonoidHom.mem_ker, hker]
    exact hσB
  have := GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem F L B 1 h0 σ hσ hσB
  rw [mul_one] at this
  exact_mod_cast this

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumTotallyRamifiedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.card_le_wild_jumpSum_totallyRamified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ B) → B ≠ ⊤ → Nat.card (L ≃ₐ[F] L) ≤ jumpSum (wild F L) ⊤ B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjectiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.ramificationJumpSum_comap_injective : ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j → jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_comap_injective | exact GlobalTheory.PMon.Ram.jumpSum_comap_injective | (intros; apply GlobalTheory.PMon.Ram.jumpSum_comap_injective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelian

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_jumpSum_wild :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B hp hE hA hord hcomm hpow hnot
  obtain ⟨j, hj, hrange, -, hram⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A
  have hmemA : ∀ σ, j σ ∈ A := fun σ => hrange.le ⟨σ, rfl⟩
  have htop : lowerRamificationGroup (IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hram, eq_top_iff]
    intro σ _
    exact hA (hmemA σ)
  have hcomm' : ∀ σ τ : L ≃ₐ[IntermediateField.fixedField A] L,
      σ * τ * σ⁻¹ * τ⁻¹ ∈ B.comap j := by
    intro σ τ
    rw [Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ (hmemA σ) _ (hmemA τ)
  have hpow' : ∀ σ : L ≃ₐ[IntermediateField.fixedField A] L, σ ^ p ∈ B.comap j := by
    intro σ
    rw [Subgroup.mem_comap, map_pow]
    exact hpow _ (hmemA σ)
  have hne : B.comap j ≠ ⊤ := by
    intro h
    apply hnot
    intro a ha
    obtain ⟨σ, rfl⟩ := hrange.ge ha
    have : σ ∈ B.comap j := h ▸ Subgroup.mem_top σ
    exact this
  have key := GlobalTheory.T.card_le_wild_jumpSum_totallyRamified (IntermediateField.fixedField A) L p E (B.comap j) hp hE htop hord
    hcomm' hpow' hne
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  have hcard : Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) = Nat.card ↥A := by
    exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).trans
      (congrArg (fun H : Subgroup (L ≃ₐ[K] L) => Nat.card ↥H) hrange)
  have hjs : jumpSum (wild K L) A B =
      jumpSum (wild (IntermediateField.fixedField A) L) ⊤ (B.comap j) := by
    rw [hwild, GlobalTheory.T.ramificationJumpSum_comap_injective _ _ j (wild K L) B hj]
    exact congrArg (fun H => jumpSum (wild K L) H B) hrange.symm
  calc Nat.card ↥A = Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) := hcard.symm
    _ ≤ _ := key
    _ = jumpSum (wild K L) A B := hjs.symm

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelianStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.card_le_wildJumpSum_of_elementaryAbelian : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild <;> assumption)
end
end
