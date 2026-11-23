module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemidirectCharacterExtOfStableStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCard
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRestrictedCharacterInIsotypicPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingleStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetCharacterOrthZero

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetOrth

def twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) : Representation ℂ H V where
  toFun x := ((η x : ℂ) ^ a) • ρ x
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, Units.val_mul, mul_pow, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_comm]

theorem trace_twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) (x : H) :
    LinearMap.trace ℂ V (twist η a ρ x) = LinearMap.trace ℂ V (ρ x) * (η x : ℂ) ^ a := by
  show LinearMap.trace ℂ V (((η x : ℂ) ^ a) • ρ x) = _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem sum_trace_mul_star_nat {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ H W) :
    ∃ k : ℕ, ∑ x, LinearMap.trace ℂ V (ρ x) * star (LinearMap.trace ℂ W (σ x)) = (Nat.card H : ℂ) * k := by
  have hne : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hne
  have h := FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of σ) (FDRep.of ρ)
  refine ⟨Module.finrank ℂ (FDRep.of σ ⟶ FDRep.of ρ), ?_⟩
  rw [← h, mul_inv_cancel_left₀ hne]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.BadShare.ZCalc.character_inv]
  rfl

end GlobalTheory.Shin.CosetOrth

open GlobalTheory.Shin.CosetOrth in
theorem GlobalTheory.Shin.finsum_coset_mul_star_eq_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  intro G Γ _ _ _ _ φ s hp hs X Y hX hY h0
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have gen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hl0 : Nat.card Γ ≠ 0 := hp.ne_zero
  obtain ⟨η, -, -, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s gen _ (Complex.isPrimitiveRoot_exp _ hl0)
  obtain ⟨e1, e2⟩ := hF X Y
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  letI : Fintype (G ⋊[φ] Γ) := Fintype.ofFinite _
  have hm : ∀ a : ℕ, ∃ k : ℕ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = (Nat.card (G ⋊[φ] Γ) : ℂ) * k := by
    intro a
    obtain ⟨n, ρ, hρ⟩ := hX
    obtain ⟨m, σ, hσ⟩ := hY
    obtain ⟨k, hk⟩ := sum_trace_mul_star_nat ρ (twist η a σ)
    refine ⟨k, ?_⟩
    rw [finsum_eq_sum_of_fintype, ← hk]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [trace_twist, hρ x, hσ x]
    rfl
  choose k hk using hm
  have hH : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsum : ∑ a ∈ Finset.range (Nat.card Γ), k a = 0 := by
    rw [h0, mul_zero] at e1
    simp_rw [hk] at e1
    rw [← Finset.mul_sum] at e1
    have := (mul_eq_zero.mp e1.symm).resolve_left hH
    exact_mod_cast this
  have hk0 : ∀ a ∈ Finset.range (Nat.card Γ), k a = 0 := Finset.sum_eq_zero_iff.mp hsum
  have hR : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hk a, hk0 a ha]; simp
  rw [hR] at e2
  exact (mul_eq_zero.mp e2).resolve_left (by exact_mod_cast hl0)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetCharacterOrthZeroStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.finsum_semidirect_coset_character_orth_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (exact GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_mul_star_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclicStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  first | (exact @GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (exact GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (intros; apply GlobalTheory.Shin.CosetFourier.fourier_coset_sums  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetPairingNeZero

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_coset_pair_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  intro G Γ _ _ _ _ φ s hp hs X hX Y hY z hz hnd hcos
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, -, -, hfour⟩ := GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic G Γ φ s hgen _ hζ
  obtain ⟨h1, h2⟩ := hfour X Y
  have hvirt : ∀ a : ℕ, (fun x => Y x * (η x : ℂ) ^ a) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    intro a
    obtain ⟨hmul, -, -, -, hlin⟩ := GlobalTheory.BI.virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
    have := hmul Y hY _ (hlin (η ^ a))
    convert this using 1
  have hm : ∀ a : ℕ, ∃ m : ℤ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = m * (Nat.card (G ⋊[φ] Γ) : ℂ) :=
    fun a => GlobalTheory.BI.finsum_mul_star_virt_int _ X _ hX (hvirt a)
  choose m hm using hm
  have hN : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hl : (Nat.card Γ : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [hm, hN, hcos, hz, mul_zero] at h1 h2
  have hsum : ∑ i : Fin (Nat.card Γ), (m i.val : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ i.val = 0 := by
    have h3 : ∑ a ∈ Finset.range (Nat.card Γ), (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a * (↑(m a) * ↑(Nat.card G * Nat.card Γ))
        = (∑ a ∈ Finset.range (Nat.card Γ), (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a) * ((Nat.card G : ℂ) * Nat.card Γ) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; push_cast; ring
    rw [h3] at h2
    rw [← Finset.sum_range (fun a => (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a)]
    have := h2.symm
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (mul_ne_zero hG hl)
  have hall := (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int hp hζ (fun i => m i.val)).1 hsum
  have hconst : ∀ a ∈ Finset.range (Nat.card Γ), m a = m 0 := by
    intro a ha
    exact hall ⟨a, Finset.mem_range.1 ha⟩ ⟨0, hp.pos⟩
  rw [Finset.sum_congr rfl (fun a ha => by rw [hconst a ha])] at h1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hz' : (z : ℂ) = (m 0 * Nat.card Γ : ℤ) := by
    push_cast at h1 ⊢
    have h4 : (Nat.card Γ : ℂ) * (Nat.card G : ℂ) * ((z : ℂ) - m 0 * Nat.card Γ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (mul_ne_zero hl hG)
    · exact sub_eq_zero.1 h
  exact hnd ⟨m 0, by rw [mul_comm]; exact_mod_cast hz'⟩

end GlobalTheory.Shin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumSemidirectCosetPairingNeZeroStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.finsum_semidirect_coset_pairing_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_pair_ne_zero) | (exact GlobalTheory.Shin.finsum_coset_pair_ne_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_pair_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupport

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem kills_const_mul {G : Type} [Group G] [Finite G] (c : ℂ) (f Y : G → ℂ) (h : Kills f Y) :
    Kills (fun g => c * f g) Y := by
  intro V _ _ _ ρ hY
  have hk := h V ρ hY
  have : Fintype G := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype] at hk ⊢
  have e : (fun g => star (c * f g) • ρ g) = fun g => star c • (star (f g) • ρ g) := by
    funext g; rw [star_mul', mul_smul]
  simp only []
  rw [e, ← Finset.smul_sum, hk, smul_zero]

theorem kills_of_norm_one_of_pairing_prime :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime →
      s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
      ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ,
      ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) →
      Kills (fun δ => X (inl δ * inr s)) Y := by
  intro G Γ _ _ _ _ φ s hp hs X hX hn Y hY hYs z hz hl
  obtain ⟨χ, e, hχ, hχG, hXe⟩ := GlobalTheory.T.virtualCharacter_coset_normOne_single G Γ φ s hp hs X hX hn
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    rw [zpowers_eq_top_of_prime_card rfl hs]
    exact Subgroup.mem_top t
  obtain ⟨Z, hZ, hZY⟩ := GlobalTheory.T.exists_semidirect_character_ext_of_stable G Γ φ s hgen Y hY hYs
  have hZv : Z ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hZ
  have hXZ : ∑ᶠ g, X (inl g) * star (Z (inl g)) = z * (Nat.card G : ℂ) := by
    simp only [hZY]; exact hz
  have hc := GlobalTheory.T.finsum_semidirect_coset_pairing_ne_zero G Γ φ s hp hs X hX Z hZv z hXZ hl
  have hχc : ∑ᶠ g, χ (inl g * inr s) * star (Z (inl g * inr s)) ≠ 0 := by
    intro h0
    apply hc
    have : (fun g => X (inl g * inr s) * star (Z (inl g * inr s)))
        = fun g => e * (χ (inl g * inr s) * star (Z (inl g * inr s))) := by
      funext g; rw [hXe, mul_assoc]
    rw [this, ← mul_finsum, h0, mul_zero]
  have hχchar : IsChar ℂ ℂ χ := by
    obtain ⟨n, ρ, -, h⟩ := hχ; exact ⟨n, ρ, h⟩
  have hχY : ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 := by
    intro h0
    apply hχc
    apply GlobalTheory.T.finsum_semidirect_coset_character_orth_zero G Γ φ s hp hs χ Z hχchar hZ
    simp only [hZY]; exact h0
  have hK := GlobalTheory.T.twisted_restricted_character_in_isotypic_part G Γ φ s χ Y hχchar hχG hY hχY
  have := kills_const_mul e _ Y hK
  simpa only [hXe] using this

end GlobalTheory.Shin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupportStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_virtualCharacter_norm_one_support : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → Kills (fun δ => X (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (exact GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (intros; apply GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime  <;> assumption)
end
end
