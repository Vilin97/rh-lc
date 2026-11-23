module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterIrreducibleExpansionNormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CliffordSemidirectPrimeIndexIrreducibleCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzeroStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwist

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.CliffTwo

def twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) : Representation ℂ H V where
  toFun x := ((ν x : ℂˣ) : ℂ) • ρ x
  map_one' := by simp
  map_mul' x y := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistRep_apply {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) (x : H) : twistRep ρ ν x = ((ν x : ℂˣ) : ℂ) • ρ x := rfl

theorem isIrreducible_twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (h : ρ.IsIrreducible) (ν : H →* ℂˣ) :
    (twistRep ρ ν).IsIrreducible := by
  let f : Subrepresentation (twistRep ρ ν) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((ν g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [twistRep_apply, smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact f.isSimpleOrder_iff.2 h

theorem isIrrChar_mul_char {H : Type} [Group H] {χ : H → ℂ} (hχ : IsIrrChar ℂ ℂ χ) (ν : H →* ℂˣ) :
    IsIrrChar ℂ ℂ (fun x => χ x * ((ν x : ℂˣ) : ℂ)) := by
  obtain ⟨n, ρ, hρ, hc⟩ := hχ
  refine ⟨n, twistRep ρ ν, isIrreducible_twistRep hρ ν, fun g => ?_⟩
  simp only [hc, Representation.character, twistRep_apply, map_smul, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

end GlobalTheory.CliffTwo


open GlobalTheory.CliffTwo in
theorem GlobalTheory.Shin.coset_pair_eq_zero_or_twist :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' →
    ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨
      ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  intro G Γ _ _ _ _ φ s hp hs χ χ' hχ hχ'
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ (SemidirectProduct.equivProd (φ := φ)).symm
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, hη1, -, hsum⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  have hS := (hsum χ χ').2
  by_cases h0 : ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0
  · exact Or.inl h0
  right
  have hne : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := by
    rw [← hS]; exact mul_ne_zero (by exact_mod_cast hp.ne_zero) h0
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hT : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := right_ne_zero_of_mul ha
  have hpow : ∀ x, ((η ^ a) x : ℂ) = (η x : ℂ) ^ a := fun x => by simp
  have hψ : IsIrrChar ℂ ℂ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) := isIrrChar_mul_char hχ' (η ^ a)
  refine ⟨η ^ a, fun g => by simp [hη1], fun x => ?_⟩
  by_contra hx
  have hne' : χ ≠ fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ) := fun e => hx (congrFun e x)
  have hpair : pair χ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) = 0 := by
    first | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne (G ⋊[φ] Γ) χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne hχ hψ hne'
  have hvirt : (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    obtain ⟨n, ρ, -, hc⟩ := hψ
    exact AddSubgroup.subset_closure ⟨n, ρ, hc⟩
  have hstar : ∀ g, star ((fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g) = (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g⁻¹ := by
    first | exact GlobalTheory.CuspGL.star_virt_eq_inv (G ⋊[φ] Γ) _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv hvirt
  apply hT
  have hcard : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) =
      ∑ᶠ x, χ x * (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) x⁻¹ := by
    congr 1; ext x; have hx := hstar x; simp only [hpow] at hx ⊢; rw [← hx]
  rw [this]
  unfold pair at hpair
  exact (mul_eq_zero.1 hpair).resolve_left (inv_ne_zero hcard)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwistStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' → ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨ ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  first | (exact @GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (exact GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (intros; apply GlobalTheory.Shin.coset_pair_eq_zero_or_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingle

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem int_comb_unit_norm_single {ι G : Type} [Fintype ι] [Fintype G] (l : ℕ) (hl : l.Prime)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ l) (f : ι → G → ℂ) (c : ι → ℤ) (R : ι → ι → Prop)
    (hR : Equivalence R) (hG : (Fintype.card G : ℂ) ≠ 0)
    (hnorm : ∀ i, ∑ g, f i g * star (f i g) = Fintype.card G)
    (horth : ∀ i j, ∑ g, f i g * star (f j g) ≠ 0 → R i j)
    (hrel : ∀ i j, R i j → ∃ a < l, ∀ g, f i g = ζ ^ a * f j g)
    (hsum : ∑ g, (∑ i, (c i : ℂ) * f i g) * star (∑ i, (c i : ℂ) * f i g) = Fintype.card G) :
    ∃ i₀ e, ∀ g, ∑ i, (c i : ℂ) * f i g = e * f i₀ g := by
  letI S : Setoid ι := ⟨R, hR⟩
  let rep : Quotient S → ι := Quotient.out
  have hrep : ∀ t : ι, R t (rep ⟦t⟧) := fun t => hR.symm (Quotient.mk_out t)
  choose a ha hfa using fun t => hrel t _ (hrep t)
  let n : Quotient S → ℕ → ℤ := fun i b => ∑ t, if (⟦t⟧ : Quotient S) = i ∧ a t = b then c t else 0
  let C : Quotient S → ℂ := fun i => ∑ b ∈ Finset.range l, (n i b : ℂ) * ζ ^ b
  have hF : ∀ g, ∑ t, (c t : ℂ) * f t g = ∑ i, C i * f (rep i) g := by
    intro g
    have h1 : ∀ i, C i * f (rep i) g =
        ∑ t, if (⟦t⟧ : Quotient S) = i then (c t : ℂ) * (ζ ^ a t * f (rep i) g) else 0 := by
      intro i
      simp only [C, n, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : (⟦t⟧ : Quotient S) = i
      · simp only [h, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_range, ha t, if_true]
        ring
      · simp [h]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp [hfa t g]
  have hort : ∀ i j, i ≠ j → ∑ g, f (rep i) g * star (f (rep j) g) = 0 := by
    intro i j hij
    by_contra h
    apply hij
    rw [← Quotient.out_eq i, ← Quotient.out_eq j]
    exact Quotient.sound (horth _ _ h)
  have hexp : ∀ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      ∑ i, ∑ j, C i * star (C j) * (f (rep i) g * star (f (rep j) g)) := by
    intro g
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have h2 : ∑ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      (∑ i, C i * star (C i)) * Fintype.card G := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · rw [← Finset.mul_sum, hnorm]
    · intro j _ hji
      rw [← Finset.mul_sum, hort i j (Ne.symm hji), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [hF] at hsum
  rw [h2] at hsum
  have h3 : ∑ i, C i * star (C i) = 1 := by
    have := hsum
    rw [← one_mul (Fintype.card G : ℂ)] at this
    exact mul_right_cancel₀ hG (by simpa using this)
  obtain ⟨i₀, -, hi₀⟩ := GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero l ζ hl hζ (Quotient S) Finset.univ n h3
  refine ⟨rep i₀, C i₀, fun g => ?_⟩
  rw [hF, Finset.sum_eq_single i₀]
  · intro i _ hi
    have : C i = 0 := hi₀ i (Finset.mem_univ i) hi
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i₀) h

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem virt_coset_norm_one_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ]
    (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ),
    ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
    ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
      ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  intro G Γ _ _ _ _ φ s hp hs X hX hXn
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) :=
    Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right))
      (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  obtain ⟨c, hirr, hXc, -⟩ := GlobalTheory.BI.virt_expand (G ⋊[φ] Γ) X hX
  let T := c.support.filter (fun χ : G ⋊[φ] Γ → ℂ => ¬ ∀ δ, χ (inl δ * inr s) = 0)
  have hT : ∀ t : T, IsIrrChar ℂ ℂ t.1 ∧ ¬ ∀ δ, t.1 (inl δ * inr s) = 0 := fun t =>
    ⟨hirr _ (Finset.mem_filter.1 t.2).1, (Finset.mem_filter.1 t.2).2⟩
  let f : T → G → ℂ := fun t g => t.1 (inl g * inr s)
  have hX' : ∀ g, X (inl g * inr s) = ∑ t : T, (c t.1 : ℂ) * f t g := by
    intro g
    rw [hXc, Finsupp.sum, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    rw [Finset.sum_coe_sort T (fun χ => (c χ : ℂ) * χ (inl g * inr s))]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    split_ifs with h
    · rw [h g, mul_zero]
    · rfl
  let R : T → T → Prop := fun t u => ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧
    ∀ x, t.1 x = u.1 x * (η x : ℂ)
  have hR : Equivalence R := by
    refine ⟨fun t => ⟨1, fun g => rfl, fun x => by simp⟩, ?_, ?_⟩
    · rintro t u ⟨η, h1, h2⟩
      refine ⟨η⁻¹, fun g => by simp [h1 g], fun x => ?_⟩
      rw [h2 x, MonoidHom.inv_apply, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]
    · rintro t u v ⟨η, h1, h2⟩ ⟨η', h1', h2'⟩
      refine ⟨η' * η, fun g => by simp [h1 g, h1' g], fun x => ?_⟩
      rw [h2 x, h2' x, MonoidHom.mul_apply, Units.val_mul, mul_assoc]
  haveI : NeZero (Nat.card Γ) := ⟨hp.ne_zero⟩
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  have hnorm : ∀ t, ∑ g, f t g * star (f t g) = Fintype.card G := by
    intro t
    rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t.1 (hT t).1 with h | ⟨-, h⟩
    · exact absurd h (hT t).2
    · rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at h
      exact h
  have horth : ∀ t u, ∑ g, f t g * star (f u g) ≠ 0 → R t u := by
    intro t u h
    rcases GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist G Γ φ s hp hs t.1 u.1 (hT t).1 (hT u).1 with h' | h'
    · rw [finsum_eq_sum_of_fintype] at h'
      exact absurd h' h
    · exact h'
  have hrel : ∀ t u, R t u → ∃ a < Nat.card Γ, ∀ g,
      f t g = Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) ^ a * f u g := by
    rintro t u ⟨η, h1, h2⟩
    have hpow : ((η (inr s) : ℂˣ) : ℂ) ^ Nat.card Γ = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one,
        Units.val_one]
    obtain ⟨a, ha, hb⟩ := hζ.eq_pow_of_pow_eq_one hpow
    refine ⟨a, ha, fun g => ?_⟩
    simp only [f]
    rw [h2, map_mul, h1, one_mul, hb, mul_comm]
  have hsum : ∑ g, (∑ t : T, (c t.1 : ℂ) * f t g) * star (∑ t : T, (c t.1 : ℂ) * f t g) =
      Fintype.card G := by
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at hXn
    simp_rw [← hX']
    exact hXn
  obtain ⟨t₀, e, he⟩ := int_comb_unit_norm_single (Nat.card Γ) hp _ hζ f (fun t => c t.1) R hR
    (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hnorm horth hrel hsum
  refine ⟨t₀.1, e, (hT t₀).1, ?_, fun δ => by rw [hX', he]⟩
  rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t₀.1 (hT t₀).1 with h | ⟨h, -⟩
  · exact absurd h (hT t₀).2
  · exact h

end GlobalTheory.Shin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingleStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.virtualCharacter_coset_normOne_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧ ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  first | (exact @GlobalTheory.Shin.virt_coset_norm_one_single) | (exact GlobalTheory.Shin.virt_coset_norm_one_single) | (intros; apply GlobalTheory.Shin.virt_coset_norm_one_single <;> assumption)
end
end
