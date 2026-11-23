module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AicValOfIsColim
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FaceFaceApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofaceRel
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
import Mathlib.RingTheory.WittVector.IsPoly
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CancelLTensor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofaceRel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompletionComplete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovOfAlgHom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectedSystemTrR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConstOfRhoEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsWP
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKill
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPQ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRetraction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplExistsUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPowSmulTopIff
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Away.Basic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneTmulMemRangeIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfOfIsCompl
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PqBaseChangePolynomial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PqLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeftEqRTensor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMemRangeLTensorOfLTensorEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SolvAtStage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPunitEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TmulEqZeroOfMemSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitTZpow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WpHomotopy
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WpPf

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AltAlt

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpCoface

theorem alt_alt (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type)
    [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n))
    (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))) (hwp : ∀ n, IsWP (ι n))
    (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) (n : ℕ) (z : K n) :
    alt (δ (n + 1)) (alt (δ n) z) = 0 := by
  have hrel : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)),
      δ (n + 1) (j.succAbove i) (δ n (i.predAbove j) z) = δ (n + 1) j (δ n i z) := fun j i =>
    DFunLike.congr_fun (coface_rel A B K ι δ hwp hδ n j i) z
  have hexp : alt (δ (n + 1)) (alt (δ n) z) = ∑ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (p.1 : ℕ) * (-1 : ℤ) ^ (p.2 : ℕ)) • δ (n + 1) p.1 (δ n p.2 z) := by
    rw [Fintype.sum_prod_type]

    simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
    map_zsmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    rw [hrel, GlobalTheory.CatH.DSq.sign_swap, neg_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ _ h
    exact Fin.succAbove_ne j i (congrArg Prod.fst h)
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨j, i⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

end GlobalTheory.CompanionTheory.WpCoface
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveAlgebraMapZero

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Coproduct

theorem bijective_algebraMap_zero {A B K : Type} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] {ι : Fin 0 → (B →ₐ[A] K)} (h : IsWP ι) :
    Function.Bijective (algebraMap A K) := by
  obtain ⟨z, hz, -⟩ := h.ex A (RingHom.id A) (fun i => i.elim0) (fun i => i.elim0)
  have hzx : ∀ a, z (algebraMap A K a) = a := fun a => by
    simpa using congrArg (fun f : A →+* A => f a) hz
  have hid : (algebraMap A K).comp z = RingHom.id K := by
    refine h.uniq K _ _ ?_ (fun i => i.elim0)
    ext a
    simp [hzx]
  refine Function.bijective_iff_has_inverse.mpr ⟨z, hzx, fun k => ?_⟩
  simpa using congrArg (fun f : K →+* K => f k) hid

theorem bijective_one {A B K : Type} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] {ι : Fin 1 → (B →ₐ[A] K)} (h : IsWP ι) :
    Function.Bijective (ι 0) := by
  obtain ⟨z, hz, hy⟩ := h.ex B (algebraMap A B) (fun _ => RingHom.id B)
    (fun _ => RingHom.id_comp _)
  have hzi : ∀ b, z (ι 0 b) = b := fun b => by
    simpa using congrArg (fun f : B →+* B => f b) (hy 0)
  have hza : ∀ a, z (algebraMap A K a) = algebraMap A B a := fun a => by
    simpa using congrArg (fun f : A →+* B => f a) hz
  have hid : ((ι 0 : B →ₐ[A] K) : B →+* K).comp z = RingHom.id K := by
    refine h.uniq K _ _ ?_ (fun i => ?_)
    · ext a
      simp [hza]
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      ext b
      simp [hzi]
  refine Function.bijective_iff_has_inverse.mpr ⟨z, hzi, fun k => ?_⟩
  simpa using congrArg (fun f : K →+* K => f k) hid

theorem exists_coface {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (h : ∀ n, IsWP (ι n)) :
    ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)),
      ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := by
  have key : ∀ (n : ℕ) (k : Fin (n + 1)), ∃ d : K n →ₐ[A] K (n + 1),
      ∀ i, d.comp (ι n i) = ι (n + 1) (k.succAbove i) := by
    intro n k
    obtain ⟨z, hz, hy⟩ := (h n).ex (K (n + 1)) (algebraMap A (K (n + 1)))
      (fun i => (ι (n + 1) (k.succAbove i) : B →+* K (n + 1)))
      (fun i => by ext a; simp)
    refine ⟨{ z with commutes' := fun a => congrArg (fun f : A →+* K (n + 1) => f a) hz },
      fun i => ?_⟩
    ext b
    exact congrArg (fun f : B →+* K (n + 1) => f b) (hy i)
  choose δ hδ using key
  exact ⟨δ, hδ⟩

theorem coproduct_low_and_coface : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)), (∀ n, IsWP (ι n)) → Function.Bijective (algebraMap A (K 0)) ∧ Function.Bijective (ι 1 0) ∧ ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)), ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := by
  intro A _ B _ _ K _ _ ι h
  exact ⟨bijective_algebraMap_zero (h 0), bijective_one (h 1), exists_coface K ι h⟩

end GlobalTheory.CompanionTheory.Coproduct
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaurentEqToLaurentSubInvert

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem laurent_eq_toLaurent_sub_invert {K : Type} [CommRing K] (h : K[T;T⁻¹]) :
    ∃ α β : Polynomial K, h = Polynomial.toLaurent α -
      LaurentPolynomial.invert (Polynomial.toLaurent β) := by
  induction h using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨α₁, β₁, rfl⟩ := hf
    obtain ⟨α₂, β₂, rfl⟩ := hg
    refine ⟨α₁ + α₂, β₁ + β₂, ?_⟩
    simp only [map_add (f := _)]
    ring
  | C_mul_T n a =>
    rcases le_total 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      refine ⟨Polynomial.monomial m a, 0, ?_⟩
      simp [Polynomial.toLaurent_C_mul_T]
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hn)
      refine ⟨0, -Polynomial.monomial m a, ?_⟩
      have hn' : n = -(m : ℤ) := by omega
      subst hn'
      simp [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_T,
        LaurentPolynomial.invert_C]

theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ _ h₁ h₂ h₃ e₁ e₂ y
  obtain ⟨k, h, hy⟩ := h₃.pow y
  obtain ⟨α, β, rfl⟩ := laurent_eq_toLaurent_sub_invert h
  obtain ⟨-, -, root₁, -, -⟩ := pf_facts p K₁ h₁.pf
  obtain ⟨-, -, root₂, -, -⟩ := pf_facts p K₂ h₂.pf
  obtain ⟨-, -, -, inj₃, -⟩ := pf_facts p K₃ h₃.pf
  obtain ⟨b₁, hb₁⟩ := root₁ k (i₁ α)
  obtain ⟨b₂, hb₂⟩ := root₂ k (i₂ β)
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K₃ h₃.pf.char k
  refine ⟨b₁, b₂, inj₃ k _ _ ?_⟩
  have key : (ρ₁ b₁ - ρ₂ b₂) ^ p ^ k = ρ₁ (b₁ ^ p ^ k) - ρ₂ (b₂ ^ p ^ k) := by
    rw [← hF (ρ₁ b₁ - ρ₂ b₂), map_sub F, hF, hF, map_pow, map_pow]
  rw [hy, key, hb₁, hb₂, e₁, e₂, map_sub]

end GlobalTheory.CompanionTheory.PerfectRing
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqZeroOfCPowMemSpan

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem mul_eq_zero_of_C_pow_mem_span (K : Type) [CommRing K]
    (hred : ∀ (x : K) (n : ℕ), x ^ n = 0 → x = 0) (f g a : K) (n : ℕ)
    (h : (Polynomial.C a) ^ n ∈
      Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) : g * a = 0 := by
  let L := Localization.Away g
  let u : L := IsLocalization.Away.invSelf g
  have hu : algebraMap K L g * u = 1 := IsLocalization.Away.mul_invSelf g
  let φ : Polynomial K →+* L := Polynomial.eval₂RingHom (algebraMap K L) (u * algebraMap K L f)
  have h0 : φ (Polynomial.C f - Polynomial.X * Polynomial.C g) = 0 := by
    have e1 : φ (Polynomial.C f) = algebraMap K L f := by simp [φ]
    have e2 : φ Polynomial.X = u * algebraMap K L f := by simp [φ]
    have e3 : φ (Polynomial.C g) = algebraMap K L g := by simp [φ]
    rw [map_sub, map_mul, e1, e2, e3]
    linear_combination (-(algebraMap K L f)) * hu
  have h1 : φ ((Polynomial.C a) ^ n) = 0 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hc, map_mul, h0, mul_zero]
  have h2 : algebraMap K L (a ^ n) = 0 := by
    have e : φ ((Polynomial.C a) ^ n) = algebraMap K L (a ^ n) := by simp [φ]
    rw [← e, h1]
  obtain ⟨⟨m, hm⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) L _).1 h2
  obtain ⟨M, rfl⟩ := hm
  have e' : g ^ M * a ^ n = 0 := e
  apply hred _ (M + n)
  calc (g * a) ^ (M + n) = g ^ n * a ^ M * (g ^ M * a ^ n) := by ring
    _ = 0 := by rw [e', mul_zero]

theorem b_inj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁]
    (K₂ : Type) [CommRing K₂] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂)
    (r : ℕ → K) (N : ℕ), Pf p K → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} →
    PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) →
    PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) →
    ∀ a : K, i₁ (Polynomial.C a) = 0 → i₂ (Polynomial.C a) = 0 → ∀ k, r k * a = 0 := by
  intro p _ K _ K₁ _ K₂ _ f g i₁ i₂ r N hK hr hN h₁ h₂ a ha₁ ha₂
  obtain ⟨-, hred, -, -, hroots⟩ := pf_facts p K hK
  obtain ⟨k₁, hk₁⟩ := (h₁.ker _).1 ha₁
  obtain ⟨k₂, hk₂⟩ := (h₂.ker _).1 ha₂
  have hg : g * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred f g a _ hk₁
  have hf : f * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred g f a _ hk₂
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hN
  have h0 : r 0 ^ N * a = 0 := by
    rw [← huv]
    linear_combination u * hf + v * hg
  exact (hroots r hr).2.2 N a h0

end GlobalTheory.CompanionTheory.PerfectRing
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TensCompl

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
namespace CrystallineSemistableComparison.D.Leaf

theorem pf_facts : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], Pf p A → (∃ F : A ≃+* A, ∀ x, F x = x ^ p) ∧ (∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0) ∧ (∀ (k : ℕ) (x : A), ∃ y, y ^ p ^ k = x) ∧ (∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y) ∧ ∀ r : ℕ → A, IsRt p r → (∀ k, ∃ c, r k = c * r (k + 1) * r (k + 1)) ∧ (∀ k, r k ^ p ^ k = r 0) ∧ ∀ (N : ℕ) (x : A), r 0 ^ N * x = 0 → ∀ k, r k * x = 0 := GlobalTheory.CompanionTheory.PerfectRing.pf_facts

theorem wp_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (n : ℕ) (ι : Fin n → (B →ₐ[A] K)), IsWP ι → Pf p A → Pf p B → Pf p K := GlobalTheory.CompanionTheory.PerfectRing.wp_pf

theorem pq_ex : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S), (p : S) = 0 → ∃ (T : Type) (_ : CommRing T) (i : S →+* T), PQ p i I := GlobalTheory.CompanionTheory.PerfClos.exists_PQ

theorem pq_lift : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (T : Type) [CommRing T] (T₁ : Type) [CommRing T₁] (i : S →+* T) (I : Ideal S) (φ : S →+* T₁), PQ p i I → Pf p T₁ → (∀ x ∈ I, φ x = 0) → ∃! ψ : T →+* T₁, ψ.comp i = φ := GlobalTheory.CompanionTheory.PerfectRing.pq_lift

theorem bc_poly : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : Polynomial A →ₐ[A] B) (h : Polynomial A), Pf p A → Pf p K → PQ p (i : Polynomial A →+* B) (Ideal.span {h}) → ∃ i₁ : Polynomial K →+* B ⊗[A] K, PQ p i₁ (Ideal.span {h.map (algebraMap A K)}) ∧ (∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := GlobalTheory.CompanionTheory.Perfection.pq_baseChange_polynomial

theorem bc_laur : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : A[T;T⁻¹] →ₐ[A] B) (f g : A), Pf p A → Pf p K → PQ p (i : A[T;T⁻¹] →+* B) (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → ∃ i₁ : K[T;T⁻¹] →+* B ⊗[A] K, PQ p i₁ (Ideal.span {LaurentPolynomial.C (algebraMap A K f) - LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)}) ∧ (∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := GlobalTheory.CompanionTheory.PerfBC.bc_laur

theorem b_inj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (r : ℕ → K) (N : ℕ), Pf p K → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → ∀ a : K, i₁ (Polynomial.C a) = 0 → i₂ (Polynomial.C a) = 0 → ∀ k, r k * a = 0 := GlobalTheory.CompanionTheory.PerfectRing.b_inj

theorem b_mid : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ (b₁ : K₁) (b₂ : K₂), ρ₁ b₁ = ρ₂ b₂ → ∃ a : K, i₁ (Polynomial.C a) = b₁ ∧ i₂ (Polynomial.C a) = b₂ := GlobalTheory.CompanionTheory.BMid.exists_const_of_rho_eq

theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := GlobalTheory.CompanionTheory.PerfectRing.b_surj

theorem mv_prod : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B₁ : Type) [CommRing B₁] [Algebra A B₁] (B₂ : Type) [CommRing B₂] [Algebra A B₂] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ₁ : B₁ →ₐ[A] D) (ρ₂ : B₂ →ₐ[A] D), IsRt p r → Pf p D → (∀ y, ∃ b₁ b₂, y = ρ₁ b₁ - ρ₂ b₂) → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B₁) ⊗ₜ[A] a) = 0 → ((1 : B₂) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ (w₁ : B₁ ⊗[A] K) (w₂ : B₂ ⊗[A] K), Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) w₁ = Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) w₂ → ∃ a : K, w₁ = (1 : B₁) ⊗ₜ[A] a ∧ w₂ = (1 : B₂) ⊗ₜ[A] a) → Cov p r (B₁ × B₂) := GlobalTheory.CompanionTheory.SnakeCov.mv_prod

theorem cov_cmp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), (∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv B a c → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra A B₁), Cov p r B₁ ∧ Solv B₁ a c) → Cov p r B := GlobalTheory.CompanionTheory.CovCmp.cov_of_solv

theorem cov_mono : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Cov p r A ∧ ∀ (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁] (φ : B →ₐ[A] B₁), Cov p r B₁ → Cov p r B := GlobalTheory.CompanionTheory.CovMono.cov_mono

theorem cov_comp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B](B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁] (r : ℕ → A), Pf p A → Pf p B → IsRt p r → Cov p r B → Cov p (fun k => algebraMap A B (r k)) B₁ → Cov p r B₁ := GlobalTheory.CompanionTheory.CovComp.cov_comp

theorem cov_root : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (P : Polynomial A), Pf p A → P.Monic → 0 < P.natDegree → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∃ x : B, Polynomial.aeval x P = 0 := GlobalTheory.CompanionTheory.CovRoot.cov_root

theorem big_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → (∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ (∀ E ∈ 𝓔, Pt (algebraMap A B) E) ∧ ∀ (T : Type) [CommRing T] (x : A →+* T), Pf p T → (∀ E ∈ 𝓔, Pt x E) → ∃ y : B →+* T, y.comp (algebraMap A B) = x := GlobalTheory.CompanionTheory.BigStep.big_step

theorem colim_ex : ∀ (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1)), ∃ (L : Type) (_ : CommRing L) (_ : Algebra A L), ∃ ι : ∀ n, G n →ₐ[A] L, IsColim f ι := GlobalTheory.CompanionTheory.ColimEx.exists_isColim

theorem colim_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ((∀ n, Pf p (G n)) → Pf p L) ∧ ∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv L a c → ∃ N, Solv (G N) a c := GlobalTheory.CompanionTheory.colim_pf

theorem colim_test : ∀ (A : Type) [CommRing A] (π : A) (G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → (∀ n, AICm (f n : G n →+* G (n + 1))) → (∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) → AIC L ∧ VAL (algebraMap A L π) := GlobalTheory.CompanionTheory.Colim.aic_val_of_isColim

theorem tors_quot : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (π : B), Pf p B → ∃ (B₁ : Type) (_ : CommRing B₁) (q : B →+* B₁), Function.Surjective q ∧ Pf p B₁ ∧ q π ∈ nonZeroDivisors B₁ ∧ (∀ x, q x = 0 ↔ π * x = 0) ∧ (AIC B → AIC B₁) ∧ (VAL π → VAL (q π)) := GlobalTheory.CompanionTheory.PerfectRing.tors_quot

theorem compl_ex : ∀ (B : Type) [CommRing B] (π : B), ∃ (T : Type) (_ : CommRing T) (g : B →+* T), IsCompl π g := GlobalTheory.CompanionTheory.AdicCompl.exists_isCompl

theorem compl_reg : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → g π ∈ nonZeroDivisors T := GlobalTheory.CompanionTheory.ComplReg.isCompl_nonZeroDivisor

theorem compl_pf : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → Pf p B → Pf p T := GlobalTheory.CompanionTheory.PerfectRing.pf_of_isCompl

theorem compl_univ : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x π}) T₁ → ∃! ψ : T →+* T₁, ψ.comp g = x := GlobalTheory.CompanionTheory.PfCompl.isCompl_existsUnique

theorem compl_val : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → VAL π → VAL (g π) := GlobalTheory.CompanionTheory.ComplVal.compl_val

theorem compl_aic : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → AIC T := GlobalTheory.CompanionTheory.Completion.aic_of_isCompl

theorem wp_ex : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (n : ℕ), ∃ (K : Type) (_ : CommRing K) (_ : Algebra A K) (ι : Fin n → (B →ₐ[A] K)), IsWP ι := GlobalTheory.CompanionTheory.AlgCoproduct.exists_isWP

theorem wp_cof : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)), (∀ n, IsWP (ι n)) → Function.Bijective (algebraMap A (K 0)) ∧ Function.Bijective (ι 1 0) ∧ ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)), ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := GlobalTheory.CompanionTheory.Coproduct.coproduct_low_and_coface

theorem wp_dd : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∀ n z, alt (δ (n + 1)) (alt (δ n) z) = 0 := GlobalTheory.CompanionTheory.WpCoface.alt_alt

theorem wp_htpy : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∃ H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n, (∀ z, H 0 (alt (δ 0) z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (alt (δ n)).lTensor B (H n z) + H (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z := GlobalTheory.CompanionTheory.WpHomotopy.wp_homotopy

theorem ami_exact : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), Pf p A → Cov p r B → ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) → ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → (∀ z, d 0 z = 0 → ∀ k, r k • z = 0) ∧ ∀ n z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := GlobalTheory.CompanionTheory.Dblock.AmiExact.exact_of_contraction

theorem tens_exact : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type) [AddCommGroup N] [Module R N] (K₀ : Type) [AddCommGroup K₀] [Module R K₀] (K₁ : Type) [AddCommGroup K₁] [Module R K₁] (K₂ : Type) [AddCommGroup K₂] [Module R K₂] (K₃ : Type) [AddCommGroup K₃] [Module R K₃] (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂) (d₂ : K₂ →ₗ[R] K₃), IsRt p r → (∀ z, d₂ (d₁ z) = 0) → (∀ z, d₁ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₀) → (∀ z, d₂ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₁) → (∀ (a : R) (x : K₃), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0) → ∀ w : N ⊗[R] K₁, d₁.lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (d₀.lTensor N) := GlobalTheory.CompanionTheory.Dblock.smul_mem_range_lTensor_of_lTensor_eq_zero

theorem tens_compl : ∀ (R : Type) [CommRing R] (r : ℕ → R) (M : ℕ) (N : Type) [AddCommGroup N] [Module R N](B : Type) [CommRing B] [Algebra R B] (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T), (∀ x : N, r 0 ^ M • x = 0) → (∀ y : T, ∃ x, y - g x ∈ Ideal.span {algebraMap R T (r 0) ^ M}) → (∀ x : B, g x ∈ Ideal.span {algebraMap R T (r 0) ^ M} → ∀ k, r k • x ∈ Ideal.span {algebraMap R B (r 0) ^ M}) → Function.Surjective (g.toLinearMap.lTensor N) ∧ ∀ w : N ⊗[R] B, g.toLinearMap.lTensor N w = 0 → ∀ k, r k • w = 0 := GlobalTheory.CompanionTheory.TensCompl.main

theorem wp_rel : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∀ (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)), (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i) := GlobalTheory.CompanionTheory.WpCoface.coface_rel

end CrystallineSemistableComparison.D.Leaf
end
end
