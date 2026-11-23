module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Etale.Weakly
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
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRootMem

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem kummer_root_mem : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 0 < m → ∀ (f : X.Kˣ) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → ∃ g : X.Kˣ, f = g ^ m := by
  intro Ω _ _ _ ε X _ _ m hm f a b M hM ha hb hb0 hfab hinv
  have hHs_open : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hHs_conn : IsPreconnected Hs :=
    (convex_halfSpace_gt Complex.imLm.isLinear (0 : ℝ)).isPreconnected
  have hbne : ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
    rcases (hb.analyticOnNhd hHs_open).eqOn_zero_or_eventually_ne_zero_of_preconnected hHs_conn with h | h
    · exfalso; apply hb0
      exact Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h hz))
    · exact h
  have hrep : ∀ x : Mero, ∃ φ : ℂ → ℂ, x = (φ : Mero) := fun x =>
    Filter.Germ.inductionOn x (fun φ => ⟨φ, rfl⟩)
  obtain ⟨φ, hφ⟩ := hrep (X.an (f : X.K))
  rw [hφ, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul] at hfab
  have h1 : ∀ᶠ z in Filter.codiscreteWithin Hs, φ z * b z ^ m = a z ^ m :=
    (Filter.Germ.coe_eq.1 hfab).mono fun z hz => by simpa using hz
  have h2 : ∀ᶠ z in Filter.codiscreteWithin Hs, (a z / b z) ^ m = φ z := by
    filter_upwards [h1, hbne] with z hz hbz
    rw [div_pow, div_eq_iff (pow_ne_zero _ hbz), hz]
  have hpoly : ∃ P : Polynomial X.K, P ≠ 0 ∧ P.eval₂ X.an (((a / b : ℂ → ℂ)) : Mero) = 0 := by
    refine ⟨Polynomial.X ^ m - Polynomial.C (f : X.K), Polynomial.X_pow_sub_C_ne_zero hm _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hφ, ← Filter.Germ.coe_pow, sub_eq_zero]
    exact Filter.Germ.coe_eq.2 (h2.mono fun z hz => by simpa using hz)
  obtain ⟨g0, hg0⟩ := X.sat a b M hM ha hb hb0 hinv hpoly
  obtain ⟨ψ, hψ⟩ := hrep (X.an g0)
  rw [hψ, ← Filter.Germ.coe_mul] at hg0
  have h3 : ∀ᶠ z in Filter.codiscreteWithin Hs, ψ z * b z = a z :=
    (Filter.Germ.coe_eq.1 hg0).mono fun z hz => by simpa using hz
  haveI : Nontrivial Mero := ⟨⟨_, _, hb0⟩⟩
  have hpow : g0 ^ m = (f : X.K) := by
    apply X.an.injective
    rw [map_pow, hψ, hφ, ← Filter.Germ.coe_pow]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [h2, h3, hbne] with z hz2 hz3 hbz
    have : ψ z = a z / b z := by rw [eq_div_iff hbz, hz3]
    simp only [Pi.pow_apply]
    rw [this, hz2]
  have hg0ne : g0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hpow
    exact f.ne_zero hpow.symm
  refine ⟨Units.mk0 g0 hg0ne, ?_⟩
  ext
  simp [hpow]

end GlobalTheory.KZ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfBettiKummerRelationPadicZero

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gamma_le_gamma_of_dvd {K M : ℕ} (h : K ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma K := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h1
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h2
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h3
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h4

theorem mem_gam_of_mem_gamma {N l : ℕ} {δ : SL(2, ℤ)} (hN : δ ∈ CongruenceSubgroup.Gamma N)
    (hl : δ ∈ CongruenceSubgroup.Gamma l) : δ ∈ Gam N l := by
  rw [CongruenceSubgroup.Gamma_mem] at hN hl
  refine ⟨?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma1_mem N δ).2 ⟨hN.1, hN.2.2.2, hN.2.2.1⟩
  · exact CongruenceSubgroup.Gamma0_mem.2 hl.2.2.1

theorem cls_pow_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (g : X.Kˣ) : X.cls l n (g ^ (l ^ n)) = 0 := by
  unfold Tower.cls
  rw [Submodule.Quotient.mk_eq_zero]
  have h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul (g ^ (l ^ n)) : X.Kl l) =
      ((l : ℤ_[l]) ^ n) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul g : X.Kl l) := by
    rw [ofMul_pow, TensorProduct.tmul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) Submodule.mem_top

theorem eq_zero_of_btZ_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l : ℕ) [Fact l.Prime], 0 < N → ∀ b : X.Fn l, BtZ X N l b 0 → b = 0 := by
  intro Ω _ _ _ ε X hε hj N l hl hN b hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, ⟨f, a, c, M₁, hM₁, hev, ⟨ha, hc, hc0, hroot⟩, hinv⟩, M₂, hM₂, hχ⟩ := hb n u
  have hlpos : 0 < l := hl.out.pos
  obtain ⟨g, hg⟩ := kummer_root_mem ε X hε hj (l ^ n) (pow_pos hlpos n) f a c (M₁ * M₂ * N * l)
    (by positivity) ha hc hc0 hroot (by
      intro γ hγ
      have h1 : γ ∈ CongruenceSubgroup.Gamma M₁ := gamma_le_gamma_of_dvd ⟨M₂ * N * l, by ring⟩ hγ
      have h2 : γ ∈ CongruenceSubgroup.Gamma M₂ := gamma_le_gamma_of_dvd ⟨M₁ * N * l, by ring⟩ hγ
      have h3 : γ ∈ CongruenceSubgroup.Gamma N := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * l, by ring⟩ hγ
      have h4 : γ ∈ CongruenceSubgroup.Gamma l := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * N, by ring⟩ hγ
      have h0 : χ γ = 0 := by
        have := hχ ⟨γ, mem_gam_of_mem_gamma h3 h4⟩ h2
        simpa using this.symm
      refine Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) fun z hz => ?_)
      have := hinv γ h1 z hz
      rw [h0] at this
      simpa using this)
  have : AdicCompletion.eval (idl l) (X.Kl l) n (b u) = 0 := by
    rw [hev, hg, cls_pow_eq_zero]
  exact this

end GlobalTheory.KZ.BettiB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfBettiKummerRelationPadicZeroStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

theorem _root_.GlobalTheory.T.eq_zero_of_bettiKummerRelationPadic_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l : ℕ) [Fact l.Prime], 0 < N → ∀ b : X.Fn l, BtZ X N l b 0 → b = 0 := by
  first | exact @GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero | exact GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero | (intros; apply GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero <;> assumption)
end
end
