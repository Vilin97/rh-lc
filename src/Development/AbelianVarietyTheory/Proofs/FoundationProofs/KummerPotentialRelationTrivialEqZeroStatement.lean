module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Analytic.Order
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerClassEvalEqZeroOfVanishingOnCongruence

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KZero

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs :=
  (convex_halfSpace_gt Complex.imLm.isLinear (0 : ℝ)).isPreconnected

theorem eventually_ne_zero {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (hb0 : (b : Mero) ≠ 0) :
    ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
  have hA : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs
  obtain ⟨z0, hz0, hbz0⟩ : ∃ z0 ∈ Hs, b z0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb0 (Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) h))
  have h0 : analyticOrderAt b z0 ≠ ⊤ := by
    rw [(hA z0 hz0).analyticOrderAt_eq_zero.2 hbz0]; exact ENat.zero_ne_top
  filter_upwards [hA.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top,
    Filter.self_mem_codiscreteWithin Hs] with z hz hzH
  rcases hz with hz | hz
  · exact (hA z hzH).analyticOrderAt_eq_zero.1 hz
  · exact absurd hz (hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_Hs hz0 hzH h0)

theorem cast_of_mul {M M' : ℕ} {x : ℤ} {y : ℤ} (h : (x : ZMod (M * M')) = y) : (x : ZMod M) = y := by
  have := congrArg (ZMod.castHom (dvd_mul_right M M') (ZMod M)) h
  simpa using this

theorem gamma_mul_le {M M' : ℕ} : CongruenceSubgroup.Gamma (M * M') ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast cast_of_mul (y := 1) (by exact_mod_cast h1)
  · exact_mod_cast cast_of_mul (y := 0) (by exact_mod_cast h2)
  · exact_mod_cast cast_of_mul (y := 0) (by exact_mod_cast h3)
  · exact_mod_cast cast_of_mul (y := 1) (by exact_mod_cast h4)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cls_pow_eq_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (G : X.Kˣ) : X.cls l n (G ^ (l ^ n)) = 0 := by
  rw [Tower.cls, Submodule.Quotient.mk_eq_zero, ofMul_pow]
  have e : (1 : ℤ_[l]) ⊗ₜ[ℤ] ((l ^ n) • Additive.ofMul G) =
      ((l : ℤ_[l]) ^ n) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul G) := by
    rw [← natCast_zsmul, TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℤ_[l]]
    push_cast
    rfl
  rw [e]
  have hl : (l : ℤ_[l]) ∈ idl l := Ideal.subset_span (Set.mem_singleton _)
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hl n) Submodule.mem_top

end GlobalTheory.KZ.H3.KZero

namespace GlobalTheory.KZ.H3


open KZero in
theorem kum_near_zero_eval : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ 0 → AdicCompletion.eval (idl l) (X.Kl l) n x = 0 := by
  intro Ω _ _ ε X l _ n x χ hK hN
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hroot⟩, hχ⟩ := hK
  obtain ⟨M', hM', hz⟩ := hN
  have hmpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hne := eventually_ne_zero hb hb0
  obtain ⟨φ, hφ⟩ := Quot.exists_rep (X.an (f : X.K))
  have hφ' : X.an (f : X.K) = (φ : Mero) := hφ.symm
  rw [hφ', ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at hroot

  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma (M * M'),
      ((fun z => a (mob (ofSL γ) z) * b z : ℂ → ℂ) : Mero) = ((fun z => a z * b (mob (ofSL γ) z) : ℂ → ℂ) : Mero) := by
    intro γ hγ
    have h1 : γ ∈ CongruenceSubgroup.Gamma M := gamma_mul_le hγ
    have h2 : γ ∈ CongruenceSubgroup.Gamma M' := gamma_mul_le (M := M') (M' := M) (by rw [mul_comm]; exact hγ)
    refine Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) fun z hz' => ?_)
    have := hχ γ h1 z hz'
    rw [hz γ h2] at this
    simpa using this

  have hP : ∃ P : Polynomial X.K, P ≠ 0 ∧ P.eval₂ X.an (((a / b : ℂ → ℂ)) : Mero) = 0 := by
    refine ⟨Polynomial.X ^ (l ^ n) - Polynomial.C (f : X.K), Polynomial.X_pow_sub_C_ne_zero hmpos _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hφ', sub_eq_zero, ← Filter.Germ.coe_pow,
      Filter.Germ.coe_eq]
    filter_upwards [hroot, hne] with z h1 h2
    simp only [Pi.pow_apply, Pi.div_apply, Pi.mul_apply] at h1 ⊢
    rw [div_pow, ← h1]
    field_simp
  obtain ⟨g, hg⟩ := X.sat a b (M * M') (Nat.mul_pos hM hM') ha hb hb0 hlev hP
  obtain ⟨ψ, hψ⟩ := Quot.exists_rep (X.an g)
  have hψ' : X.an g = (ψ : Mero) := hψ.symm
  rw [hψ', ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at hg
  haveI : Nontrivial Mero := ⟨⟨(b : Mero), 0, hb0⟩⟩
  have hgm : g ^ (l ^ n) = (f : X.K) := by
    apply X.an.injective
    rw [map_pow, hψ', hφ', ← Filter.Germ.coe_pow, Filter.Germ.coe_eq]
    filter_upwards [hroot, hg, hne] with z h1 h2 h3
    simp only [Pi.pow_apply, Pi.mul_apply] at h1 h2 ⊢
    have h4 : ψ z ^ (l ^ n) * b z ^ (l ^ n) = φ z * b z ^ (l ^ n) := by rw [← mul_pow, h2, h1]
    exact mul_right_cancel₀ (pow_ne_zero _ h3) h4
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hmpos.ne'] at hgm
    exact f.ne_zero hgm.symm
  have hfG : f = (Units.mk0 g hg0) ^ (l ^ n) := by
    ext; simp [hgm]
  rw [hx, hfG]
  exact cls_pow_eq_zero X l n _

end GlobalTheory.KZ.H3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerClassEvalEqZeroOfVanishingOnCongruenceStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ 0 → AdicCompletion.eval (idl l) (X.Kl l) n x = 0 := by
  first | exact @GlobalTheory.KZ.H3.kum_near_zero_eval | exact GlobalTheory.KZ.H3.kum_near_zero_eval | (intros; apply GlobalTheory.KZ.H3.kum_near_zero_eval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationTrivialEqZero

section

@[expose] public section

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem relTriv_gamma_of_dvd {N M : ℕ} (h : N ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

theorem toZModPow_eval_mulVec {l : ℕ} [Fact l.Prime] (n : ℕ) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n)) (u : Fin 2 → ℤ_[l]) (q : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval
      (((δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℤ_[l]) *ᵥ u) q) =
      PadicInt.toZModPow n (MvPolynomial.eval u q) := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ
  obtain ⟨a, b, c, d⟩ := hδ
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval]
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  have e : ∀ x : ℤ, PadicInt.toZModPow n ((x : ℤ_[l])) = (x : ZMod (l ^ n)) := fun x => map_intCast _ x
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e, a, b, c, d]

theorem rel_triv_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ →
      ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  intro Ω _ _ ε X l _ w Γ M₀ hM₀ hΓ b F hR hF
  obtain ⟨ψ, p, hψ, hFψ⟩ := hF
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, hK, M₁, hM₁, hχ⟩ := hR u n
  change AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n ((0 : X.Fn l) u)
  rw [Pi.zero_apply, map_zero]
  refine GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence Ω ε X l n (b u) χ hK ⟨M₁ * M₀ * l ^ n, ?_, fun δ hδ => ?_⟩
  · have : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    positivity
  have h1 : δ ∈ CongruenceSubgroup.Gamma M₁ := relTriv_gamma_of_dvd ⟨M₀ * l ^ n, by ring⟩ hδ
  have h0 : δ ∈ Γ := hΓ (relTriv_gamma_of_dvd ⟨M₁ * l ^ n, by ring⟩ hδ)
  have hl : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := relTriv_gamma_of_dvd ⟨M₁ * M₀, by ring⟩ hδ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hδI : mob (ofSL δ) Complex.I ∈ Hs := (GlobalTheory.T.glTwoPosRatMobius_basic_laws).1 _ _ hI
  have key := hχ δ h1 Complex.I hI
  beta_reduce at key
  rw [← key, hFψ _ hδI, hFψ _ hI, ← hψ δ h0 Complex.I hI]
  simp only [map_add (f := _), GlobalTheory.KZ.Betti.eval_slP, add_sub_add_right_eq_sub, map_sub,
    toZModPow_eval_mulVec n hl, sub_self, Pi.zero_apply]

end GlobalTheory.KZ.H3
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationTrivialEqZeroStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  first | exact @GlobalTheory.KZ.H3.rel_triv_eq_zero | exact GlobalTheory.KZ.H3.rel_triv_eq_zero | (intros; apply GlobalTheory.KZ.H3.rel_triv_eq_zero <;> assumption)
end
end
