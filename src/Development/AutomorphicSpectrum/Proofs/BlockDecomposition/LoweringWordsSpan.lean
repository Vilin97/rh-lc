module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectorsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirEqOfSingularWeightVectorStatement
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirElement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowSpanInfIdealLeSquareSpanStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatOfSimpleLoweringNilpotentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdealStatement
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimir

section

@[expose] public section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.NormIneq

variable {n : ℕ}

theorem casC_eq_sum (σ : Fin n → ℂ) :
    casC σ = ∑ a, σ a ^ 2 + ∑ a, σ a * ((n : ℂ) - 1 - 2 * ((a : ℕ) : ℂ)) :=
  _root_.UpperTheory.Reformulated.B.CasimirElement.main σ

theorem sum_wt_mul (m : Fin n × Fin n →₀ ℕ) (f : Fin n → ℤ) :
    ∑ k, wt m k * f k = m.sum fun a c => (c : ℤ) * (f a.1 - f a.2) := by
  simp only [wt, Finsupp.sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [rootAt, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem lt_of_step {f : Fin n → ℤ} (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i) :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d + 1 → f j < f i := by
  intro d
  induction d with
  | zero => intro i j hij; exact h i j (by simpa using hij)
  | succ d ih =>
    intro i j hij
    have hk : (i : ℕ) + d + 1 < n := by have := j.2; omega
    have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
    have h2 := h ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
    exact h2.trans h1

theorem eq_zero_of_casC_eq {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (hm : LowExp m)
    (hp : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ))
    (hc : casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n)) : m = 0 := by
  by_contra hne
  obtain ⟨f, hf⟩ : ∃ f : Fin n → ℤ, ∀ k, f k = 2 * ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) + wt m k :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i := by
    intro i j hij
    obtain ⟨p, hp⟩ := hp i j hij
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
    have hij' : ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + 1 := by exact_mod_cast hij
    rw [hf, hf, hij']
    linarith
  have hneg : ∑ k, wt m k * f k < 0 := by
    rw [sum_wt_mul]
    refine Finset.sum_neg (fun a ha => ?_) (Finsupp.support_nonempty_iff.2 hne)
    have hlow : (a.2 : ℕ) < a.1 := hm a ha
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (a.1 : ℕ) = a.2 + d + 1 := ⟨(a.1 : ℕ) - a.2 - 1, by omega⟩
    have hlt := lt_of_step hstep d a.2 a.1 hd
    have hpos : (0 : ℤ) < (m a : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 ha)
    exact mul_neg_of_pos_of_neg hpos (by linarith)
  have key : ((∑ k, wt m k * f k : ℤ) : ℂ) =
      casC (fun k => rhoVec n k + (wt m k : ℂ)) - casC (rhoVec n) := by
    rw [casC_eq_sum, casC_eq_sum, add_sub_add_comm, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    push_cast
    simp only [rhoVec]
    ring
  rw [hc, sub_self] at key
  have : ∑ k, wt m k * f k = 0 := by exact_mod_cast key
  omega

end GlobalTheory.CompanionTheory.PresRho.NormIneq
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimirStatement

section

@[expose] public section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

theorem _root_.GlobalTheory.T.eq_zero_of_low_exponent_casimir : ∀ {n : ℕ} (m : Fin n × Fin n →₀ ℕ), LowExp m → (∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ)) → casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n) → m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | exact GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorMemLowSpanSupVerma

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

namespace Verma

def lowPart (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter fun a => IsLower a

theorem lowExp_lowPart (m : Fin n × Fin n →₀ ℕ) : LowExp (lowPart m) := by
  intro a ha
  rw [lowPart, Finsupp.support_filter, Finset.mem_filter] at ha
  exact ha.2

theorem canon_lowPart (m : Fin n × Fin n →₀ ℕ) :
    canon (lowPart m) = word (blockW (lowL n) m) := by
  have hd : ∀ a ∈ diagL n, lowPart m a = 0 := fun a ha => by
    rw [lowPart, Finsupp.filter_apply_neg]
    exact not_lower_of_diag (mem_diagL.1 ha)
  have hu : ∀ a ∈ upL n, lowPart m a = 0 := fun a ha => by
    rw [lowPart, Finsupp.filter_apply_neg]
    exact not_lower_of_upper (mem_upL.1 ha)
  rw [canon_eq_blocks, blockW_eq_nil hd, blockW_eq_nil hu]
  simp only [word_nil, mul_one]
  refine congrArg word (blockW_congr fun a ha => ?_)
  rw [lowPart, Finsupp.filter_apply_pos _ _ (mem_lowL.1 ha)]

theorem wt_lowPart {m : Fin n × Fin n →₀ ℕ} (hu : ¬ HasUpper m) : wt (lowPart m) = wt m := by
  funext k
  rw [wt, wt, lowPart, Finsupp.sum_filter_index, Finsupp.support_filter, Finsupp.sum]
  refine Finset.sum_filter_of_ne fun a ha hne => ?_
  rcases lt_trichotomy a.1 a.2 with h | h | h
  · exact absurd ⟨a, h, Finsupp.mem_support_iff.1 ha⟩ hu
  · exfalso
    apply hne
    have : rootAt a k = 0 := by simp [rootAt, h]
    rw [this, mul_zero]
  · exact h

theorem wt_eq_of_mem_support {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x)
    {m : Fin n × Fin n →₀ ℕ} (hm : m ∈ (pbw.repr x).support) : wt m = μ := by
  funext k
  set s := (pbw.repr x).support
  set c := fun m => pbw.repr x m
  have hxs : x = ∑ m ∈ s, c m • canon m := (sum_repr_canon x).symm
  have h0 : ∑ m ∈ s, (c m * ((wt m k : ℂ) - (μ k : ℂ))) • canon m = 0 := by
    have h1 := sub_eq_zero.2 (hx k)
    rw [← h1]
    conv_rhs => rw [hxs]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, smul_smul, smul_smul,
      ← sub_smul, mul_sub, mul_comm (μ k : ℂ)]
  have h2 := linearIndependent_iff'.1 linearIndependent_canon s _ h0 m hm
  have hc : c m ≠ 0 := Finsupp.mem_support_iff.1 hm
  have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hc)
  exact_mod_cast h3

theorem canon_mem {μ : Fin n → ℤ} {m : Fin n × Fin n →₀ ℕ} (hw : wt m = μ) :
    canon m ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  by_cases hu : HasUpper m
  · exact Submodule.mem_sup_right (nPlusU_le_vermaIdeal _ (canon_mem_nPlusU hu))
  · have hnil : blockW (upL n) m = [] := blockW_eq_nil fun a ha => by
      by_contra h
      exact hu ⟨a, mem_upL.1 ha, h⟩
    set p : MvPolynomial (Fin n) ℂ := MvPolynomial.monomial (diagExp m) 1
    set ev : ℂ := MvPolynomial.eval (rhoVec n) p
    have hdec : canon m = ev • canon (lowPart m) +
        word (blockW (lowL n) m) * (hcEmb p - algebraMap ℂ (U n) ev) := by
      rw [canon_eq_triangular, hnil, canon_lowPart, mul_sub, word_nil, mul_one,
        Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      abel
    rw [hdec]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨lowPart m, lowExp_lowPart m, (wt_lowPart hu).trans hw, rfl⟩)) ?_
    exact mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal _ p)

end Verma

theorem mem_lowSpanW_sup_vermaIdeal_of_isAdW {n : ℕ} (μ : Fin n → ℤ) (x : U n) (hx : IsAdW μ x) :
    x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  rw [← sum_repr_canon x]
  exact Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ (Verma.canon_mem (Verma.wt_eq_of_mem_support hx hm))

end GlobalTheory.CompanionTheory.PresRho
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorMemLowSpanSupVermaStatement

section

@[expose] public section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

theorem _root_.GlobalTheory.T.weight_vector_mem_low_span_sup_verma : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | exact GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LoweringWordsSpan

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem exists_exp {μ : Fin n → ℤ} {x : U n} (h : x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n))
    (hx : x ∉ vermaIdeal (rhoVec n)) : ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ := by
  by_contra hne
  have hbot : lowSpanW μ = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨m, hm, hw, rfl⟩
    exact absurd ⟨m, hm, hw⟩ hne
  rw [hbot, bot_sup_eq] at h
  exact hx h

theorem lowExp_wt_zero {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) (h : wt m = 0) : m = 0 := by
  refine GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm (fun i j hij => ⟨1, by simp [h]⟩) ?_
  simp [h]

theorem mem_of_adW_zero {x : U n} (h : x ∈ lowSpanW (0 : Fin n → ℤ) ⊔ vermaIdeal (rhoVec n)) :
    ∃ c : ℂ, x - c • 1 ∈ vermaIdeal (rhoVec n) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 h
  clear h
  have : ∃ c : ℂ, y = c • 1 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, hw0, rfl⟩ := hx
      exact ⟨1, by rw [lowExp_wt_zero hm hw0]; simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨r * c, by rw [mul_smul]⟩
  obtain ⟨c, rfl⟩ := this
  exact ⟨c, by simpa using hw⟩

theorem mem_Jp_of_adW {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (ht0 : t ≠ 0)
    (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) :
    ∀ (N : ℕ) (μ : Fin n → ℤ) (x : U n), -ht μ < N → IsAdW μ x → φ x t = 0 → x ∈ Jp n := by
  intro N
  induction N with
  | zero =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have := ht_wt_nonpos hm
    push_cast at hN
    omega
  | succ N ih =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n := by
      intro a ha
      refine ih _ _ ?_ (hx.e_mul a) (by simp [h0])
      rw [ht_add_rootAt, ht_rootAt]
      have h1 : (a.1 : ℕ) < a.2 := ha
      push_cast at hN
      omega
    have hm0 : m = 0 := GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm
      (fun i j hij => GlobalTheory.T.nat_of_simple_lowering_nilpotent (wt m) x i j hx hup hJ hij (GlobalTheory.T.simple_lowering_pow_mem_ideal i j x hij))
      (GlobalTheory.T.casimir_eq_of_singular_weight_vector (wt m) x hx hup hJ)
    subst hm0
    have hw0 : wt (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext k; simp [wt]
    rw [hw0] at hx
    obtain ⟨c, hc⟩ := mem_of_adW_zero (GlobalTheory.T.weight_vector_mem_low_span_sup_verma 0 x hx)
    have h1 := act_eq_zero_of_mem φ t hd hu hc
    rw [map_sub, LinearMap.sub_apply, h0, zero_sub, map_smul, map_one] at h1
    have hc0 : c = 0 := by
      by_contra hne
      simp [hne, ht0] at h1
    rw [hc0, zero_smul, sub_zero] at hc
    exact hJ (vermaIdeal_le_Jp hc)

theorem word_mem_lowSpan {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, p.2 < p.1) :
    word l ∈ lowSpan n := by
  refine (Submodule.span_le.2 ?_) (word_mem_canonSpan closed_lower l hl)
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact Submodule.subset_span ⟨m, hm, rfl⟩

theorem rho_cast (a : Fin n) : ((rhoV n a : ℝ) : ℂ) = rhoVec n a := by
  simp [rhoV, rhoVec]

theorem act_eq_zero_of_sqSpan {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    {F : Fin n → Fin n → Module.End ℂ Z} (φ : U n →ₐ[ℂ] Module.End ℂ Z)
    (hφ : ∀ i j, φ (e (i, j)) = F i j) (z : Z)
    (hz : ∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) {x : U n}
    (hx : x ∈ sqSpan n) : φ x z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    simp only [map_mul, map_pow, hφ, Module.End.mul_apply]
    rw [hz i j hij, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

theorem pres_rho : ∀ {n : ℕ} {A Z : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (G : Fin n → Fin n → Module.End ℂ A) (F : Fin n → Fin n → Module.End ℂ Z),
    Formalism.REAL.GlRel G → Formalism.REAL.GlRel F → ∀ t : A, t ≠ 0 →
    (∀ a, G a a t = ((rhoV n a : ℝ) : ℂ) • t) → (∀ a b, a < b → G a b t = 0) →
    ∀ z : Z, (∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) →
    ∀ (s : Finset (List (Fin n × Fin n))) (coef : List (Fin n × Fin n) → ℂ), (∀ l ∈ s, ∀ p ∈ l, p.2 < p.1) →
    ∑ l ∈ s, coef l • (l.map fun p => G p.1 p.2).prod t = 0 →
    ∑ l ∈ s, coef l • (l.map fun p => F p.1 p.2).prod z = 0 := by
  intro n A Z _ _ _ _ G F hG hF t ht0 hd hu z hz s coef hs hsum
  obtain ⟨φ, hφ⟩ := exists_act G hG
  obtain ⟨ψ, hψ⟩ := exists_act F hF
  have hd' : ∀ k, φ (e (k, k)) t = rhoVec n k • t := fun k => by
    rw [hφ, hd, rho_cast]
  have hu' : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0 := fun a ha => by
    rw [show e a = e (a.1, a.2) from rfl, hφ]; exact hu _ _ ha
  set Y : U n := ∑ l ∈ s, coef l • word l with hY
  have hYlow : Y ∈ lowSpan n :=
    Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (word_mem_lowSpan (hs l hl))
  have hYt : φ Y t = 0 := by

    rw [hY, map_sum, LinearMap.sum_apply, ← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, act_word φ hφ]
  have hYJ : Y ∈ Jp n := by
    refine (Submodule.span_le.2 ?_) (GlobalTheory.T.annihilator_spanned_by_weight_vectors φ t hd' Y hYt)
    rintro y ⟨μ, hy, h0⟩
    exact mem_Jp_of_adW φ t ht0 hd' hu' (-ht μ + 1).toNat μ y (by omega) hy h0
  have hYs := GlobalTheory.T.low_span_inf_ideal_le_square_span Y hYlow hYJ
  have h := act_eq_zero_of_sqSpan ψ hψ z hz hYs

  rw [hY, map_sum, LinearMap.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, LinearMap.smul_apply, act_word ψ hψ]

end GlobalTheory.CompanionTheory.PresRho
end
end
end
