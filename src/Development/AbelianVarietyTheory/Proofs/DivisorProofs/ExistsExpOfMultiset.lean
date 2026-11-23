module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
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
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosetsStatement
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Field.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRootLeCardMulBoundOfEsymmNormLeStatement
import Mathlib.Algebra.Order.Star.Real
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLeStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeTj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  first | exact @GlobalTheory.TjCount.tj_cosets_finite_card_le | exact GlobalTheory.TjCount.tj_cosets_finite_card_le | (intros; apply GlobalTheory.TjCount.tj_cosets_finite_card_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTnScalarUniformiserSingleTranslation

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.LFun

theorem tn_single (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (ϖ : w.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E w ϖ) :
    ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)), ∃ g,
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  classical
  intro x hx
  have h0 : ϖ ≠ 0 := Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ
  set g := Formalism.UG.P.tjcosets_dG n n ϖ h0 with hg
  have hdiag : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    unfold Formalism.UG.diagJ
    ext i j
    by_cases h : i = j
    · subst h; simp [i.2]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hcomm : ∀ a : GL (Fin n) (w.adicCompletion E), g * a = a * g := fun a => by
    ext : 1
    rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val, hdiag]
    simp
  have hT : Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n = Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL w (n := n)) g := by
    unfold Formalism.UG.Tj Formalism.UG.dosetInd
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b, hb, Units.ext (by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]; exact e)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]⟩
  refine ⟨g, ?_⟩
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx (R := {g})]
  · simp
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
    refine ⟨g, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have : g⁻¹ * (a * g * b) = a * b := by
      rw [← hcomm a]; group
    rw [this]
    exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ha hb

end GlobalTheory.LFun
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTnScalarUniformiserSingleTranslationStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)), ∃ g, GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  first | exact @GlobalTheory.LFun.tn_single | exact GlobalTheory.LFun.tn_single | (intros; apply GlobalTheory.LFun.tn_single <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormInvLePowCardOfNormProdEqOne

section

@[expose] public section

namespace GlobalTheory

theorem norm_inv_le_pow_card_of_norm_prod_eq_one :
    ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) →
      ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  intro B M hM hB hprod b hb
  have aux : ∀ C : Multiset ℂˣ, (∀ c ∈ C, ‖(c : ℂ)‖ ≤ M) →
      ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ ≤ M ^ C.card := by
    intro C
    induction C using Multiset.induction_on with
    | empty => intro _; simp
    | cons a C ih =>
      intro hC
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, norm_mul,
        mul_comm (M ^ _)]
      exact mul_le_mul (hC a (Multiset.mem_cons_self a C))
        (ih fun c hc => hC c (Multiset.mem_cons_of_mem hc)) (norm_nonneg _) (by linarith)
  obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hb
  have hC : ∀ c ∈ C, ‖(c : ℂ)‖ ≤ M := fun c hc => hB c (Multiset.mem_cons_of_mem hc)
  rw [Multiset.map_cons, Multiset.prod_cons, norm_mul] at hprod
  have hinv : ‖((b⁻¹ : ℂˣ) : ℂ)‖ = ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact (eq_inv_of_mul_eq_one_right hprod).symm
  rw [hinv, Multiset.card_cons]
  exact (aux C hC).trans (pow_le_pow_right₀ hM (Nat.le_succ _))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormInvLePowCardOfNormProdEqOneStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' : ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) → ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  first | exact @GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one | exact GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one | (intros; apply GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpOfMultiset

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V
open Formalism.L2.Host

namespace GlobalTheory.HenQ

theorem local_bound (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (h1 : ∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) (h2 : ∀ x, x ≠ 0 → 0 < (Bf x x).re)
    (h3 : ∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w ρ B) :
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Formalism.UG.qV E w : ℝ) ^ (n * n + n)) ∧
      ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ ((Formalism.UG.qV E w : ℝ) ^ (n * n + n)) ^ n := by
  obtain ⟨x, hx0, hxK, hcard, hT⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  set q := Formalism.UG.qV E w with hqdef
  have hq2 : 2 ≤ q := GlobalTheory.LFun.one_lt_absNorm w
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)

  have he : ∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ (q : ℝ) ^ (n * n) := by
    intro j _ hjn
    obtain ⟨hfin, hc⟩ := GlobalTheory.T.heckeTj_cosets_finite_card_le E w n ϖ hϖ j hjn
    have hh : ∀ g, ‖Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j g‖ ≤ 1 := fun g => by
      unfold Formalism.UG.Tj
      exact (norm_indicator_le_norm_self _ _).trans (by simp)
    have k1 := GlobalTheory.T.norm_heckeEigenvalue_le_card_cosets _ (GlobalTheory.LFun.KGL w (n := n)) V ρ Bf h1 h2 h3 _ x _ hh hfin hx0 (hT ϖ hϖ j hjn)
    have k2 : ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ ‖GlobalTheory.LFun.satEig q n B j‖ := by
      unfold GlobalTheory.LFun.satEig
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      refine le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow hq1 ?_)
      have : (((j : ℂ) * ((n : ℂ) - j)) / 2).re = (j : ℝ) * ((n : ℝ) - j) / 2 := by simp
      rw [this]
      have : (j : ℝ) ≤ n := by exact_mod_cast hjn
      positivity
    refine k2.trans (k1.trans ?_)
    refine le_trans ((Nat.cast_le (α := ℝ)).2 hc) ?_
    push_cast
    exact pow_le_pow_right₀ hq1 (Nat.mul_le_mul_left n hjn)
  have hnq : (n : ℝ) ≤ (q : ℝ) ^ n := by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    have h2n : (2 : ℝ) ^ n ≤ (q : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq2) n
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast this.le
    linarith
  have hup : ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (q : ℝ) ^ (n * n + n) := by
    intro b hb
    refine (GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le n B _ hcard (one_le_pow₀ hq1) he b hb).trans ?_
    rw [pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_left hnq (by positivity)
  refine fun b hb => ⟨hup b hb, ?_⟩

  obtain ⟨g, hg⟩ := GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation E w n V ρ ϖ hϖ x hxK
  have hn := hT ϖ hϖ n le_rfl
  have hsat : GlobalTheory.LFun.satEig q n B n = (B.map fun b : ℂˣ => (b : ℂ)).prod := by
    unfold GlobalTheory.LFun.satEig
    simp only [sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
    have : (B.map fun b : ℂˣ => (b : ℂ)).card = n := by rw [Multiset.card_map, hcard]
    rw [← this, Multiset.esymm, Multiset.powersetCard_self]
    simp
  rw [hg, hsat] at hn
  have hp : ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 := by
    set c := (B.map fun b : ℂˣ => (b : ℂ)).prod
    have e := h3 g x x
    rw [hn, map_smul, map_smulₛₗ, LinearMap.smul_apply] at e
    have hx : Bf x x ≠ 0 := fun h0 => by simpa [h0] using h2 x hx0
    simp only [smul_eq_mul] at e
    have e2 : starRingEnd ℂ c * c = 1 := by
      refine mul_right_cancel₀ hx ?_
      rw [one_mul]
      nth_rewrite 2 [← e]
      ring
    have e3 : ‖c‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      have : (Complex.normSq c : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact e2
      exact_mod_cast this
    nlinarith [norm_nonneg c]
  have := GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' B _ (one_le_pow₀ hq1) hup hp b hb
  rwa [hcard] at this

end GlobalTheory.HenQ
end
end
end
