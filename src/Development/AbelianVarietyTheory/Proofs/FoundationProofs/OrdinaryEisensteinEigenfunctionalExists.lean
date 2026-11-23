module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CharElementary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSqStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenfunctionalAllCharactersOfAtkinLehner
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharParityMulNeOneMulInvNeOneStatement
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalDepletedEisensteinNeZe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductValueNeZeroOfDepletedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothingIntegersTwoCharactersStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdgeStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedNewformPrim

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
noncomputable section

namespace GlobalTheory.EisM

theorem depleted_newform_prim : ∀ (k r : ℕ) (g : Newform k), 1 ≤ k → 2 ≤ r → ∃ χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2), Prim k _ χ (fun n => if n.Coprime (g.M * r) then g.a n else 0) ∧ ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d := by
  intro k r g _ hr
  have hM := g.pos
  have hLpos : 0 < g.M * r := Nat.mul_pos hM (by omega)
  have hdvd : g.M ∣ g.M * (g.M * r) ^ 2 := dvd_mul_right _ _
  have hLN : g.M * r ∣ g.M * (g.M * r) ^ 2 := (dvd_pow_self _ two_ne_zero).mul_left g.M
  have hcop : ∀ n : ℕ, n.Coprime (g.M * (g.M * r) ^ 2) ↔ n.Coprime (g.M * r) := by
    intro n
    constructor
    · intro h; exact h.coprime_dvd_right hLN
    · intro h
      exact Nat.Coprime.mul_right (h.coprime_dvd_right (dvd_mul_right _ _)) (Nat.Coprime.pow_right 2 h)
  set χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2) := DirichletCharacter.changeLevel hdvd g.χ with hχdef
  have hχZ : ∀ d : ℤ, IsCoprime d ((g.M * (g.M * r) ^ 2 : ℕ) : ℤ) → ch χ d = g.χ (d : ZMod g.M) := by
    intro d hd
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd' g.χ hdvd hd
  have hχN : ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d := by
    intro d hd
    have := hχZ d (Nat.isCoprime_iff_coprime.2 hd)
    simpa [ch] using this
  refine ⟨χ, ?_, hχN⟩

  have hcf0 := ((gamma1_char_elementary k g.M g.χ hM).2 g.f g.char).2
  have htw := GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq k g.M (g.M * r) g.χ (1 : DirichletCharacter ℂ (g.M * r)) (coef g.f) hLpos hcf0
  have hseq : (fun n : ℕ => (1 : DirichletCharacter ℂ (g.M * r)) n * coef g.f n) =
      (fun n => if n.Coprime (g.M * r) then g.a n else 0) := by
    funext n
    by_cases h : n.Coprime (g.M * r)
    · rw [if_pos h, MulChar.one_apply ((ZMod.isUnit_iff_coprime n _).2 h), one_mul]; rfl
    · rw [if_neg h, MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n _).1 hu)), zero_mul]
  rw [hseq] at htw
  have hlin := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k (g.M * (g.M * r) ^ 2) (fun d => ch g.χ d * ch (1 : DirichletCharacter ℂ (g.M * r)) d ^ 2)).2.2.2.1
    (ch χ) _ ?_ htw.1
  swap
  · intro d hd
    have hdL : IsCoprime d ((g.M * r : ℕ) : ℤ) := hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hLN)
    rw [hχZ d hd]
    simp only [ch]
    rw [← ZMod.coe_unitOfIsCoprime d hdL, MulChar.one_apply_coe, one_pow, mul_one]
  refine ⟨⟨hlin, htw.2⟩, ?_, ?_, ?_⟩
  · have h1 : (1 : ℕ).Coprime (g.M * r) := Nat.coprime_one_left _
    simp only [if_pos h1]
    exact g.one
  · intro n hn
    have : ¬ n.Coprime (g.M * r) := fun h => hn ((hcop n).2 h)
    simp only [if_neg this]
  · intro q hq hqN
    have hqL : q.Coprime (g.M * r) := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqN (h.trans hLN))
    have hqM : ¬ q ∣ g.M := fun h => hqN (h.trans hdvd)
    have hchq : ch χ (q : ℤ) = g.χ (q : ZMod g.M) := by
      rw [hχZ (q : ℤ) (Nat.isCoprime_iff_coprime.2 ((hcop q).2 hqL))]; simp
    have heig := g.eig q hq hqM
    funext n
    simp only [To, Vo, hchq, if_pos hqL]
    by_cases hn : n.Coprime (g.M * r)
    · have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; rw [Nat.coprime_zero_left] at hn; nlinarith
        · exact h0
      have hqn : (q * n).Coprime (g.M * r) := Nat.Coprime.mul_left hqL hn
      rw [if_pos hqn, if_pos hn]
      have e := heig n hn1
      by_cases hd : q ∣ n
      · have hnq : (n / q).Coprime (g.M * r) := hn.coprime_dvd_left (Nat.div_dvd_of_dvd hd)
        rw [if_pos hd, if_pos hnq]
        rw [if_pos hd] at e
        exact e
      · rw [if_neg hd]
        rw [if_neg hd] at e
        exact e
    · have hqn : ¬ (q * n).Coprime (g.M * r) := fun h => hn (Nat.Coprime.coprime_mul_left h)
      rw [if_neg hqn, if_neg hn, mul_zero]
      by_cases hd : q ∣ n
      · have hnq : ¬ (n / q).Coprime (g.M * r) := by
          intro h
          apply hn
          rw [← Nat.mul_div_cancel' hd]
          exact Nat.Coprime.mul_left hqL h
        rw [if_pos hd, if_neg hnq]; simp
      · rw [if_neg hd]; simp

end GlobalTheory.EisM

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenfunctionalAllCharactersOfAtkinLehnerStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eigenfunctionalAllCharacters_of_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c → ∃ (B' : ℕ) (c' : ℕ → ℂ), EigAll k N l χ g (χ l * α) B' c' ∧ ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a' := by
  first | exact @GlobalTheory.EisM.eigAll_of_atkinLehner | exact GlobalTheory.EisM.eigAll_of_atkinLehner | (intros; apply GlobalTheory.EisM.eigAll_of_atkinLehner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalDepletedEisensteinNeZeStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_heckeEigenfunctional_depletedEisenstein_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ ≠ 1 → ∃ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.EisM.eigF_value_ne_zero | exact GlobalTheory.EisM.eigF_value_ne_zero | (intros; apply GlobalTheory.EisM.eigF_value_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctionalStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_muModel_measure_of_eigenfunctional : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (α : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → ‖ι.symm α‖ = 1 → (∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ → MF (2 * e + 1) (N * l) (ch ε) a → lam B c a = 0) → (∀ a, MF (2 * e + 1) (N * l) (ch χ) a → lam B c (Uo l a) = α * lam B c a) → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → MeasMu ι e ((-1) ^ e * ψ (-1)) (hat θ) (tw2 N ((-1) ^ e * ψ (-1))) ψ α B c ((2 / (N.totient : ℂ)) * val B c l α 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e))) := by
  first | exact @GlobalTheory.EisM.measMu_of_eig | exact GlobalTheory.EisM.measMu_of_eig | (intros; apply GlobalTheory.EisM.measMu_of_eig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitRootSplit

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem unitRoot_split : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (t D : ℂ),
    ‖ι.symm t‖ = 1 → ‖ι.symm D‖ < 1 →
    ∃ α β : ℂ, α + β = t ∧ α * β = D ∧ ‖ι.symm α‖ = 1 ∧ ‖ι.symm β‖ = ‖ι.symm D‖ := by
  intro l _ ι t D ht hD
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4 * D) (n := 2) (by norm_num)
  have hsum : (t + s) / 2 + (t - s) / 2 = t := by ring
  have hprod : (t + s) / 2 * ((t - s) / 2) = D := by
    have : (t + s) / 2 * ((t - s) / 2) = (t ^ 2 - s ^ 2) / 4 := by ring
    rw [this, hs]; ring
  have key : ∀ a b : ℂ, a + b = t → a * b = D → 1 ≤ ‖ι.symm a‖ →
      ‖ι.symm a‖ = 1 ∧ ‖ι.symm b‖ = ‖ι.symm D‖ := by
    intro a b hab hmul ha
    have hmulN : ‖ι.symm a‖ * ‖ι.symm b‖ = ‖ι.symm D‖ := by
      rw [← norm_mul, ← map_mul, hmul]
    have hb : ‖ι.symm b‖ < 1 := by
      by_contra h
      push_neg at h
      have : 1 ≤ ‖ι.symm a‖ * ‖ι.symm b‖ := by nlinarith
      linarith
    have hta : ι.symm a = ι.symm t + (-ι.symm b) := by
      rw [← hab, map_add (f := _)]; ring
    have hne : ‖ι.symm t‖ ≠ ‖-ι.symm b‖ := by rw [norm_neg, ht]; exact (ne_of_lt hb).symm
    have ha1 : ‖ι.symm a‖ = 1 := by
      rw [hta, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, ht]
      exact max_eq_left hb.le
    refine ⟨ha1, ?_⟩
    rw [← hmulN, ha1, one_mul]
  have hmax : 1 ≤ max ‖ι.symm ((t + s) / 2)‖ ‖ι.symm ((t - s) / 2)‖ := by
    have := IsUltrametricDist.norm_add_le_max (ι.symm ((t + s) / 2)) (ι.symm ((t - s) / 2))
    rw [← map_add (f := _), hsum, ht] at this
    exact this
  rcases le_max_iff.mp hmax with h | h
  · obtain ⟨h1, h2⟩ := key _ _ hsum hprod h
    exact ⟨_, _, hsum, hprod, h1, h2⟩
  · have hsum' : (t - s) / 2 + (t + s) / 2 = t := by rw [add_comm]; exact hsum
    have hprod' : (t - s) / 2 * ((t + s) / 2) = D := by rw [mul_comm]; exact hprod
    obtain ⟨h1, h2⟩ := key _ _ hsum' hprod' h
    exact ⟨_, _, hsum', hprod', h1, h2⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinaryEisensteinEigenfunctionalExists

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem chapterM_theta : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N →
    (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := GlobalTheory.T.exists_dirichletCharacter_parity_mul_ne_one_mul_inv_ne_one

theorem chapterM_smooth : ∀ (N l e : ℕ) (θ₁ θ₂ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l), 0 < N → l.Prime →
    ¬ l ∣ N → 1 ≤ e → θ₁ ≠ 1 → θ₂ ≠ 1 → ∃ c d : ℕ, 1 < c ∧ 1 < d ∧ c.Coprime (6 * N * l) ∧ d.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c : ℂ) ^ e ≠ z) ∧ ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₁ d ^ n₁ * ψ d ^ n₂) ∧ (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₂ d ^ n₁ * ψ d ^ n₂) := GlobalTheory.T.exists_smoothing_integers_coprime

theorem norm_symm_char_unit {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} [NeZero N]
    (φ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) : ‖ι.symm (φ u)‖ = 1 := by
  have h : (φ u) ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖ι.symm (φ u)‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

theorem chapterM_of_level (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) (he : 1 ≤ e)
    (g : Newform (2 * e + 1)) (hal : ‖ι.symm (g.a l)‖ = 1) (ψ : DirichletCharacter ℂ l)
    (N r : ℕ) (hN : 0 < N) (hr : r.Prime) (hr7 : 7 ≤ r) (hrN : r ∣ N) (hlN : ¬ l ∣ N)
    (χ : DirichletCharacter ℂ N) (g' : ℕ → ℂ) (hprim : Prim (2 * e + 1) N χ g')
    (hg' : ∀ n : ℕ, n.Coprime N → g' n = g.a n) :
    ∃ (θ : DirichletCharacter ℂ N) (α v : ℂ) (B : ℕ) (c : ℕ → ℂ) (c₁ d₁ : ℕ),
      5 ≤ N ∧ ‖ι.symm α‖ = 1 ∧
      α ^ 2 - g.a l * α + χ l * (l : ℂ) ^ (2 * e) = 0 ∧
      EigAll (2 * e + 1) N l χ (fun q => g.a q) α B c ∧ χ (-1) = -1 ∧ θ (-1) = (-1) ^ e * ψ (-1) ∧
      MeasMu ι e ((-1) ^ e * ψ (-1)) (hat θ) (tw2 N ((-1) ^ e * ψ (-1))) ψ α B c v ∧ v ≠ 0 ∧
      1 < c₁ ∧ 1 < d₁ ∧ c₁.Coprime (6 * N * l) ∧ d₁.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c₁ : ℂ) ^ e ≠ z) ∧ ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ) d₁ ^ n₁ * ψ d₁ ^ n₂) ∧
        (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ⁻¹) d₁ ^ n₁ * ψ d₁ ^ n₂) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero N := ⟨hN.ne'⟩
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  have hgl : g' l = g.a l := hg' l hcop

  have hχm1 : χ (-1) = -1 :=
    (GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N 1 χ (1 : DirichletCharacter ℂ 1) g' ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2)
      (odd_two_mul_add_one e) hN one_pos hprim le_rfl).1

  have hψ : ψ (-1) = 1 ∨ ψ (-1) = -1 :=
    mul_self_eq_one_iff.mp (by rw [← map_mul, neg_one_mul, neg_neg, map_one])
  have hsg : (-1 : ℂ) ^ e * ψ (-1) = 1 ∨ (-1 : ℂ) ^ e * ψ (-1) = -1 := by
    rcases neg_one_pow_eq_or ℂ e with h | h <;> rcases hψ with h' | h' <;> simp [h, h']
  obtain ⟨θ, hθm1, hθχ, hθχ'⟩ := chapterM_theta N r χ _ hN hr hr7 hrN hsg

  set u : (ZMod N)ˣ := ZMod.unitOfCoprime l hcop with hu
  have hul : ((u : ZMod N)) = (l : ZMod N) := ZMod.coe_unitOfCoprime l hcop
  have hnχ : ‖ι.symm (χ l)‖ = 1 := by rw [← hul]; exact norm_symm_char_unit ι χ u
  have hnχ' : ‖ι.symm (χ⁻¹ l)‖ = 1 := by rw [← hul]; exact norm_symm_char_unit ι χ⁻¹ u
  have hnl : ‖ι.symm (l : ℂ)‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hlp.one_lt)
  have ht : ‖ι.symm (χ⁻¹ l * g' l)‖ = 1 := by rw [map_mul, norm_mul, hnχ', hgl, hal, one_mul]
  have hD : ‖ι.symm (χ⁻¹ l * (l : ℂ) ^ (2 * e))‖ < 1 := by
    rw [map_mul, norm_mul, hnχ', one_mul, map_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hnl (by omega)
  obtain ⟨α, β, hs, hp, hα, -⟩ := GlobalTheory.unitRoot_split l ι _ _ ht hD

  obtain ⟨B, c, hEig, hval⟩ := GlobalTheory.T.exists_heckeEigenfunctional_depletedEisenstein_ne_zero l ι e N χ θ ψ g' α β he hN hlN hprim hs hp hα hθm1 hθχ

  obtain ⟨x, y, hxy⟩ : IsCoprime (N : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
  have hbez : (N : ℤ) * x * 1 - l * (-y) * 1 = 1 := by linear_combination hxy
  obtain ⟨B', c', hall, hrel⟩ := GlobalTheory.T.eigenfunctionalAllCharacters_of_atkinLehner (2 * e + 1) N l χ g' α B c x (-y) 1 1 hbez (by omega) hN hlp hlN hEig
  have hα0 : α ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hα; exact zero_ne_one hα
  have key := GlobalTheory.T.muModelProduct_value_ne_zero_of_depleted e N l χ⁻¹ θ ψ (fun n => conj (g' n)) α β x (-y) 1 1 hbez he hN hlp hlN
  simp only [inv_inv, Complex.conj_conj] at key
  have hv := key hprim hs hp hα0 hθm1 hθχ B c hEig hval B' c' hrel (fun a ha => hall.U a ha)
  have hmeas := GlobalTheory.T.exists_muModel_measure_of_eigenfunctional l ι e N χ θ ψ (χ l * α) B' c' he hN hlN
    (by rw [map_mul, norm_mul, hnχ, hα, one_mul]) hall.kill hall.U hθm1 hχm1
  obtain ⟨c₁, d₁, hc1, hd1, hc1c, hd1c, hc, hd⟩ := chapterM_smooth N l e (θ * χ) (θ * χ⁻¹) ψ hN hlp hlN he hθχ hθχ'
  refine ⟨θ, χ l * α, _, B', c', c₁, d₁, ?_, ?_, ?_, ?_, hχm1, hθm1, hmeas, ?_, hc1, hd1, hc1c, hd1c, hc, hd⟩
  · have := Nat.le_of_dvd hN hrN; omega
  · rw [map_mul, norm_mul, hnχ, hα, one_mul]
  · have hxy1 : χ l * χ⁻¹ l = 1 := by
      rw [← hul, MulChar.inv_apply_eq_inv', mul_inv_cancel₀]
      exact (u.isUnit.map χ).ne_zero
    rw [hgl] at hs
    linear_combination ((χ l) ^ 2 * α) * hs - (χ l) ^ 2 * hp + (χ l * g.a l * α - χ l * (l : ℂ) ^ (2 * e)) * hxy1
  · refine ⟨⟨fun a ha q hq hqN => ?_, hall.U⟩, hall.kill⟩
    have hqc : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqN (h.trans (dvd_mul_right N l)))
    rw [← hg' q hqc]
    exact hall.T a ha q hq hqN
  · refine mul_ne_zero (div_ne_zero two_ne_zero ?_) hv
    exact_mod_cast (Nat.totient_pos.2 hN).ne'

theorem chapterM_holds : CuspidalUnitaryTwistsClaim := by
  intro l _ hl2 ι e he g hlM hal ψ N₀ hN₀ hlN₀
  have hlp : l.Prime := Fact.out
  obtain ⟨r, hrge, hr⟩ := Nat.exists_infinite_primes (l + 7)
  have hrl : ¬ l ∣ r := by
    intro h
    rcases (Nat.dvd_prime hr).1 h with h1 | h1
    · exact hlp.one_lt.ne' h1
    · omega
  obtain ⟨χ, hprim, hχ⟩ := depleted_newform_prim (2 * e + 1) (N₀ * r) g (by omega) (by nlinarith [hr.two_le])
  have hMpos := g.pos
  have hrpos := hr.pos
  have hN : 0 < g.M * (g.M * (N₀ * r)) ^ 2 := by positivity
  have hL : g.M * (N₀ * r) ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_pow_self _ two_ne_zero).mul_left g.M
  have hrN : r ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_mul_of_dvd_right (dvd_mul_left r N₀) g.M).trans hL
  have hN₀N : N₀ ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_mul_of_dvd_right (dvd_mul_right N₀ r) g.M).trans hL
  have hMN : g.M ∣ g.M * (g.M * (N₀ * r)) ^ 2 := dvd_mul_right _ _
  have hlN : ¬ l ∣ g.M * (g.M * (N₀ * r)) ^ 2 := by
    intro h
    rcases hlp.dvd_mul.1 h with h | h
    · exact hlM h
    · rcases hlp.dvd_mul.1 (hlp.dvd_of_dvd_pow h) with h | h
      · exact hlM h
      · rcases hlp.dvd_mul.1 h with h | h
        · exact hlN₀ h
        · exact hrl h
  have hg' : ∀ n : ℕ, n.Coprime (g.M * (g.M * (N₀ * r)) ^ 2) →
      (fun n => if n.Coprime (g.M * (N₀ * r)) then g.a n else 0) n = g.a n := by
    intro n hn
    simp only [if_pos (hn.coprime_dvd_right hL)]
  obtain ⟨θ, α, v, B, c, c₁, d₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    chapterM_of_level l ι e he g hal ψ _ r hN hr (by omega) hrN hlN χ _ hprim hg'
  exact ⟨_, χ, θ, α, v, B, c, c₁, d₁, h1, hMN, hN₀N, hlN, hχ, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

end GlobalTheory.EisM

end
end
end
