module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondDiagMulEqMulOfDvdLowerLeftGamma1InterGammStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondDiagMulEqMulUpperTriangularOfNotDvdLowerLStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperTriangularMulEqMulUpperTriangularGamma1InteStatement
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesCosetsDistinct

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory

theorem tqFam_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime →
    tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  intro q σ g i i' hq h
  have hq1 : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  have hdet : (mat g).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrArg (· 0 0) h
  have e01 := congrArg (· 0 1) h
  have e10 := congrArg (· 1 0) h
  have e11 := congrArg (· 1 1) h
  simp only [tqFam] at e00 e01 e10 e11
  have hi := i.isLt
  have hi' := i'.isLt
  by_cases h1 : (i : ℕ) < q <;> by_cases h2 : (i' : ℕ) < q <;>
    simp only [h1, h2, if_true, if_false, dg, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at e00 e01 e10 e11
  ·
    apply Fin.ext
    have hg00 : (mat g) 0 0 = 1 := by linarith
    rw [hg00] at e01
    have hii : (0:ℤ) ≤ (i : ℕ) := by positivity
    have hii' : (0:ℤ) ≤ (i' : ℕ) := by positivity
    have hlt : ((i : ℕ) : ℤ) < q := by exact_mod_cast h1
    have hlt' : ((i' : ℕ) : ℤ) < q := by exact_mod_cast h2
    rcases lt_trichotomy ((mat g) 0 1) 0 with hn | hz | hp
    · exfalso; nlinarith
    · rw [hz] at e01; exact_mod_cast (by linarith : ((i : ℕ) : ℤ) = (i' : ℕ))
    · exfalso; nlinarith
  · exfalso
    have hd : (q : ℤ) ∣ 1 := ⟨mat g 0 0 * mat σ 0 0 + mat g 0 1 * mat σ 1 0, by linear_combination e00⟩
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · exfalso
    have hd : (q : ℤ) ∣ 1 := by
      rw [← hdet]
      exact Dvd.dvd.sub (Dvd.dvd.mul_right ⟨mat σ 0 0, by linear_combination -e00⟩ _)
        (Dvd.dvd.mul_left ⟨mat σ 1 0, by linear_combination -e10⟩ _)
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · apply Fin.ext; omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesCosetsDistinctStatement

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

theorem _root_.GlobalTheory.T.heckeTqRepresentatives_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime → tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  first | exact @GlobalTheory.tqFam_cosets_distinct | exact GlobalTheory.tqFam_cosets_distinct | (intros; apply GlobalTheory.tqFam_cosets_distinct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperMulEqMulDiamondDiagGamma1InterGamma0

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

theorem upper_mul_eq_mul_diamond_diag : ∀ (N l q j : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ →
    j < q → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 →
    ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * (mat σ * dg q 1) := by
  intro N l q j σ γ _ _ hσ _ hγ hdiv
  obtain ⟨t, ht⟩ := hdiv
  obtain ⟨hσ10, hσ11⟩ := hσ
  have hγ1 := (Gamma1_mem N γ).1 (Subgroup.mem_inf.1 hγ).1
  have hcl := Gamma0_mem.1 (Subgroup.mem_inf.1 hγ).2
  obtain ⟨ha, hd, hc⟩ := hγ1
  have hdγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hdσ : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have ht' : γ 0 0 + (j : ℤ) * γ 1 0 = q * t := ht
  have hM : Matrix.det !![t * σ 1 1 - (γ 0 1 + j * γ 1 1) * σ 1 0, (γ 0 1 + j * γ 1 1) * σ 0 0 - t * σ 0 1;
      γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0, q * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (q * t * γ 1 1 - (γ 0 1 + j * γ 1 1) * γ 1 0) * hdσ + hdγ - γ 1 1 * ht'
  have hdvd : ((N * l : ℕ) : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ10
  have h10N : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans ⟨l, by push_cast; ring⟩ hdvd)
  have h10l : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans ⟨N, by push_cast; ring⟩ hdvd)
  have hdN := congrArg (fun x : ℤ => (x : ZMod N)) hdσ
  have htN := congrArg (fun x : ℤ => (x : ZMod N)) ht'
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast, h10N, hσ11, ha, hc] at hdN htN
  refine ⟨⟨_, hM⟩, Subgroup.mem_inf.2 ⟨(Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩, ?_⟩
  · show ((t * σ 1 1 - (γ 0 1 + j * γ 1 1) * σ 1 0 : ℤ) : ZMod N) = 1
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, h10N, hσ11]
    linear_combination -htN
  · show ((q * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1 : ℤ) : ZMod N) = 1
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hc, hd]
    linear_combination hdN
  · show ((γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0 : ℤ) : ZMod N) = 0
    simp only [Int.cast_sub, Int.cast_mul, hc, h10N]
    ring
  · show ((γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0 : ℤ) : ZMod l) = 0
    simp only [Int.cast_sub, Int.cast_mul, hcl, h10l]
    ring
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [mat, dg, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination ht' - q * t * hdσ
    · linear_combination -(γ 0 1 + j * γ 1 1) * hdσ
    · linear_combination -(q * γ 1 0) * hdσ
    · linear_combination -(q * γ 1 1) * hdσ

end GlobalTheory.Hk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperMulEqMulDiamondDiagGamma1InterGamma0Statement

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

theorem _root_.GlobalTheory.T.upper_mul_eq_mul_diamond_diag_gamma1InterGamma0 : ∀ (N l q j : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → j < q → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * (mat σ * dg q 1) := by
  first | exact @GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag | exact GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag | (intros; apply GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTSlashInvariant

section

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HkInv
open GlobalTheory.HeckeFamilyMatrices

theorem reps (N l q : ℕ) (σ γ : SL(2, ℤ)) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ)
    (hγ : γ ∈ GlobalTheory.Hk.lev N l) (i : Fin (q + 1)) :
    ∃ i' : Fin (q + 1), ∃ γ' ∈ GlobalTheory.Hk.lev N l, tqFam q σ i * mat γ = mat γ' * tqFam q σ i' := by
  by_cases hi : (i : ℕ) < q
  · have e : tqFam q σ i = !![(1 : ℤ), ((i : ℕ) : ℤ); 0, (q : ℤ)] := by rw [tqFam, if_pos hi]
    rw [e]
    by_cases hd : (q : ℤ) ∣ mat γ 0 0 + ((i : ℕ) : ℤ) * mat γ 1 0
    · obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.upper_mul_eq_mul_diamond_diag_gamma1InterGamma0 N l q i σ γ hq hqN hσ hi hγ hd
      refine ⟨Fin.last q, γ', h1, ?_⟩
      rw [h2, tqFam, if_neg (by simp)]
    · obtain ⟨j', hj', γ', h1, h2⟩ := GlobalTheory.T.upperTriangular_mul_eq_mul_upperTriangular_gamma1InterGamma0 N l q i γ hq hqN hi hγ hd
      refine ⟨⟨j', by omega⟩, γ', h1, ?_⟩
      rw [h2, tqFam, if_pos (by simpa using hj')]
  · have e : tqFam q σ i = mat σ * dg q 1 := by rw [tqFam, if_neg hi]
    rw [e]
    by_cases hd : (q : ℤ) ∣ mat γ 1 0
    · obtain ⟨γ', h1, h2⟩ := GlobalTheory.T.diamond_diag_mul_eq_mul_of_dvd_lowerLeft_gamma1InterGamma0 N l q σ γ hq hqN hσ hγ hd
      refine ⟨Fin.last q, γ', h1, ?_⟩
      rw [h2, tqFam, if_neg (by simp)]
    · obtain ⟨j', hj', γ', h1, h2⟩ := GlobalTheory.T.diamond_diag_mul_eq_mul_upperTriangular_of_not_dvd_lowerLeft N l q σ γ hq hqN hσ hγ hd
      refine ⟨⟨j', by omega⟩, γ', h1, ?_⟩
      rw [h2, tqFam, if_pos (by simpa using hj')]

theorem perm (N l q : ℕ) (σ γ : SL(2, ℤ)) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ)
    (hγ : γ ∈ GlobalTheory.Hk.lev N l) :
    ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  choose π g hg he using reps N l q σ γ hq hqN hσ hγ
  have hinj : Function.Injective π := by
    intro i₁ i₂ h
    have e1 := he i₁
    have e2 := he i₂
    rw [h] at e1
    apply GlobalTheory.T.heckeTqRepresentatives_cosets_distinct q σ (g i₁ * (g i₂)⁻¹) i₁ i₂ hq
    have hγi : mat γ * mat γ⁻¹ = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgi : mat (g i₂)⁻¹ * mat (g i₂) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc tqFam q σ i₁ = tqFam q σ i₁ * mat γ * mat γ⁻¹ := by rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
      _ = mat (g i₁) * (mat (g i₂)⁻¹ * (mat (g i₂) * tqFam q σ (π i₂))) * mat γ⁻¹ := by
          rw [e1, ← Matrix.mul_assoc (mat (g i₂)⁻¹), hgi, Matrix.one_mul]
      _ = mat (g i₁ * (g i₂)⁻¹) * (tqFam q σ i₂ * mat γ * mat γ⁻¹) := by
          rw [← e2, show mat (g i₁ * (g i₂)⁻¹) = mat (g i₁) * mat (g i₂)⁻¹ from Matrix.SpecialLinearGroup.coe_mul _ _]
          simp only [Matrix.mul_assoc]
      _ = mat (g i₁ * (g i₂)⁻¹) * tqFam q σ i₂ := by rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
  exact ⟨Equiv.ofBijective π hinj.bijective_of_finite, fun i => ⟨g i, hg i, he i⟩⟩

theorem det_tqFam (q : ℕ) (hq : 0 < q) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : (tqFam q σ i).det ≠ 0 := by
  unfold tqFam
  split_ifs
  · simp [Matrix.det_fin_two_of, hq.ne']
  · rw [Matrix.det_mul]; simp [dg, Matrix.det_fin_two_of, hq.ne']

theorem heckeT_slash_invariant : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → (∀ γ ∈ GlobalTheory.Hk.lev N l, f ∣[k] γ = f) →
    ∀ γ ∈ GlobalTheory.Hk.lev N l, GlobalTheory.Hk.heckeT k q σ f ∣[k] γ = GlobalTheory.Hk.heckeT k q σ f := by
  intro N l q k σ f _ hq hqN hσ hf γ hγ
  obtain ⟨π, hπ⟩ := perm N l q σ γ hq hqN hσ hγ
  have hq0 := hq.pos
  have hmat : (mat γ).det ≠ 0 := by simp [mat]
  rw [← GlobalTheory.SlashUpperTriangularMatrices.tq_eq k q σ f hq0, TqF, hkF]
  have key : ∀ i, (f ∣[k] toGL (tqFam q σ i)) ∣[k] γ = f ∣[k] toGL (tqFam q σ (π i)) := by
    intro i
    obtain ⟨γ', hγ', he⟩ := hπ i
    have hmat' : (mat γ').det ≠ 0 := by simp [mat]
    rw [ModularForm.SL_slash, ← SlashAction.slash_mul, ← GlobalTheory.SlashUpperTriangularMatrices.toGL_SL,
      ← GlobalTheory.SlashUpperTriangularMatrices.toGL_mul _ _ (det_tqFam q hq0 σ i) hmat, he,
      GlobalTheory.SlashUpperTriangularMatrices.toGL_mul _ _ hmat' (det_tqFam q hq0 σ _), SlashAction.slash_mul,
      GlobalTheory.SlashUpperTriangularMatrices.toGL_SL, ← ModularForm.SL_slash, hf γ' hγ']
  have hsum : ∀ (s : Finset (Fin (q + 1))) (F : Fin (q + 1) → ℍ → ℂ),
      (∑ i ∈ s, F i) ∣[k] γ = ∑ i ∈ s, F i ∣[k] γ := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simp [SlashAction.zero_slash]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  rw [hsum, Finset.sum_congr rfl (fun i _ => key i)]
  exact Equiv.sum_comp π (fun i => f ∣[k] toGL (tqFam q σ i))

end GlobalTheory.HkInv
end
end
