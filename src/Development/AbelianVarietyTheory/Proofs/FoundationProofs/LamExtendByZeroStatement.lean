module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearFunctionalEqCoeffLinearCombinationFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlane
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FormsOfCharactersIndependent

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.EisM.Indep

theorem qs_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℂ) (ha : ∀ i, PolyB (a i)) :
    qs (∑ i ∈ s, a i) = ∑ i ∈ s, qs (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.EisM.Lin.qs_zero
  | insert i s hi ih =>
    have hp : PolyB (∑ j ∈ s, a j) := by
      clear ih hi
      induction s using Finset.induction_on with
      | empty => simpa using GlobalTheory.EisM.Lin.polyB_zero
      | insert j t hj ih2 =>
        rw [Finset.sum_insert hj]; exact GlobalTheory.EisM.Lin.polyB_add _ _ (ha j) ih2
    rw [Finset.sum_insert hi, Finset.sum_insert hi, GlobalTheory.EisM.Lin.qs_add _ _ (ha i) hp, ih]

theorem exists_gamma (L N : ℕ) (hL : 0 < L) (hNL : N ∣ L) (u : (ZMod N)ˣ) :
    ∃ γ : SL(2, ℤ), γ 1 0 = (L : ℤ) ∧ ((γ 1 1 : ℤ) : ZMod N) = u := by
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hNL u
  have hc : Nat.Coprime (v : ZMod L).val L := ZMod.val_coe_unit_coprime v
  have hc' : IsCoprime (((v : ZMod L).val : ℕ) : ℤ) (L : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨x, y, hxy⟩ := hc'
  refine ⟨⟨!![x, -y; (L : ℤ), (((v : ZMod L).val : ℕ) : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hxy
  · simp
  · simp only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← hv, ZMod.unitsMap_val, ZMod.cast_eq_val, Int.cast_natCast]

theorem forms_of_characters_independent : ∀ (k L N : ℕ) (a : DirichletCharacter ℂ N → ℕ → ℂ), 0 < L → N ∣ L →
    (∀ ε, MF k L (ch ε) (a ε)) → (∑ ε, a ε) = 0 → ∀ ε, a ε = 0 := by
  intro k L N a hL hNL hmf hsum ε₀
  have hN : N ≠ 0 := by rintro rfl; exact hL.ne' (Nat.eq_zero_of_zero_dvd hNL)
  haveI : NeZero N := ⟨hN⟩
  set f : DirichletCharacter ℂ N → ℍ → ℂ := fun ε => qs (a ε) with hf
  have hfs : ∑ ε, f ε = 0 := by
    rw [hf, ← qs_finset_sum _ _ (fun ε => (hmf ε).1), hsum]; exact GlobalTheory.EisM.Lin.qs_zero

  have key : ∀ (b : ZMod N) (τ : ℍ), ∑ ε, ε b * f ε τ = 0 := by
    intro b τ
    by_cases hb : IsUnit b
    · obtain ⟨u, rfl⟩ := hb
      obtain ⟨γ, h10, h11⟩ := exists_gamma L N hL hNL u
      have hdiv : (L : ℤ) ∣ γ 1 0 := by rw [h10]
      have hj : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) ≠ 0 := by
        apply pow_ne_zero
        intro h0
        have him := congrArg Complex.im h0
        simp only [h10, Int.cast_natCast, Complex.add_im, Complex.mul_im, Complex.natCast_re,
          Complex.natCast_im, Complex.intCast_im, zero_mul, add_zero, Complex.zero_im] at him
        have : (0 : ℝ) < (L : ℝ) * (τ : ℂ).im := mul_pos (by exact_mod_cast hL) τ.im_pos
        linarith
      have e : ∀ ε, f ε (γ • τ) = ε (u : ZMod N) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * f ε τ := by
        intro ε
        rw [hf]; dsimp only
        rw [(hmf ε).2 γ hdiv τ, ch, h11]
      have h0 : ∑ ε, f ε (γ • τ) = 0 := by
        have := congrFun hfs (γ • τ); simpa [Finset.sum_apply] using this
      simp only [e] at h0
      have h1 : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * ∑ ε, ε (u : ZMod N) * f ε τ = 0 := by
        rw [Finset.mul_sum, ← h0]; exact Finset.sum_congr rfl (fun ε _ => by ring)
      exact (mul_eq_zero.mp h1).resolve_left hj
    · exact Finset.sum_eq_zero (fun ε _ => by rw [MulChar.map_nonunit ε hb, zero_mul])
  funext n
  have hq : f ε₀ = 0 := by
    funext τ
    have hT : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = 0 :=
      Finset.sum_eq_zero (fun b _ => by rw [key b τ, mul_zero])
    have hT' : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = ∑ ε, f ε τ * ∑ b : ZMod N, (ε₀⁻¹ * ε) b := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [MulChar.coeToFun_mul, Pi.mul_apply]; ring
    rw [hT'] at hT
    rw [Finset.sum_eq_single ε₀] at hT
    · rw [inv_mul_cancel, MulChar.sum_one_eq_card_units] at hT
      have hc : ((Fintype.card (ZMod N)ˣ : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simpa [hc, hN] using hT
    · intro ε _ hne
      rw [MulChar.sum_eq_zero_of_ne_one, mul_zero]
      intro h1; apply hne
      have := congrArg (ε₀ * ·) h1
      simpa using this
    · intro h; exact absurd (Finset.mem_univ _) h
  have := qs_injective (a ε₀) 0 (hmf ε₀).1 GlobalTheory.EisM.Lin.polyB_zero (by rw [GlobalTheory.EisM.Lin.qs_zero]; exact hq)
  simpa using congrFun this n

end GlobalTheory.EisM.Indep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FormsOfCharactersIndependentStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eq_zero_of_mf_ch_sum_eq_zero : ∀ (k L N : ℕ) (a : DirichletCharacter ℂ N → ℕ → ℂ), 0 < L → N ∣ L → (∀ ε, MF k L (ch ε) (a ε)) → (∑ ε, a ε) = 0 → ∀ ε, a ε = 0 := by
  first | exact @GlobalTheory.EisM.Indep.forms_of_characters_independent | exact GlobalTheory.EisM.Indep.forms_of_characters_independent | (intros; apply GlobalTheory.EisM.Indep.forms_of_characters_independent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SturmSumOverCharactersEqZero

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem sturm_sum_coef_zero : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ,
    (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := by
  classical
  intro k L N hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  choose f hf using fun ε => modularForm_gammaOne_of_MF k L N ε (a ε) hL hN (ha ε)
  have hc : ∀ ε n, (qExpansion 1 (f ε)).coeff n = a ε n := by
    intro ε n
    have := coef_qs (a ε) (ha ε).1 n
    unfold coef at this
    rw [← this, hf]
  have hsum : ∀ (s : Finset (DirichletCharacter ℂ N)) (n : ℕ),
      (qExpansion 1 ⇑(∑ ε ∈ s, f ε)).coeff n = ∑ ε ∈ s, a ε n := by
    intro s n
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ModularForm.coe_zero, qExpansion_zero, map_zero]
    | insert e s he ih =>
      rw [Finset.sum_insert he, ModularForm.coe_add, ModularForm.qExpansion_add one_pos hΓ, map_add (f := _), ih, hc, Finset.sum_insert he]
  have h0 : ∑ ε, f ε = 0 := hm _ fun n hn => by
    rw [hsum]
    simpa [Finset.sum_apply] using hz n hn
  funext n
  have := hsum Finset.univ n
  rw [h0] at this
  rw [ModularForm.coe_zero, qExpansion_zero, map_zero] at this
  rw [Finset.sum_apply, ← this]
  rfl

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SturmSumOverCharactersEqZeroStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.sturm_sum_over_characters_eq_zero : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ, (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := by
  first | exact @GlobalTheory.EisM.sturm_sum_coef_zero | exact GlobalTheory.EisM.sturm_sum_coef_zero | (intros; apply GlobalTheory.EisM.sturm_sum_coef_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamExtendByZero

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory


open Classical in
theorem lam_extend_by_zero : ∀ (k L N : ℕ) (χ₀ : DirichletCharacter ℂ N) (B : ℕ) (c : ℕ → ℂ), 0 < L → N ∣ L →
    ∃ (B' : ℕ) (c' : ℕ → ℂ), (∀ a, MF k L (ch χ₀) a → lam B' c' a = lam B c a) ∧
      ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ₀ → MF k L (ch ε) a → lam B' c' a = 0 := by
  intro k L N χ₀ B c hL hN
  have lin := GlobalTheory.T.modularFormCoeffSeq_linear_structure k L
  let Fam : (DirichletCharacter ℂ N → ℕ → ℂ) → Prop := fun a => ∀ ε, MF k L (ch ε) (a ε)
  have uniq : ∀ a b, Fam a → Fam b → (∑ ε, a ε) = ∑ ε, b ε → a = b := by
    intro a b ha hb hab
    have hd : Fam (fun ε => a ε + (-1 : ℂ) • b ε) := fun ε =>
      ((lin (ch ε)).2.1 _ _ (ha ε) ((lin (ch ε)).2.2.1 (-1) _ (hb ε)).1).1
    have h0 := GlobalTheory.T.eq_zero_of_mf_ch_sum_eq_zero k L N (fun ε => a ε + (-1 : ℂ) • b ε) hL hN hd (by
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, hab, neg_one_smul, add_neg_cancel])
    funext ε
    have h1 : a ε + (-1 : ℂ) • b ε = 0 := h0 ε
    rw [neg_one_smul, ← sub_eq_add_neg] at h1
    exact sub_eq_zero.mp h1
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.T.sturm_sum_over_characters_eq_zero k L N hL hN
  let S : Set (ℕ → ℂ) := {s | ∃ a, Fam a ∧ s = ∑ ε, a ε}
  let rep : (ℕ → ℂ) → DirichletCharacter ℂ N → ℕ → ℂ := fun s => if h : s ∈ S then Classical.choose h else 0
  have rep_spec : ∀ a, Fam a → rep (∑ ε, a ε) = a := by
    intro a ha
    have hs : (∑ ε, a ε) ∈ S := ⟨a, ha, rfl⟩
    simp only [rep, dif_pos hs]
    have h := Classical.choose_spec hs
    exact uniq _ _ h.1 ha h.2.symm
  let φ : (ℕ → ℂ) → ℂ := fun s => lam B c (rep s χ₀)
  have lam_add : ∀ x y : ℕ → ℂ, lam B c (x + y) = lam B c x + lam B c y := by
    intro x y; simp only [lam, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have lam_smul : ∀ (t : ℂ) (x : ℕ → ℂ), lam B c (t • x) = t * lam B c x := by
    intro t x; simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  obtain ⟨c', hc'⟩ := GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite S B₀ φ
    ⟨0, fun ε => (lin (ch ε)).1, by simp⟩
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab : Fam (a + b) := fun ε => ((lin (ch ε)).2.1 _ _ (ha ε) (hb ε)).1
      have e : (∑ ε, a ε) + ∑ ε, b ε = ∑ ε, (a + b) ε := by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      refine ⟨⟨a + b, hab, e⟩, ?_⟩
      show lam B c (rep _ χ₀) = lam B c (rep _ χ₀) + lam B c (rep _ χ₀)
      rw [e, rep_spec _ hab, rep_spec _ ha, rep_spec _ hb]
      exact lam_add _ _)
    (by
      rintro t _ ⟨a, ha, rfl⟩
      have hta : Fam (t • a) := fun ε => ((lin (ch ε)).2.2.1 t _ (ha ε)).1
      have e : t • ∑ ε, a ε = ∑ ε, (t • a) ε := by
        simp only [Pi.smul_apply, Finset.smul_sum]
      refine ⟨⟨t • a, hta, e⟩, ?_⟩
      show lam B c (rep _ χ₀) = t * lam B c (rep _ χ₀)
      rw [e, rep_spec _ hta, rep_spec _ ha]
      exact lam_smul _ _)
    (by
      rintro _ ⟨a, ha, rfl⟩ h
      exact hB₀ a ha h)
  have single : ∀ (ε₀ : DirichletCharacter ℂ N) (a : ℕ → ℂ), MF k L (ch ε₀) a →
      lam B₀ c' a = lam B c (if ε₀ = χ₀ then a else 0) := by
    intro ε₀ a ha
    let fa : DirichletCharacter ℂ N → ℕ → ℂ := fun ε => if ε = ε₀ then a else 0
    have hfa : Fam fa := by
      intro ε
      by_cases h : ε = ε₀
      · subst h; simp only [fa, if_pos rfl]; exact ha
      · simp only [fa, if_neg h]; exact (lin (ch ε)).1
    have hs : ∑ ε, fa ε = a := by simp [fa]
    have h := hc' _ ⟨fa, hfa, rfl⟩
    simp only [φ] at h
    rw [rep_spec _ hfa, hs] at h
    rw [← h]
    by_cases h' : ε₀ = χ₀
    · subst h'; simp [fa]
    · simp [fa, h', Ne.symm h']
  refine ⟨B₀, c', fun a ha => by simpa using single χ₀ a ha, fun ε a hε ha => ?_⟩
  rw [single ε a ha, if_neg hε]
  simp [lam]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamExtendByZeroStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_lam_eq_and_vanishes_off_character : ∀ (k L N : ℕ) (χ₀ : DirichletCharacter ℂ N) (B : ℕ) (c : ℕ → ℂ), 0 < L → N ∣ L → ∃ (B' : ℕ) (c' : ℕ → ℂ), (∀ a, MF k L (ch χ₀) a → lam B' c' a = lam B c a) ∧ ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ₀ → MF k L (ch ε) a → lam B' c' a = 0 := by
  first | exact @GlobalTheory.lam_extend_by_zero | exact GlobalTheory.lam_extend_by_zero | (intros; apply GlobalTheory.lam_extend_by_zero <;> assumption)
end
end
