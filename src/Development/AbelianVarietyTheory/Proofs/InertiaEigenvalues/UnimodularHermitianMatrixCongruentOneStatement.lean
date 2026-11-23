module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitNormalFormUnitInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
public import Mathlib.Analysis.Normed.Group.Ultra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormOneAddEqOne

section

@[expose] public section

namespace GlobalTheory.UnitValueExistence

open Matrix

theorem norm_add_lt_one {E : Type} [NormedField E] [IsUltrametricDist E] {a b : E}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

theorem norm_one_add_eq_one {E : Type} [NormedField E] [IsUltrametricDist E] {a : E}
    (ha : ‖a‖ < 1) : ‖1 + a‖ = 1 := by
  have h : ‖(1 : E)‖ ≠ ‖a‖ := by rw [norm_one]; exact ha.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, norm_one, max_eq_left ha.le]

theorem norm_det_lt_one {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (h : ∀ i j, ‖G i j‖ < 1) : ‖G.det‖ < 1 := by
  rw [Matrix.det_apply']
  refine Finset.sum_induction _ (fun x : E => ‖x‖ < 1) (fun a b ha hb => norm_add_lt_one ha hb)
    (by simp) ?_
  intro σ _
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [norm_mul, hs, one_mul, norm_prod]
  obtain ⟨i⟩ := ‹Nonempty n›
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h2 : ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => (h _ _).le)
  calc ‖G (σ i) i‖ * ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ ‖G (σ i) i‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact h _ _

theorem exists_unit_value {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he : ‖e0‖ ≤ (1 : ℝ)) (htr : e0 + star e0 = 1)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (hG : Matrix.IsHermitian G) (hint : ∀ i j, ‖G i j‖ ≤ (1 : ℝ)) (hdet : ‖G.det‖ = (1 : ℝ)) :
    ∃ (i : n) (w : n → E), (∀ a, ‖w a‖ ≤ (1 : ℝ)) ∧ w i = 1 ∧
      ‖star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ) := by
  by_cases hd : ∃ i, ‖G i i‖ = 1
  · obtain ⟨i, hi⟩ := hd
    refine ⟨i, Pi.single i 1, ?_, by simp, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp
      · simp [Pi.single_eq_of_ne ha]
    · have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
        rw [Pi.star_single, star_one]
      rw [hs, single_dotProduct, Matrix.mulVec_single_one]
      simpa using hi
  · have hdiag : ∀ i, ‖G i i‖ < 1 := fun i =>
      lt_of_le_of_ne (hint i i) (fun h => hd ⟨i, h⟩)
    have hex : ∃ i j, ‖G i j‖ = 1 := by
      by_contra hne
      have := norm_det_lt_one G (fun i j => lt_of_le_of_ne (hint i j) (fun h => hne ⟨i, j, h⟩))
      exact this.ne hdet
    obtain ⟨i, j, hij⟩ := hex
    have hne : i ≠ j := by
      rintro rfl
      exact (hdiag i).ne hij
    have hg0 : G i j ≠ 0 := by
      intro h; rw [h, norm_zero] at hij; exact zero_ne_one hij
    set t : E := e0 / G i j with ht
    have htn : ‖t‖ ≤ 1 := by rw [ht, norm_div, hij, div_one]; exact he
    have htG : G i j * t = e0 := by rw [ht]; field_simp
    have hji : G j i = star (G i j) := (hG.apply j i).symm
    have htG' : star t * G j i = star e0 := by rw [hji, ← star_mul, htG]
    refine ⟨i, Pi.single i 1 + Pi.single j t, ?_, ?_, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp [Pi.single_eq_of_ne hne]
      · by_cases hb : a = j
        · subst hb; simpa [Pi.single_eq_of_ne ha] using htn
        · simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
    · simp [Pi.single_eq_of_ne hne]
    · have hs : star (Pi.single i (1 : E) + Pi.single j t : n → E)
          = Pi.single i 1 + Pi.single j (star t) := by
        rw [star_add, Pi.star_single, Pi.star_single, star_one]
      have key : star (Pi.single i (1 : E) + Pi.single j t : n → E) ⬝ᵥ
          Matrix.mulVec G (Pi.single i 1 + Pi.single j t)
          = 1 + (G i i + star t * (G j j * t)) := by
        rw [hs, add_dotProduct, single_dotProduct, single_dotProduct, Matrix.mulVec_add]
        simp only [Pi.add_apply, Matrix.mulVec, dotProduct_single]
        linear_combination htG + htG' + htr
      rw [key]
      apply norm_one_add_eq_one
      apply norm_add_lt_one (hdiag i)
      rw [norm_mul, norm_mul, hstar]
      have h1 := hdiag j
      have h2 := norm_nonneg t
      have h3 := norm_nonneg (G j j)
      have h4 : ‖G j j‖ * ‖t‖ ≤ ‖G j j‖ := mul_le_of_le_one_right h3 htn
      have h5 : ‖t‖ * (‖G j j‖ * ‖t‖) ≤ ‖G j j‖ * ‖t‖ :=
        mul_le_of_le_one_left (mul_nonneg h3 h2) htn
      linarith

theorem main : (let d1 : {E : Type} → [NormedField E] → {n m : Type} → Matrix n m E → Prop := @(fun {E : Type} [NormedField E] {n m : Type} (h : Matrix n m E) ↦ ∀ (i : n) (j : m), ‖h i j‖ ≤ (1 : ℝ)); ∀ {E : Type} [inst : NormedField E] [IsUltrametricDist E] [inst_2 : StarRing E], (∀ (y : E), ‖Star.star y‖ = ‖y‖) → ∀ (e0 : E), ‖e0‖ ≤ (1 : ℝ) → e0 + Star.star e0 = (1 : E) → ∀ {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] [Nonempty n] (G : Matrix n n E), Matrix.IsHermitian G → d1 G → ‖Matrix.det G‖ = (1 : ℝ) → ∃ (i : n) (w : n → E), (∀ (a : n), ‖w a‖ ≤ (1 : ℝ)) ∧ w i = (1 : E) ∧ ‖Star.star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ)) := by
  intro d1 E _ _ _ hstar e0 he htr n _ _ _ G hG hint hdet
  exact exists_unit_value hstar e0 he htr G hG hint hdet

end GlobalTheory.UnitValueExistence
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHermitianMatrixCongruentOne

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.HermUnimod

section Gen

variable {E : Type} [NormedField E]

def Intg {n m : Type} (h : Matrix n m E) : Prop := ∀ i j, ‖h i j‖ ≤ 1

theorem nsum_le [IsUltrametricDist E] {ι : Type} (s : Finset ι) (f : ι → E) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i ∈ s, ‖f i‖ ≤ r) :
    ‖∑ i ∈ s, f i‖ ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem intg_mul [IsUltrametricDist E] {l n m : Type} [Fintype n] {A : Matrix l n E} {B : Matrix n m E} (hA : Intg A)
    (hB : Intg B) : Intg (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine nsum_le _ _ zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

theorem intg_conjT [StarRing E] (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n m : Type} {A : Matrix n m E} (hA : Intg A) :
    Intg Aᴴ := by
  intro i j
  rw [conjTranspose_apply, hs]
  exact hA j i

theorem intg_one {n : Type} [DecidableEq n] : Intg (1 : Matrix n n E) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem norm_det_conjT [StarRing E] (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n E) : ‖Aᴴ.det‖ = ‖A.det‖ := by
  rw [det_conjTranspose, hs]

def Good (n : Type) [Fintype n] [DecidableEq n] (E : Type) [NormedField E] [StarRing E] : Prop :=
  ∀ G : Matrix n n E, G.IsHermitian → (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 →
    ∃ h : Matrix n n E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1

end Gen

section Step

variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem intg_fromBlocks {l m n o : Type} {A : Matrix n l E} {B : Matrix n m E} {C : Matrix o l E}
    {D : Matrix o m E} (hA : Intg A) (hB : Intg B) (hC : Intg C) (hD : Intg D) :
    Intg (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem intg_sub {n m : Type} {A B : Matrix n m E} (hA : Intg A) (hB : Intg B) : Intg (A - B) := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (by rw [norm_neg]; exact hB i j))

theorem intg_neg {n m : Type} {A : Matrix n m E} (hA : Intg A) : Intg (-A) := by
  intro i j
  change ‖-(A i j)‖ ≤ 1
  rw [norm_neg]
  exact hA i j

theorem intg_zero {n m : Type} : Intg (0 : Matrix n m E) := by
  intro i j
  simp

theorem schur_conj {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m E) (B : Matrix m Unit E) :
    (fromBlocks 1 0 (-Bᴴ) 1 : Matrix (m ⊕ Unit) (m ⊕ Unit) E)ᴴ * fromBlocks A B Bᴴ 1 *
        fromBlocks 1 0 (-Bᴴ) 1 = fromBlocks (A - B * Bᴴ) 0 0 1 := by
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_add_neg]

theorem good_sum (hs : ∀ y : E, ‖star y‖ = ‖y‖) {m : Type} [Fintype m] [DecidableEq m] (H : Good m E)
    (G : Matrix (m ⊕ Unit) (m ⊕ Unit) E) (hG : G.IsHermitian) (hGi : ∀ i j, ‖G i j‖ ≤ 1)
    (hGd : ‖G.det‖ = 1) (hk : G (Sum.inr ()) (Sum.inr ()) = 1) :
    ∃ h : Matrix (m ⊕ Unit) (m ⊕ Unit) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  have hD : G.toBlocks₂₂ = 1 := by
    ext ⟨⟩ ⟨⟩
    simp [toBlocks₂₂, hk]
  have hG' : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₁ 1 := by
    rw [← hD, fromBlocks_toBlocks]
  set A := G.toBlocks₁₁
  set B := G.toBlocks₁₂
  set C := G.toBlocks₂₁
  have hh := hG
  rw [hG', isHermitian_fromBlocks_iff] at hh
  obtain ⟨hA, hBC, -, -⟩ := hh
  rw [← hBC] at hG'
  have hAi : Intg A := fun i j => hGi _ _
  have hBi : Intg B := fun i j => hGi _ _
  have hA'i : Intg (A - B * Bᴴ) := intg_sub hAi (intg_mul hBi (intg_conjT hs hBi))
  have hA'h : (A - B * Bᴴ).IsHermitian := hA.sub (isHermitian_mul_conjTranspose_self B)
  have hA'd : ‖(A - B * Bᴴ).det‖ = 1 := by
    rw [← det_fromBlocks_one₂₂, ← hG']
    exact hGd
  obtain ⟨h', hi', hd', hh'⟩ := H _ hA'h hA'i hA'd
  refine ⟨fromBlocks 1 0 (-Bᴴ) 1 * fromBlocks h' 0 0 1, ?_, ?_, ?_⟩
  · exact intg_mul (intg_fromBlocks intg_one intg_zero (intg_neg (intg_conjT hs hBi)) intg_one)
      (intg_fromBlocks hi' intg_zero intg_zero intg_one)
  · rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
    simp [hd']
  · rw [conjTranspose_mul, hG']
    calc (fromBlocks h' 0 0 1)ᴴ * (fromBlocks 1 0 (-Bᴴ) 1)ᴴ * fromBlocks A B Bᴴ 1 *
          (fromBlocks 1 0 (-Bᴴ) 1 * fromBlocks h' 0 0 1)
        = (fromBlocks h' 0 0 1)ᴴ * ((fromBlocks 1 0 (-Bᴴ) 1)ᴴ * fromBlocks A B Bᴴ 1 *
          fromBlocks 1 0 (-Bᴴ) 1) * fromBlocks h' 0 0 1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [schur_conj]
        simp [fromBlocks_conjTranspose, fromBlocks_multiply, hh']

end Step

section Main

variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem sol_transfer (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n') (G : Matrix n n E) (h : Matrix n' n' E) (hi : ∀ i j, ‖h i j‖ ≤ 1)
    (hd : ‖h.det‖ = 1) (hh : hᴴ * reindex e e G * h = 1) :
    ∃ h : Matrix n n E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  refine ⟨reindex e.symm e.symm h, fun i j => hi _ _, by rw [det_reindex_self]; exact hd, ?_⟩
  have : reindex e.symm e.symm (hᴴ * reindex e e G * h) = 1 := by rw [hh]; simp
  rw [← this]
  simp only [reindex_apply, Equiv.symm_symm, conjTranspose_submatrix]
  rw [← submatrix_mul_equiv (hᴴ * _) h e e e, ← submatrix_mul_equiv hᴴ _ e e e]
  simp

theorem good_all (hs : ∀ y : E, ‖star y‖ = ‖y‖)
    (piv : ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E), G.IsHermitian →
      Intg G → ‖G.det‖ = 1 → ∃ P : Matrix n n E, Intg P ∧ ‖P.det‖ = 1 ∧ ∃ k, (Pᴴ * G * P) k k = 1) :
    ∀ (m : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = m → Good n E := by
  intro m
  induction m with
  | zero =>
    intro n _ _ hc G _ _ _
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.1 hc
    refine ⟨1, fun i => isEmptyElim i, by simp, ?_⟩
    ext i
    exact isEmptyElim i
  | succ m ih =>
    intro n _ _ hc G hG hGi hGd
    haveI : Nonempty n := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨P, hPi, hPd, k, hk⟩ := piv n G hG hGi hGd
    have hM : (Pᴴ * G * P).IsHermitian := isHermitian_conjTranspose_mul_mul P hG
    have hMi : Intg (Pᴴ * G * P) := intg_mul (intg_mul (intg_conjT hs hPi) hGi) hPi
    have hMd : ‖(Pᴴ * G * P).det‖ = 1 := by
      rw [det_mul, det_mul, norm_mul, norm_mul, norm_det_conjT hs, hPd, hGd, one_mul, one_mul]
    let e : n ≃ {j // j ≠ k} ⊕ Unit :=
      (Equiv.optionSubtypeNe k).symm.trans (Equiv.optionEquivSumPUnit.{0, 0} _)
    have hc' : Fintype.card {j // j ≠ k} = m := by
      have := Fintype.card_congr (Equiv.optionSubtypeNe k)
      rw [Fintype.card_option] at this
      omega
    have hk' : reindex e e (Pᴴ * G * P) (Sum.inr ()) (Sum.inr ()) = 1 := by
      simpa [e, reindex_apply, Equiv.optionSubtypeNe] using hk
    obtain ⟨h, hi, hd, hh⟩ := good_sum hs (ih _ hc') (reindex e e (Pᴴ * G * P))
      (by simpa [reindex_apply] using hM.submatrix e.symm) (fun i j => hMi _ _)
      (by rw [det_reindex_self]; exact hMd) hk'
    obtain ⟨h₁, hi₁, hd₁, hh₁⟩ := sol_transfer hs e _ h hi hd hh
    refine ⟨P * h₁, intg_mul hPi hi₁, by rw [det_mul, norm_mul, hPd, hd₁, one_mul], ?_⟩
    rw [conjTranspose_mul, ← hh₁]
    simp only [Matrix.mul_assoc]

end Main

section Piv

theorem pivot_w {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hs : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he0 : ‖e0‖ ≤ 1) (he0' : e0 + star e0 = 1) {n : Type}
    [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E) (hG : G.IsHermitian) (hGi : Intg G)
    (hGd : ‖G.det‖ = 1) :
    ∃ i, ∃ w : n → E, (∀ a, ‖w a‖ ≤ 1) ∧ w i = 1 ∧ ‖star w ⬝ᵥ (G *ᵥ w)‖ = 1 := by
  first
  | exact @_root_.GlobalTheory.UnitValueExistence.main
  | exact _root_.GlobalTheory.UnitValueExistence.main
  | (apply _root_.GlobalTheory.UnitValueExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitValueExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitValueExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitValueExistence.main ..)

end Piv

section Field

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem fixed_mem (a : E) (ha : star a = a) : ∃ u : F, algebraMap F E u = a := by
  apply GlobalTheory.JR.Step.UNormal.exists_algebraMap_of_star_eq <;> assumption

theorem quad_col {n : Type} [Fintype n] (G P : Matrix n n E) (k : n) :
    (Pᴴ * G * P) k k = star (fun a => P a k) ⬝ᵥ (G *ᵥ fun a => P a k) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

include F in
theorem pivot {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E) (hG : G.IsHermitian)
    (hGi : Intg G) (hGd : ‖G.det‖ = 1) :
    ∃ P : Matrix n n E, Intg P ∧ ‖P.det‖ = 1 ∧ ∃ k, (Pᴴ * G * P) k k = 1 := by
  haveI := Unram.ultraE (F := F) (E := E)
  have hs : ∀ y : E, ‖star y‖ = ‖y‖ := Unram.norm_star (F := F)
  obtain ⟨-, ⟨e0, he0, he0'⟩, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  obtain ⟨i, w, hw, hwi, hq⟩ := pivot_w hs e0 he0 he0' G hG hGi hGd
  have ha : star (star w ⬝ᵥ (G *ᵥ w)) = star w ⬝ᵥ (G *ᵥ w) := by
    calc star (star w ⬝ᵥ (G *ᵥ w)) = (star w ᵥ* Gᴴ) ⬝ᵥ w := by rw [star_dotProduct, star_mulVec, star_star]
      _ = star w ⬝ᵥ (G *ᵥ w) := by rw [← dotProduct_mulVec, hG.eq]
  obtain ⟨u, hu⟩ := fixed_mem (F := F) _ ha
  have hu1 : ‖u‖ = 1 := by rw [← norm_algebraMap' E u, hu]; exact hq
  obtain ⟨v0, hv0⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E u hu1
  rw [hu] at hv0
  have hv0n : ‖v0‖ = 1 := by
    have h := congrArg norm hv0
    rw [norm_mul, hs, hq] at h
    nlinarith [norm_nonneg v0]
  have hv0ne : v0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv0n
    exact zero_ne_one hv0n
  have hc : ‖(star v0)⁻¹‖ = 1 := by rw [norm_inv, hs, hv0n, inv_one]
  refine ⟨(1 : Matrix n n E).updateCol i ((star v0)⁻¹ • w), ?_, ?_, i, ?_⟩
  · intro p q
    rw [updateCol_apply]
    split_ifs
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]
      exact hw p
    · exact intg_one p q
  · rw [← cramer_apply, cramer_one]
    simp [hc, hwi]
  · rw [quad_col]
    have hcol : (fun a => (1 : Matrix n n E).updateCol i ((star v0)⁻¹ • w) a i) = (star v0)⁻¹ • w := by
      funext a
      simp
    have hst : star ((star v0)⁻¹ • w) = v0⁻¹ • star w := by
      funext p
      simp [star_mul', star_inv₀]
    rw [hcol, hst, smul_dotProduct, mulVec_smul, dotProduct_smul, ← hv0, smul_eq_mul, smul_eq_mul]
    have hsv : star v0 ≠ 0 := by rwa [star_ne_zero]
    field_simp

end Field

theorem unimodular_hermitian_eq_conj : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (s : ℕ) (G : Matrix (Fin s) (Fin s) E), G.IsHermitian →
    (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 →
    ∃ h : Matrix (Fin s) (Fin s) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  intro F E _ _ _ _ _ s G hG hGi hGd
  haveI := Unram.ultraE (F := F) (E := E)
  exact good_all (Unram.norm_star (F := F)) (fun n _ _ _ G hG hGi hGd => pivot (F := F) (E := E) G hG hGi hGd) s (Fin s)
    (Fintype.card_fin s) G hG hGi hGd

end GlobalTheory.HermUnimod
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHermitianMatrixCongruentOneStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unimodular_hermitian_matrix_congruent_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (s : ℕ) (G : Matrix (Fin s) (Fin s) E), G.IsHermitian → (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 → ∃ h : Matrix (Fin s) (Fin s) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  first | exact @GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj | exact GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj | (intros; apply GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj <;> assumption)
end
end
