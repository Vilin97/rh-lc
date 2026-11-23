module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSumEigenvaluesNoncompactPartLeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CumulantLowerBoundOfBoundedCentredStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivLeadMinorExpHermitianZeroDiag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsLeWeightedSumBlockVariancesOfGapStatement
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Set.PowersetCard
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivLeadMinorExpHermitianZeroDiagStatement

section

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.deriv_leadMinor_exp_hermitian_zeroDiag : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Y.IsHermitian → (∀ a, Y a a = 0) → ∀ (l : ℕ) (hl : l ≤ n), deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) 0 = 0 ∧ deriv (deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)) 0 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.MinorJet.deriv_leadMinor_exp | exact GlobalTheory.MinorJet.deriv_leadMinor_exp | (intros; apply GlobalTheory.MinorJet.deriv_leadMinor_exp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorExpHermitianEqConvexExpSum

section

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorExp

theorem sum_dite_card {n l : ℕ} {M : Type*} [AddCommMonoid M] (f : Set.powersetCard (Fin n) l → M) :
    ∑ J : Finset (Fin n), (if h : J.card = l then f ⟨J, h⟩ else 0) = ∑ S, f S := by
  symm
  refine Finset.sum_of_injOn (fun S : Set.powersetCard (Fin n) l => S.1)
    (fun _ _ _ _ h => Subtype.ext h) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro J _ hJ
    rw [dif_neg]
    intro h
    exact hJ ⟨⟨J, h⟩, by simp, rfl⟩
  · intro S _
    have h : S.1.card = l := S.2
    rw [dite_eq_left h]

theorem exp_smul_eq {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) =
      (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        diagonal (fun j => ((Real.exp (t * hY.eigenvalues j) : ℝ) : ℂ)) *
        (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  have h2 : Uᴴ * U = 1 := (hY.eigenvectorUnitary).2.1
  have hs : Y = U * diagonal (fun j => ((hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    have := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h3 : (t : ℂ) • Y = U * diagonal (fun j => ((t * hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hs]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext j
    simp
  rw [h3]
  refine (Matrix.exp_units_conj (⟨U, Uᴴ, h1, h2⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).trans ?_
  rw [Matrix.exp_diagonal]
  change U * _ * Uᴴ = _
  congr 3
  funext j
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem leadMinor_exp_eq_sum (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ)
    (hl : l ≤ n) :
    ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧
      ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl =
        ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  set A : Matrix (Fin l) (Fin n) ℂ := U.submatrix (Fin.castLE hl) id with hA
  have hAA : A * Aᴴ = 1 := by
    rw [hA, conjTranspose_submatrix, ← submatrix_mul U Uᴴ _ id _ Function.bijective_id, h1]
    exact submatrix_one _ (Fin.castLE_injective hl)
  refine ⟨fun J => if h : J.card = l then
    ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0,
    ?_, ?_, ?_, ?_⟩
  · intro J
    dsimp only
    split_ifs <;> positivity
  · intro J hJ
    by_contra h
    exact hJ (dif_neg h)
  · rw [sum_dite_card (fun S => ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2)]
    exact GlobalTheory.sum_norm_sq_minors_eq_one A hAA
  · intro t
    have hsum : (∑ J : Finset (Fin n), (if h : J.card = l then
        ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0) *
          Real.exp (t * ∑ j ∈ J, hY.eigenvalues j)) =
        ∑ S : Set.powersetCard (Fin n) l, ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2 *
          Real.exp (t * ∑ j ∈ S.1, hY.eigenvalues j) := by
      rw [← sum_dite_card]
      refine Finset.sum_congr rfl fun J _ => ?_
      split_ifs <;> simp
    rw [hsum, exp_smul_eq hY t, leadMinor]
    rw [submatrix_mul _ _ _ id _ Function.bijective_id,
      submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id,
      ← conjTranspose_submatrix]
    refine (GlobalTheory.det_mul_diagonal_mul_eq_sum_minors A _ Aᴴ).trans ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← conjTranspose_submatrix, det_conjTranspose, Complex.star_def, Complex.mul_conj',
      Finset.mul_sum, Real.exp_sum]
    push_cast
    ring

end GlobalTheory.LeadMinorExp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorExpHermitianEqConvexExpSumStatement

section

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n), ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧ ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl = ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | exact GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | (intros; apply GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLeadMinorDecay

section

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.MinorDecay

lemma Jm_sq {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

lemma herm_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) :
    X.IsHermitian := by
  obtain ⟨h1, h2⟩ := h
  unfold inG at h1
  have h3 : Xᴴ * Jm ε = X * Jm ε := by
    rw [h2]; exact eq_neg_of_add_eq_zero_left h1
  have h4 := congrArg (· * Jm ε) h3
  simp only [Matrix.mul_assoc, Jm_sq, Matrix.mul_one] at h4
  exact h4

lemma diag_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X)
    (a : Fin n) : X a a = 0 := by
  have h2 := congrFun (congrFun h.2 a) a
  unfold Jm at h2
  simp only [mul_diagonal, Matrix.neg_apply, diagonal_mul] at h2
  split_ifs at h2
  · linear_combination h2 / 2
  · linear_combination -h2 / 2

lemma hs_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    ((hs X : ℝ) : ℂ) = (X * Xᴴ).trace := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.mul_conj']
  rfl

lemma conj_facts {n : ℕ} {ε : Fin n → Bool} {X k : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X)
    (hk : k ∈ Kset ε) :
    inP ε (k⁻¹ * X * k) ∧ hs (k⁻¹ * X * k) = hs X ∧
      k⁻¹ * NormedSpace.exp X * k = NormedSpace.exp (k⁻¹ * X * k) := by
  obtain ⟨hu, hJ⟩ := hk
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv h1
  have hunit : IsUnit k := ⟨⟨k, kᴴ, h2, h1⟩, rfl⟩
  have hH := herm_of_inP h
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, Matrix.mul_one]
      _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
      _ = (kᴴ * k) * Jm ε * kᴴ := by rw [← hJ]; simp only [Matrix.mul_assoc]
      _ = Jm ε * kᴴ := by rw [h1, Matrix.one_mul]
  have hanti : kᴴ * X * k * Jm ε = -(Jm ε * (kᴴ * X * k)) := by
    calc kᴴ * X * k * Jm ε = kᴴ * (X * Jm ε) * k := by
          simp only [Matrix.mul_assoc]; rw [hJ]
      _ = -(kᴴ * Jm ε * X * k) := by rw [h.2]; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = _ := by rw [hJ']; simp only [Matrix.mul_assoc]
  have hYH : (kᴴ * X * k)ᴴ = kᴴ * X * k := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]
  refine ⟨?_, ?_, (Matrix.exp_conj' k X hunit).symm⟩
  · rw [hinv]
    refine ⟨?_, hanti⟩
    unfold inG
    rw [hYH, hanti, neg_add_cancel]
  · rw [hinv]
    apply Complex.ofReal_injective
    rw [hs_eq_trace, hs_eq_trace, hYH, hH.eq]
    have : kᴴ * X * k * (kᴴ * X * k) = kᴴ * (X * (k * kᴴ) * X * k) := by
      simp only [Matrix.mul_assoc]
    rw [this, h2, Matrix.mul_one, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]

lemma deriv_sum_exp {ι : Type} [Fintype ι] (w y : ι → ℝ) :
    deriv (fun t : ℝ => ∑ J, w J * Real.exp (t * y J)) =
      fun t : ℝ => ∑ J, (w J * y J) * Real.exp (t * y J) := by
  funext t
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro J _
  have := (((hasDerivAt_id t).mul_const (y J)).exp).const_mul (w J)
  exact this.congr_deriv (by simp only [id]; ring)

lemma hs_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs X := by
  unfold hs; positivity

lemma minor_bound {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y)
    (R : ℝ) (hR : R = Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y))
    (l : ℕ) (hl : l ≤ n) :
    0 < (leadMinor (NormedSpace.exp Y) l hl).re ∧ (leadMinor (NormedSpace.exp Y) l hl).im = 0 ∧
      min 1 (1 / R) * (∑ a : Fin n, ∑ b : Fin n,
        if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0) / 4
        ≤ Real.log (leadMinor (NormedSpace.exp Y) l hl).re := by
  have hH := herm_of_inP h
  obtain ⟨w, hw0, -, hw1, hw⟩ := GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum n Y hH l hl
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.deriv_leadMinor_exp_hermitian_zeroDiag n Y hH (diag_of_inP h) l hl
  have hrange := GlobalTheory.T.abs_sum_eigenvalues_noncompactPart_le n ε Y hH h
  rw [← hR] at hrange
  set y : Finset (Fin n) → ℝ := fun J => ∑ j ∈ J, hH.eigenvalues j with hy
  have hfun : (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)
      = fun t : ℝ => ∑ J, w J * Real.exp (t * y J) := by
    funext t; rw [hw t, Complex.ofReal_re]
  rw [hfun, deriv_sum_exp] at hd1 hd2
  rw [deriv_sum_exp] at hd2
  simp only [zero_mul, Real.exp_zero, mul_one] at hd1 hd2
  have hone := hw 1
  simp only [Complex.ofReal_one, one_smul, one_mul] at hone
  rw [hone, Complex.ofReal_re, Complex.ofReal_im]
  have hpos : 0 < ∑ J, w J * Real.exp (y J) := by
    have : ∃ J, w J ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hw1
    obtain ⟨J, hJ⟩ := this
    exact Finset.sum_pos' (fun J _ => mul_nonneg (hw0 J) (Real.exp_pos _).le)
      ⟨J, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw0 J) hJ.symm) (Real.exp_pos _)⟩
  refine ⟨hpos, rfl, ?_⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hvar : ∑ J, w J * y J ^ 2 = ∑ a : Fin n, ∑ b : Fin n,
        if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
    rw [← hd2]; refine Finset.sum_congr rfl fun J _ => by ring
  rw [← hvar]
  rcases hR0.eq_or_lt with h0 | h0
  · have hy0 : ∀ J, y J = 0 := fun J => abs_nonpos_iff.1 (by rw [h0]; exact hrange J)
    change _ ≤ Real.log (∑ J, w J * Real.exp (y J))
    simp [hy0, hw1]
  · exact GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred _ w y R h0 hw0 hw1 hd1 (fun J _ => hrange J)

lemma min_mul_eq (H c : ℝ) (hH : 0 ≤ H) :
    min 1 (1 / (c * Real.sqrt H)) * H = min H (Real.sqrt H / c) := by
  rw [min_mul_of_nonneg _ _ hH, one_mul]
  congr 1
  rcases hH.eq_or_lt with h0 | h0
  · simp [← h0]
  · have hs : 0 < Real.sqrt H := Real.sqrt_pos.2 h0
    have : H = Real.sqrt H * Real.sqrt H := (Real.mul_self_sqrt hH).symm
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) hc]
      linear_combination c * this

theorem prod_leadMinor_decay : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (X km : Matrix (Fin n) (Fin n) ℂ), IsHCParam lam → GapAtLeast ε lam h → inP ε X → km ∈ Kset ε → (∀ (l : ℕ) (hl : l ≤ n), 0 < (leadMinor (km⁻¹ * NormedSpace.exp X * km) l hl).re ∧ (leadMinor (km⁻¹ * NormedSpace.exp X * km) l hl).im = 0) ∧ ∏ i : Fin (n - 1), (leadMinor (km⁻¹ * NormedSpace.exp X * km) (i.val + 1) (by omega)).re ^ (-(lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1)) ≤ Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ)))) := by
  intro n ε lam h X km hlam hgap hX hk
  obtain ⟨hY, hhs, hexp⟩ := conj_facts hX hk
  rw [hexp, ← hhs]
  set Y := km⁻¹ * X * km with hYdef
  have key := minor_bound hY _ rfl
  refine ⟨fun l hl => ⟨(key l hl).1, (key l hl).2.1⟩, ?_⟩
  have hgs := GlobalTheory.T.hs_le_weighted_sum_blockVariances_of_gap n ε lam h Y hlam.1 hgap hY
  rw [← min_mul_eq _ _ (hs_nonneg Y)]
  set c := Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) with hc
  set t := min 1 (1 / (c * Real.sqrt (hs Y))) with ht
  have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
  rw [Finset.prod_congr rfl fun i _ => Real.rpow_def_of_pos (key _ _).1 _, ← Real.exp_sum,
    Real.exp_le_exp]
  have h2 := mul_le_mul_of_nonneg_left hgs (by positivity : 0 ≤ t / 4)
  rw [Finset.mul_sum] at h2
  have h3 : -(h / 8) * (t * hs Y) = -(t / 4 * (h * hs Y / 2)) := by ring
  rw [h3, le_neg]
  refine h2.trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlt : lam ⟨i.val + 1, by omega⟩ < lam ⟨i.val, by omega⟩ :=
    hlam.1 (by simp [Fin.lt_def])
  have hk := (key (i.val + 1) (by omega)).2.2
  have hs0 : 0 ≤ lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1 := by linarith
  have := mul_le_mul_of_nonneg_left hk hs0
  linarith

end GlobalTheory.MinorDecay
end
end
