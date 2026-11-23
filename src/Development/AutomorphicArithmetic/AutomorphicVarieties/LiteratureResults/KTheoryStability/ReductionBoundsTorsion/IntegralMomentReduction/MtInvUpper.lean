module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.OmG
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.ContVal
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.UmatUpper
import Mathlib.Tactic.TypeStar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.ConeStep

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem cone_step {T : ℝ} {s : Fin N → ℝ} (h : Cone T s) :
    ∀ d : ℕ, ∀ l q : Fin N, (q : ℕ) = l + d → s q ≤ s l + d * T := by
  intro d
  induction d with
  | zero =>
    intro l q hq
    have : q = l := Fin.ext (by simpa using hq)
    subst this
    simp
  | succ d ih =>
    intro l q hq
    have hlt : (l : ℕ) + d < N := by have := q.isLt; omega
    have h1 := ih l ⟨(l : ℕ) + d, hlt⟩ rfl
    have h2 := h ⟨(l : ℕ) + d, hlt⟩ q (by simp; omega)
    push_cast
    linarith

theorem cone_le {T : ℝ} {s : Fin N → ℝ} (h : Cone T s) {l q : Fin N} (hlq : l ≤ q) :
    s q - s l ≤ N * |T| := by
  have h1 := cone_step h ((q : ℕ) - l) l q (by have : (l : ℕ) ≤ q := hlq; omega)
  have h2 : (((q : ℕ) - l : ℕ) : ℝ) ≤ N := by
    have : (q : ℕ) - l ≤ N := by omega
    exact_mod_cast this
  have h3 : (((q : ℕ) - l : ℕ) : ℝ) * T ≤ (((q : ℕ) - l : ℕ) : ℝ) * |T| :=
    mul_le_mul_of_nonneg_left (le_abs_self T) (Nat.cast_nonneg _)
  have h4 : (((q : ℕ) - l : ℕ) : ℝ) * |T| ≤ N * |T| := mul_le_mul_of_nonneg_right h2 (abs_nonneg T)
  linarith

theorem env (M T : ℝ) : ∃ R1 : ℝ, ∀ (n p k : Matrix (Fin N) (Fin N) ℂ) (s0 s : Fin N → ℝ), Cone T s0 →
    (∀ i, |s i - s0 i| ≤ 1) → n.BlockTriangular id → (∀ i j, i ≤ j → ‖n i j‖ ≤ 2 * Real.exp (s0 i - s0 j)) →
    p.BlockTriangular id → (∀ i j, ‖p i j‖ ≤ M) → k ∈ unitaryGroup (Fin N) ℂ →
    ∀ i j, ‖(diagonal (fun i => ((Real.exp (-s0 i) : ℝ) : ℂ)) *
      (n * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k)) i j‖ ≤ R1 := by
  refine ⟨(N : ℝ) * N * (2 * |M| * Real.exp (1 + N * |T|)), ?_⟩
  intro n p k s0 s hc hs hnb hn hpb hp hk i j
  have key : ∀ l m : Fin N, ‖((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j)‖
      ≤ 2 * |M| * Real.exp (1 + N * |T|) := by
    intro l m
    by_cases hil : l < i
    · rw [hnb hil]; simp; positivity
    by_cases hlm : m < l
    · rw [hpb hlm]; simp; positivity
    push_neg at hil hlm
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have h1 := hn i l hil
    have h2 : ‖p l m‖ ≤ |M| := (hp l m).trans (le_abs_self M)
    have h3 : ‖k m j‖ ≤ 1 := entry_norm_bound_of_unitary hk m j
    have h4 := cone_le hc hlm
    have h5 := (abs_le.mp (hs m)).2
    have hexp : Real.exp (-s0 i) * Real.exp (s0 i - s0 l) * Real.exp (s m) = Real.exp (s m - s0 l) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-s0 i) * (‖n i l‖ * ‖p l m‖ * Real.exp (s m) * ‖k m j‖)
        ≤ Real.exp (-s0 i) * (2 * Real.exp (s0 i - s0 l) * |M| * Real.exp (s m) * 1) := by gcongr
      _ = 2 * |M| * (Real.exp (-s0 i) * Real.exp (s0 i - s0 l) * Real.exp (s m)) := by ring
      _ = 2 * |M| * Real.exp (s m - s0 l) := by rw [hexp]
      _ ≤ 2 * |M| * Real.exp (1 + N * |T|) := by gcongr; linarith
  have entry : (diagonal (fun i => ((Real.exp (-s0 i) : ℝ) : ℂ)) *
      (n * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k)) i j
      = ∑ m, ∑ l, ((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j) := by
    rw [diagonal_mul, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  rw [entry]
  calc ‖∑ m, ∑ l, ((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j)‖
      ≤ ∑ m : Fin N, ∑ l : Fin N, (2 * |M| * Real.exp (1 + N * |T|)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => key l m))
    _ = (N : ℝ) * N * (2 * |M| * Real.exp (1 + N * |T|)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.EntryMulLe

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem entry_mul_le {A B : Matrix (Fin N) (Fin N) ℂ} {a b : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ a)
    (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin N) : ‖(A * B) i j‖ ≤ N * (a * b) := by
  rw [Matrix.mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin N, a * b := by
        gcongr with k
        rw [norm_mul]
        exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ((norm_nonneg _).trans (hA i k))
    _ = N * (a * b) := by simp

theorem adj_le {A : Matrix (Fin N) (Fin N) ℂ} {M : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ M) (i j : Fin N) :
    ‖adjugate A i j‖ ≤ (N.factorial : ℝ) * (max M 1) ^ N := by
  rw [adjugate_apply]
  have hb : ∀ k l, (NormedField.toAbsoluteValue ℂ) (A.updateRow j (Pi.single i 1) k l) ≤ max M 1 := by
    intro k l
    show ‖A.updateRow j (Pi.single i 1) k l‖ ≤ max M 1
    rcases eq_or_ne k j with rfl | hk
    · rw [updateRow_self]
      by_cases hl : l = i
      · subst hl; simp
      · simp [hl]
    · rw [updateRow_ne hk]; exact (hA k l).trans (le_max_left _ _)
  have h := Matrix.det_le hb
  rw [nsmul_eq_mul, Fintype.card_fin] at h
  exact h

theorem tri (M : ℝ) : ∃ R0 : ℝ, ∀ (h p p' u : Matrix (Fin N) (Fin N) ℂ) (s s' : Fin N → ℝ),
    (∀ i, |s i - s' i| ≤ 1) → h.BlockTriangular id → p.BlockTriangular id → p'.BlockTriangular id →
    (∀ i j, ‖p i j‖ ≤ M) → (∀ i j, ‖p' i j‖ ≤ M) → p.det = 1 → p'.det = 1 → u ∈ unitaryGroup (Fin N) ℂ →
    h * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) =
      p' * diagonal (fun i => ((Real.exp (s' i) : ℝ) : ℂ)) * u →
    ∀ i j, ‖h i j‖ ≤ R0 := by
  refine ⟨N * (N * (M * Real.exp 1) * ((N.factorial : ℝ) * (max M 1) ^ N)), ?_⟩
  intro h p p' u s s' hss hh hp hp' hpM hp'M hpd hp'd hu heq i j
  set a := diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) with ha
  set a' := diagonal (fun i => ((Real.exp (s' i) : ℝ) : ℂ)) with ha'
  set ai := diagonal (fun i => ((Real.exp (-s i) : ℝ) : ℂ)) with hai
  have haai : a * ai = 1 := by
    rw [ha, hai, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hpadj : p * adjugate p = 1 := by rw [mul_adjugate, hpd, one_smul]
  have hrec : h * p * a * ai * adjugate p = h := by
    rw [show h * p * a * ai * adjugate p = h * (p * (a * ai) * adjugate p) by simp only [Matrix.mul_assoc],
      haai, Matrix.mul_one, hpadj, Matrix.mul_one]
  rw [heq] at hrec
  have hdet' : IsUnit (p' * a').det := by
    rw [det_mul, hp'd, one_mul, ha', det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast (Real.exp_pos _).ne')
  have hu_eq : u = (p' * a')⁻¹ * (h * p * a) := by
    rw [heq, Matrix.nonsing_inv_mul_cancel_left (A := p' * a') (B := u) hdet']
  have hut : u.BlockTriangular id := by
    haveI := invertibleOfIsUnitDet (p' * a') hdet'
    rw [hu_eq]
    exact (blockTriangular_inv_of_blockTriangular (hp'.mul (blockTriangular_diagonal _))).mul
      ((hh.mul hp).mul (blockTriangular_diagonal _))
  have hstar : star u * u = 1 := (mem_unitaryGroup_iff'.1 hu)
  have hinv : u⁻¹ = star u := Matrix.inv_eq_left_inv hstar
  have hut' : (star u).BlockTriangular id := by
    rw [← hinv]
    haveI : Invertible u := invertibleOfLeftInverse _ _ hstar
    exact blockTriangular_inv_of_blockTriangular hut
  have hoff : ∀ k l, k ≠ l → u k l = 0 := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h1 | h1
    · have := hut' (show id k < id l from h1)
      rw [star_apply] at this
      simpa using this
    · exact hut h1
  have hD : ∀ k l, ‖(a' * u * ai) k l‖ ≤ Real.exp 1 := by
    intro k l
    rw [ha', hai, mul_diagonal, diagonal_mul]
    by_cases hkl : k = l
    · subst hkl
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      calc Real.exp (s' k) * ‖u k k‖ * Real.exp (-s k) ≤ Real.exp (s' k) * 1 * Real.exp (-s k) := by
            gcongr; exact entry_norm_bound_of_unitary hu k k
        _ = Real.exp (s' k - s k) := by rw [mul_one, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by have := hss k; rw [abs_le] at this; linarith)
    · rw [hoff k l hkl]; simp; positivity
  rw [← hrec, show p' * a' * u * ai * adjugate p = p' * (a' * u * ai) * adjugate p by
    simp only [Matrix.mul_assoc]]
  exact entry_mul_le (entry_mul_le hp'M hD) (adj_le hpM) i j

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.MtInvUpper

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.TwSMInt2

open PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem sum_meas_le {α β : Type*} [MeasurableSpace α] (μ : Measure α) (F : Finset β) (A : β → Set α)
    (hA : ∀ b, MeasurableSet (A b)) {Y : Set α} (hY : MeasurableSet Y) (hsub : ∀ b ∈ F, A b ⊆ Y) (R : ℕ)
    (hR : ∀ x, ∀ S : Finset β, S ⊆ F → (∀ b ∈ S, x ∈ A b) → S.card ≤ R) : ∑ b ∈ F, μ (A b) ≤ R * μ Y := by
  classical
  have e1 : ∑ b ∈ F, μ (A b) = ∫⁻ x, ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x ∂μ := by
    rw [lintegral_finsetSum _ fun b _ => measurable_one.indicator (hA b)]
    exact Finset.sum_congr rfl fun b _ => (lintegral_indicator_one (hA b)).symm
  have e2 : (R : ℝ≥0∞) * μ Y = ∫⁻ x, Y.indicator (fun _ => (R : ℝ≥0∞)) x ∂μ := (lintegral_indicator_const hY _).symm
  rw [e1, e2]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Y
  · rw [Set.indicator_of_mem hx]
    have : ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x = ((F.filter fun b => x ∈ A b).card : ℝ≥0∞) := by
      simp [Set.indicator_apply]
    rw [this]
    exact Nat.cast_le.2 (by
      convert hR x (F.filter fun b => x ∈ A b) (Finset.filter_subset _ _) fun b hb => (Finset.mem_filter.1 hb).2)
  · rw [Set.indicator_of_notMem hx]
    refine (Finset.sum_eq_zero fun b hb => Set.indicator_of_notMem (fun h => hx (hsub b hb h)) _).le

theorem mt_mul' (a b : G ι N) (w : ι) : mt (a * b) w = mt a w * mt b w := rfl

theorem mt_nu_same (w0 : ι) (c : SpecialLinearGroup (Fin N) GaussianInt) :
    mt (nu w0 c) w0 = (c : Matrix (Fin N) (Fin N) GaussianInt).map GaussianInt.toComplex := by
  classical
  simp only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rfl

theorem mt_nu_ne {w0 w : ι} (h : w ≠ w0) (c : SpecialLinearGroup (Fin N) GaussianInt) :
    mt (nu w0 c) w = 1 := by
  classical
  simp only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
  rfl

theorem mt_inv_upper {a : G ι N} {w : ι} (h : (mt a w).BlockTriangular id) : (mt a⁻¹ w).BlockTriangular id := by
  have h1 : mt a⁻¹ w * mt a w = 1 := by rw [← mt_mul', inv_mul_cancel]; rfl
  haveI : Invertible (mt a w) := invertibleOfLeftInverse _ _ h1
  rw [← Matrix.inv_eq_left_inv h1]
  exact blockTriangular_inv_of_blockTriangular h

theorem mt_inv_unit {a : G ι N} {w : ι} (h : mt a w ∈ unitaryGroup (Fin N) ℂ) : mt a⁻¹ w ∈ unitaryGroup (Fin N) ℂ := by
  have h1 : mt a⁻¹ w * mt a w = 1 := by rw [← mt_mul', inv_mul_cancel]; rfl
  rw [← Matrix.inv_eq_left_inv h1, Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 h)]
  exact Unitary.star_mem h

theorem pack [Fintype ι] [Nonempty ι] [MeasurableSpace (G ι N)] [BorelSpace (G ι N)] (μ : Measure (G ι N))
    [μ.IsHaarMeasure] {P : Set (G ι N)} (hPc : IsCompact P) (M T : ℝ) (hP : P ⊆ PB M) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : Fin N → ℤ) (s0 : Fin N → ℝ), ∑ i, s0 i = 0 → Cone T s0 →
      (∀ i, (m i : ℝ) ≤ s0 i ∧ s0 i ≤ m i + 1) →
      μ (Xb P T m) ≤ K * ENNReal.ofReal (Real.exp (-2 * Phi s0)) := by
  classical
  obtain ⟨w0⟩ := ‹Nonempty ι›
  obtain ⟨R0, hR0⟩ := tri (N := N) M
  obtain ⟨R, hR⟩ := fin_bdd (N := N) R0
  obtain ⟨R1, hR1⟩ := env (N := N) M T
  refine ⟨R * μ (Zb R1), ENNReal.mul_ne_top (ENNReal.natCast_ne_top R) (cpt_Z R1).measure_lt_top.ne, ?_⟩
  intro m s0 hs0 hc0 hm0
  obtain ⟨F, hF, hcard⟩ := count s0
  have hs0' : ∑ i, (-s0 i) = 0 := by rw [Finset.sum_neg_distrib, hs0, neg_zero]
  have hXm : MeasurableSet (Xb P T m) := (cpt_X hPc T m).measurableSet
  have hZm : MeasurableSet (Zb (ι := ι) (N := N) R1) := (cpt_Z R1).measurableSet
  have hclose : ∀ s s' : Fin N → ℝ, (∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1) →
      (∀ i, (m i : ℝ) ≤ s' i ∧ s' i ≤ m i + 1) → ∀ i, |s i - s' i| ≤ 1 := by
    intro s s' h h' i
    have := h i; have := h' i
    rw [abs_le]; constructor <;> linarith
  have key := sum_meas_le μ F (fun c => (fun x => (nu w0 c)⁻¹ * x) ⁻¹' Xb P T m)
    (fun c => measurable_const_mul _ hXm)
    (Y := (fun x => (dg (fun i => -s0 i) hs0' : G ι N) * x) ⁻¹' Zb R1) (measurable_const_mul _ hZm) ?_ R ?_
  · simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul] at key
    have h1 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m) ≤ R * μ (Zb R1) :=
      (mul_le_mul' hcard le_rfl).trans key
    have h2 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * ENNReal.ofReal (Real.exp (-2 * Phi s0)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp
    calc μ (Xb P T m) = (ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m)) *
          ENNReal.ofReal (Real.exp (-2 * Phi s0)) := by rw [mul_right_comm, h2, one_mul]
      _ ≤ _ := mul_le_mul' h1 le_rfl
  · rintro c hc x ⟨p, hp, s, hs, -, hm, k, hk, hx⟩ w i j
    have hx' : x = nu w0 c * p * dg s hs * k := by
      have : x = nu w0 c * ((nu w0 c)⁻¹ * x) := by group
      rw [this]; dsimp only at hx; rw [hx]; simp only [mul_assoc]
    rw [hx']
    have hn : (mt (nu w0 c) w).BlockTriangular id ∧
        ∀ i j, i ≤ j → ‖mt (nu w0 c) w i j‖ ≤ 2 * Real.exp (s0 i - s0 j) := by
      by_cases hw : w = w0
      · subst hw; rw [mt_nu_same]; exact hF c hc
      · rw [mt_nu_ne hw]
        refine ⟨blockTriangular_one, fun i j _ => ?_⟩
        by_cases hij : i = j
        · subst hij; simp
        · rw [one_apply_ne hij, norm_zero]; positivity
    exact hR1 _ _ _ s0 s hc0 (hclose _ _ hm hm0) hn.1 hn.2 (hP hp w).1 (hP hp w).2 (hk w) i j
  · intro x S hS hx
    refine hR S fun c hc c' hc' i j => ?_
    obtain ⟨p, hp, s, hs, -, hm, k, hk, e⟩ := hx c hc
    obtain ⟨p', hp', s', hs', -, hm', k', hk', e'⟩ := hx c' hc'
    dsimp only at e e'
    have hE : nu w0 (c⁻¹ * c') * p' * dg s' hs' = p * dg s hs * (k * k'⁻¹) := by
      have a1 : p' * dg s' hs' = (nu w0 c')⁻¹ * x * k'⁻¹ := by rw [e']; group
      rw [mul_assoc, a1, ← mul_assoc (p * dg s hs), ← e, map_mul, map_inv]; group
    have hup : (mt (nu w0 (c⁻¹ * c')) w0).BlockTriangular id := by
      rw [map_mul, map_inv, mt_mul']
      refine (mt_inv_upper ?_).mul ?_
      · rw [mt_nu_same]; exact (hF c (hS hc)).1
      · rw [mt_nu_same]; exact (hF c' (hS hc')).1
    have := hR0 (mt (nu w0 (c⁻¹ * c')) w0) (mt p' w0) (mt p w0) (mt (k * k'⁻¹) w0) s' s (hclose _ _ hm' hm) hup
      (hP hp' w0).1 (hP hp w0).1 (hP hp' w0).2 (hP hp w0).2 (p' w0).2 (p w0).2
      (by rw [mt_mul']; exact mul_mem (hk w0) (mt_inv_unit (hk' w0))) (congrArg (fun y => mt y w0) hE) i j
    rw [mt_nu_same] at this
    exact this

end PositivityTheory.KB.TwSMInt2

end
end
end
