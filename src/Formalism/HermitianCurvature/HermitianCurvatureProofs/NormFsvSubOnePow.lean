module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormWaveMDiff
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Fourier.FourierTransform
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RoomOffGridSymmetric
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.XiBound
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormLeDecay

section

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem norm_fsv (a t : ℂ) : ‖fsv a t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (a * t - conj a * conj t).re = 0 := by
    simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im]
  rw [this, Real.exp_zero]

theorem continuous_fsv₂ : Continuous (fun q : ℂ × ℂ => fsv q.1 q.2) := by
  unfold fsv
  exact Complex.continuous_exp.comp ((continuous_fst.mul continuous_snd).sub
    ((Complex.continuous_conj.comp continuous_fst).mul (Complex.continuous_conj.comp continuous_snd)))

theorem integrable_fsv_mul {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) (a : ℂ) :
    Integrable (fun t => fsv a t * φ t) := by
  refine hi.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun t => (norm_fsv a t).le)
  exact (continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

theorem continuous_transform {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) :
    Continuous (fun s : ℂ => ∫ t, fsv s t * φ t) := by
  refine continuous_of_dominated (bound := fun t => ‖φ t‖) (fun s => ?_) (fun s => ?_) hi.norm ?_
  · exact ((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).mul hφ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by rw [norm_mul, norm_fsv, one_mul]
  · exact Filter.Eventually.of_forall fun t =>
      (continuous_fsv₂.comp (continuous_id.prodMk continuous_const)).mul continuous_const

theorem integrable_decay3' : Integrable (fun s : ℂ => ((1 + ‖s‖) ^ 3)⁻¹) := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(3 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine hd.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (0 : ℝ) < 1 + ‖t‖ := by positivity
  simp only []
  rw [Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem integral_norm_le_decay {Ξ : ℂ → ℂ} (hΞ : Continuous Ξ) {K : ℝ} (hK : ∀ s, ‖Ξ s‖ ≤ K * ((1 + ‖s‖) ^ 3)⁻¹) :
    Integrable Ξ ∧ ∫ s, ‖Ξ s‖ ≤ K * ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ := by
  have hint : Integrable Ξ :=
    Integrable.mono' (integrable_decay3'.const_mul K) hΞ.aestronglyMeasurable (Filter.Eventually.of_forall hK)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint.norm (integrable_decay3'.const_mul K) hK

theorem fsv_sigma {c : ℂ} (hc : c ≠ 0) :
    fsv (Complex.I * (Real.pi : ℂ) / (2 * c)) c = -1 ∧
      ‖Complex.I * (Real.pi : ℂ) / (2 * c)‖ = Real.pi / (2 * ‖c‖) := by
  constructor
  · unfold fsv
    have e1 : Complex.I * (Real.pi : ℂ) / (2 * c) * c = Complex.I * (Real.pi / 2 : ℝ) := by
      push_cast; field_simp
    have e2 : conj (Complex.I * (Real.pi : ℂ) / (2 * c)) * conj c = -(Complex.I * (Real.pi / 2 : ℝ)) := by
      rw [← map_mul, e1, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [e1, e2, sub_neg_eq_add, ← two_mul, show (2 : ℂ) * (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
      Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  · rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_two, one_mul]

theorem rr_eq_form {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h : C.LPt)
    (hh : D.IsLocPt h j) :
    p.RR F j w h h = p.form j hj w (KB.slv p.T F j hj w h hh.2) (KB.slv p.T F j hj w h hh.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨hh, hh⟩, dite_eq_left hj]
  rfl

theorem bdd_of_tendsto {u : ℕ → ℂ} {x : ℂ} (hu : Tendsto u atTop (𝓝 x)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖u n‖ ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨max B 0, le_max_right _ _, fun n => (hB _ ⟨n, rfl⟩).trans (le_max_left _ _)⟩

end Formalism.FourierDecayAlt.P.PBO
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.NormLeIntegralFsv

section

@[expose] public section

open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

def isoQ : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun s := conj (Complex.I * s)
  invFun w := -Complex.I * conj w
  map_add' a b := by simp [mul_add]
  map_smul' c a := by
    simp only [RingHom.id_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  left_inv a := by
    simp only [map_mul, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp
  right_inv w := by
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp [Complex.I_sq]
  norm_map' s := by simp

theorem isoQ_apply (s : ℂ) : isoQ s = conj (Complex.I * s) := rfl

theorem fsv_smul (s u z : ℂ) : P5.fsv s u * z = 𝐞 (-⟪u, (π⁻¹ : ℝ) • isoQ s⟫) • z := by
  unfold P5.fsv
  simp [Circle.smul_def, isoQ_apply]
  left
  rw [Real.fourierChar_apply]
  congr 1
  have hπ : π ≠ 0 := Real.pi_ne_zero
  apply Complex.ext <;> simp <;> field_simp <;> ring

theorem norm_le_integral_fsv (φ : ℂ → ℂ) (hφ : Continuous φ) (hi : MeasureTheory.Integrable φ)
    (hΞ : MeasureTheory.Integrable (fun s : ℂ => ∫ t : ℂ, P5.fsv s t * φ t)) (t : ℂ) :
    ‖φ t‖ ≤ ∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖ := by
  have hc : (π⁻¹ : ℝ) ≠ 0 := inv_ne_zero Real.pi_ne_zero
  have hL : ∀ s : ℂ, (∫ u : ℂ, P5.fsv s u * φ u) = 𝓕 φ ((π⁻¹ : ℝ) • isoQ s) := by
    intro s
    rw [fourier_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => fsv_smul s u (φ u))
  have hmp : MeasurePreserving isoQ := isoQ.measurePreserving
  have hme : MeasurableEmbedding isoQ := isoQ.toHomeomorph.measurableEmbedding
  have hint1 : Integrable (fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) := by
    have h1 : Integrable ((fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) ∘ isoQ) := by
      have h2 := hΞ
      simp_rw [hL] at h2
      exact h2
    exact (hmp.integrable_comp_emb hme).mp h1
  have hint : Integrable (𝓕 φ) := by
    first
      | exact (integrable_comp_smul_iff volume (𝓕 φ) hc).mp hint1
  have hinv : 𝓕⁻ (𝓕 φ) t = φ t := by
    first
      | exact hi.fourier_inversion hint hφ.continuousAt
      | exact hi.fourierInv_fourier_eq hint hφ.continuousAt
  have hb : ‖φ t‖ ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := by
    rw [← hinv]
    first
      | rw [fourierInv_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext w
    first
      | exact Circle.norm_smul _ _
  have e1 := hmp.integral_comp hme (fun s : ℂ => ‖𝓕 φ ((π⁻¹ : ℝ) • s)‖)
  have e2 := Measure.integral_comp_smul (volume : Measure ℂ) (fun w : ℂ => ‖𝓕 φ w‖) (π⁻¹ : ℝ)
  try dsimp only at e1
  try dsimp only at e2
  have heq : (∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖) =
      |((π⁻¹ : ℝ) ^ 2)⁻¹| • ∫ w : ℂ, ‖𝓕 φ w‖ := by
    simp_rw [hL]
    rw [e1, e2, Complex.finrank_real_complex]
  rw [heq, smul_eq_mul]
  have h0 : 0 ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := integral_nonneg fun _ => norm_nonneg _
  have hπ : 1 ≤ |((π⁻¹ : ℝ) ^ 2)⁻¹| := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  nlinarith

end Formalism.FourierDecayAlt.P.PBO
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.NormFsvSubOnePow

section

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem transform_diff3 {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) (σ s : ℂ) :
    ∫ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t) =
      (∫ t, fsv (s + 3 * σ) t * φ t) - 3 * (∫ t, fsv (s + 2 * σ) t * φ t) + 3 * (∫ t, fsv (s + σ) t * φ t) -
        ∫ t, fsv s t * φ t := by
  have e : ∀ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t) =
      fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t) + 3 * (fsv (s + σ) t * φ t) - fsv s t * φ t := by
    intro t
    have e1 : fsv (s + σ) t = fsv s t * fsv σ t := (fsv_mul_fsv s σ t).symm
    have e2 : fsv (s + 2 * σ) t = fsv s t * fsv σ t * fsv σ t := by
      rw [fsv_mul_fsv, fsv_mul_fsv]; congr 1; ring
    have e3 : fsv (s + 3 * σ) t = fsv s t * fsv σ t * fsv σ t * fsv σ t := by
      rw [fsv_mul_fsv, fsv_mul_fsv, fsv_mul_fsv]; congr 1; ring
    rw [e1, e2, e3]; ring
  simp only [e]
  have i0 := integrable_fsv_mul hφ hi s
  have i1 := integrable_fsv_mul hφ hi (s + σ)
  have i2 := integrable_fsv_mul hφ hi (s + 2 * σ)
  have i3 := integrable_fsv_mul hφ hi (s + 3 * σ)
  have j1 : Integrable (fun t => fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t)) := i3.sub (i2.const_mul 3)
  have j2 : Integrable (fun t => fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t) +
      3 * (fsv (s + σ) t * φ t)) := j1.add (i1.const_mul 3)
  rw [integral_sub j2 i0, integral_add j1 (i1.const_mul 3), integral_sub i3 (i2.const_mul 3),
    integral_const_mul, integral_const_mul]

theorem norm_fsv_sub_one_pow (σ t : ℂ) : ‖(fsv σ t - 1) ^ 3‖ ≤ 8 := by
  rw [norm_pow]
  have : ‖fsv σ t - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_fsv, norm_one]; norm_num)
  calc ‖fsv σ t - 1‖ ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) this 3
    _ = 8 := by norm_num



theorem decayUnif_of (hRH : KB.RadHead) (hHT : KB.HeadTop) (hWDF : WaveDiffForm) : DecayUnif := by
  intro hP Cb
  obtain ⟨CcF, hFL⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨CcW, hWD⟩ := hWDF hP Cb
  refine ⟨max CcF CcW, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N cut lo hi hθ hχ hε hf hfA hthr hcut hon hroom j hj w hw hN h h' hh hh'
  have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by positivity
  have hthrF : CcF * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    have := mul_le_mul_of_nonneg_right (le_max_left CcF CcW) hX
    nlinarith
  have hthrW : CcW * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    have := mul_le_mul_of_nonneg_right (le_max_right CcF CcW) hX
    nlinarith
  obtain ⟨hcpt, hlim⟩ := hFL Wp Wq P p f χ ε A (N + 3) cut hθ hχ hε hf hfA hthrF hcut
  have hWDa := hWD Wp Wq P p f χ ε A N cut hθ hχ hε hf hfA hthrW hcut j hj w hw hN h hh

  obtain ⟨grid, hinj, hgr⟩ := grid_exists P p.l0 lo hi hon w hw j (by
    have h1 : (w.length : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : (j : ℝ) ≤ P.r := by exact_mod_cast hj
    nlinarith)
  have hlp : ∀ n : Fin 3 → Fin (2 * j + 1), (KB.plusW (List.ofFn fun a => grid a (n a)) w).length ≤ N + 3 := by
    intro n; rw [Formalism.FourierDecayAlt.P.PBD.plusW_eq]; simp; omega
  have hlm : ∀ n : Fin 3 → Fin (2 * j + 1), (KB.minusW (List.ofFn fun a => grid a (n a)) w).length ≤ N + 3 := by
    intro n; rw [Formalism.FourierDecayAlt.P.PBD.minusW_eq]; simp; omega

  have bnd : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → w'.length ≤ N + 3 → ∀ a : C.LPt,
      ∃ B, 0 ≤ B ∧ ∀ n, ‖p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) j w' a a‖ ≤ B :=
    fun w' hw' hl a => bdd_of_tendsto (hlim j w' hw' hl a a)
  choose Bp hBp0 hBp using fun n => bnd _ (hgr n).1 (hlp n) h
  choose Bm hBm0 hBm using fun n => bnd _ (hgr n).2.1 (hlm n) h'
  obtain ⟨Bh, hBh0, hBh⟩ := bnd w hw (by omega) h
  obtain ⟨Bh', hBh'0, hBh'⟩ := bnd w hw (by omega) h'
  set B := Bh + Bh' + ∑ n, (Bp n + Bm n) with hBdef
  have hS0 : 0 ≤ ∑ n, (Bp n + Bm n) := Finset.sum_nonneg fun n _ => add_nonneg (hBp0 n) (hBm0 n)
  have hB0 : 0 ≤ B := by positivity
  have hBpB : ∀ n, Bp n ≤ B := fun n => by
    have := Finset.single_le_sum (f := fun n => Bp n + Bm n) (fun n _ => add_nonneg (hBp0 n) (hBm0 n))
      (Finset.mem_univ n)
    linarith [hBm0 n]
  have hBmB : ∀ n, Bm n ≤ B := fun n => by
    have := Finset.single_le_sum (f := fun n => Bp n + Bm n) (fun n _ => add_nonneg (hBp0 n) (hBm0 n))
      (Finset.mem_univ n)
    linarith [hBp0 n]
  have hBhB : Bh ≤ B := by linarith
  have hBh'B : Bh' ≤ B := by linarith

  choose Cw hCw using fun n : Fin 3 → Fin (2 * j + 1) => hWDa (List.ofFn fun a => grid a (n a)) (by simp)
    (hgr n).1
  obtain ⟨C0, hC0⟩ := hWDa [] (by simp) hw
  set CW := |C0| + ∑ n, |Cw n| with hCWdef
  have hCW0 : 0 ≤ CW := by positivity
  have hCwW : ∀ n, Cw n ≤ CW := fun n => by
    have := Finset.single_le_sum (f := fun n => |Cw n|) (fun n _ => abs_nonneg _) (Finset.mem_univ n)
    linarith [le_abs_self (Cw n), abs_nonneg C0]
  have hC0W : C0 ≤ CW := by
    linarith [le_abs_self C0, Finset.sum_nonneg (fun n (_ : n ∈ Finset.univ) => abs_nonneg (Cw n))]

  set K := ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| /
        Real.sqrt (((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod)
    with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun n _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set T1 := 8 * (1 + K) * Real.sqrt (B * B) with hT1
  have hT10 : 0 ≤ T1 := by positivity
  have hxi : ∀ m s, ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2))
      (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ T1 * ((1 + ‖s‖) ^ 3)⁻¹ := by
    intro m s
    refine xi_bound hP P p (fun g => cut m g • D.cutF p.T.base χ f ε g) (hcpt m) j hj w hw h h' hh hh' grid hinj hgr LinearMap.id
      (fun ε x hx => hx) (fun x hx => hx) B B ?_ ?_ ?_ ?_ s
    · show ‖p.form j hj w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)‖ ≤ B
      rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh]; exact (hBh m).trans hBhB
    · rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh']; exact (hBh' m).trans hBh'B
    · intro n
      rw [onOld_eq_self (w := w) (⇑(LinearMap.id (R := ℂ)
        (M := Wd.Ix (Fin w.length) → FourierDecayAlt.B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))) (fun x => rfl), ← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj _ h hh]
      exact (hBp n m).trans (hBpB n)
    · intro n
      rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj _ h' hh']
      exact (hBm n m).trans (hBmB n)
  set I3 := ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ with hI3
  have hI30 : 0 ≤ I3 := integral_nonneg fun s => by positivity
  set C := T1 + 8 * T1 * I3 + (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 with hCdef
  have hX3 : 0 ≤ (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 := by positivity
  have hT8 : 0 ≤ 8 * T1 * I3 := mul_nonneg (mul_nonneg (by norm_num) hT10) hI30
  have hC1 : T1 ≤ C := by rw [hCdef]; linarith only [hX3, hT8]
  clear_value C I3 T1 K CW B
  refine ⟨C, fun m => ⟨fun c hc => ?_, fun s => ?_⟩⟩
  swap
  · have hs0 : (0 : ℝ) ≤ ((1 + ‖s‖) ^ 3)⁻¹ := inv_nonneg.2 (pow_nonneg (by positivity) 3)
    exact (hxi m s).trans (mul_le_mul_of_nonneg_right hC1 hs0)
  obtain ⟨φ, hφc, hφi, hφeq, hφs⟩ := pStdCpt_of_heads hP hRH hHT Wp Wq P p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h h' hh hh' Cb hθ
    (hcpt m) hw
  rw [← hφeq c hc]
  have hΞ : ∀ s, ‖∫ t, fsv s t * φ t‖ ≤ T1 * ((1 + ‖s‖) ^ 3)⁻¹ := fun s => by rw [hφs s]; exact hxi m s
  obtain ⟨hΞi, hΞI⟩ := integral_norm_le_decay (continuous_transform hφc hφi) hΞ
  have hφle := norm_le_integral_fsv φ hφc hφi hΞi c
  have hu : 0 < 1 + ‖c‖ := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hu 3)]
  by_cases hc1 : ‖c‖ ≤ 1
  · have hu8 : (1 + ‖c‖) ^ 3 ≤ 8 := by
      calc (1 + ‖c‖) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hu.le (by linarith) 3
        _ = 8 := by norm_num
    have h1 : ‖φ c‖ ≤ T1 * I3 := hφle.trans (by rw [hI3]; exact hΞI)
    have hTI : 0 ≤ T1 * I3 := mul_nonneg hT10 hI30
    calc ‖φ c‖ * (1 + ‖c‖) ^ 3 ≤ (T1 * I3) * 8 := mul_le_mul h1 hu8 (pow_nonneg hu.le 3) hTI
      _ = 8 * T1 * I3 := by ring
      _ ≤ C := by rw [hCdef]; linarith only [hX3, hT10]
  · push Not at hc1
    obtain ⟨hfσ, hσn⟩ := fsv_sigma hc
    set σ := Complex.I * (Real.pi : ℂ) / (2 * c) with hσdef
    have hc0 : 0 < ‖c‖ := by linarith
    have hσ2 : ‖σ‖ ≤ 2 := by
      rw [hσn, div_le_iff₀ (by linarith only [hc0])]
      linarith only [Real.pi_le_four, hc1]
    clear_value σ
    have hxc : ∀ e, KB.CptCoef (p.T.bs j) ((KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2) e) := fun e =>
      Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p _ j hj w h hh (hcpt m) e
    have hyc : ∀ e, KB.CptCoef (p.T.bs j) ((KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2) e) := fun e =>
      Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p _ j hj w h' hh' (hcpt m) e
    have hfc : Continuous (fun t => (fsv σ t - 1) ^ 3) :=
      ((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).sub continuous_const).pow 3
    have hψc : Continuous (fun t => (fsv σ t - 1) ^ 3 * φ t) := hfc.mul hφc
    have hψi : Integrable (fun t => (fsv σ t - 1) ^ 3 * φ t) :=
      hφi.bdd_mul (c := 8) hfc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => norm_fsv_sub_one_pow σ t)
    have hσ6 : 0 ≤ ‖σ‖ ^ 6 := pow_nonneg (norm_nonneg _) 6
    have hΨb : ∀ s, ‖∫ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t)‖ ≤
        (8 * (1 + K) * Real.sqrt (CW * ‖σ‖ ^ 6 * B)) * ((1 + ‖s‖) ^ 3)⁻¹ := by
      intro s
      rw [transform_diff3 hφc hφi σ s, hφs, hφs, hφs, hφs, ← form_wave_mDiff P p j hj w _ _ hxc hyc s σ]
      have hA0 : ‖p.form j hj w (mDiff (p.T.bs j) σ w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)) (mDiff (p.T.bs j) σ w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2))‖ ≤ CW * ‖σ‖ ^ 6 :=
        (hC0 m σ hσ2).trans (mul_le_mul_of_nonneg_right hC0W hσ6)
      have hB0' : ‖p.form j hj w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ B := by
        rw [← rr_eq_form p _ j hj w h' hh']; exact (hBh' m).trans hBh'B
      have key := xi_bound hP P p _ (hcpt m) j hj w hw h h' hh hh' grid hinj hgr (mDiff (p.T.bs j) σ w)
        (fun ε x hx => mDiff_nice _ σ w ε x hx) (fun x hx => mDiff_cpt hP P p j hj w hw σ x hx)
        (CW * ‖σ‖ ^ 6) B hA0 hB0'
        (fun n => (hCw n m σ hσ2).trans (mul_le_mul_of_nonneg_right (hCwW n) hσ6))
        (fun n => by rw [← rr_eq_form p _ j hj _ h' hh']; exact (hBm n m).trans (hBmB n)) s
      rw [← hKdef] at key
      exact key
    obtain ⟨hΨi, hΨI⟩ := integral_norm_le_decay (continuous_transform hψc hψi) hΨb
    have hψle := norm_le_integral_fsv _ hψc hψi hΨi c
    have hψc' : ‖(fsv σ c - 1) ^ 3 * φ c‖ = 8 * ‖φ c‖ := by
      rw [hfσ, norm_mul]; norm_num
    have hsq : Real.sqrt (CW * ‖σ‖ ^ 6 * B) = ‖σ‖ ^ 3 * Real.sqrt (CW * B) := by
      rw [show CW * ‖σ‖ ^ 6 * B = (‖σ‖ ^ 3) ^ 2 * (CW * B) by ring, Real.sqrt_mul (pow_nonneg (pow_nonneg (norm_nonneg _) 3) 2),
        Real.sqrt_sq (pow_nonneg (norm_nonneg _) 3)]
    have h1 : 8 * ‖φ c‖ ≤ 8 * (1 + K) * (‖σ‖ ^ 3 * Real.sqrt (CW * B)) * I3 := by
      rw [← hψc', ← hsq, hI3]; exact hψle.trans hΨI
    have h2 : ‖φ c‖ ≤ (1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3 := by linarith only [h1]
    have hu8 : (1 + ‖c‖) ^ 3 ≤ 8 * ‖c‖ ^ 3 := by
      calc (1 + ‖c‖) ^ 3 ≤ (2 * ‖c‖) ^ 3 := pow_le_pow_left₀ hu.le (by linarith only [hc1]) 3
        _ = 8 * ‖c‖ ^ 3 := by ring
    have hπ : ‖σ‖ ^ 3 * (8 * ‖c‖ ^ 3) = Real.pi ^ 3 := by
      have hc3 : (2 : ℝ) ^ 3 * ‖c‖ ^ 3 ≠ 0 := (mul_pos (by norm_num) (pow_pos hc0 3)).ne'
      rw [hσn, div_pow, mul_pow, div_mul_eq_mul_div, mul_div_assoc,
        show (8 : ℝ) * ‖c‖ ^ 3 / (2 ^ 3 * ‖c‖ ^ 3) = 1 by rw [div_eq_one_iff_eq hc3]; norm_num, mul_one]
    have hK1 : (0 : ℝ) ≤ 1 + K := by linarith only [hK]
    have hs3 : (0 : ℝ) ≤ ‖σ‖ ^ 3 := pow_nonneg (norm_nonneg σ) 3
    have hQ4 : 0 ≤ (1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3 :=
      mul_nonneg (mul_nonneg (mul_nonneg hK1 (Real.sqrt_nonneg (CW * B))) hs3) hI30
    calc ‖φ c‖ * (1 + ‖c‖) ^ 3 ≤ ((1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3) * (8 * ‖c‖ ^ 3) :=
          mul_le_mul h2 hu8 (pow_nonneg hu.le 3) hQ4
      _ = (1 + K) * Real.sqrt (CW * B) * I3 * (‖σ‖ ^ 3 * (8 * ‖c‖ ^ 3)) := by ring
      _ = (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 := by rw [hπ]
      _ ≤ C := by rw [hCdef]; linarith only [hT10, hT8]

end Formalism.FourierDecayAlt.P.PBO
end
end
end
