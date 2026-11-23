module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructureStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ConjTransposeMemGLs
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
import Mathlib.Tactic.Linter.Style
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.GelfandReading
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.UnitaryMemGLs

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ContinuousCoords

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.KSuppPf

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem inv_contAt (A : Mat n) (hA : A.det ≠ 0) : ContinuousAt (fun B : Mat n => B⁻¹) A := by
  apply continuousAt_matrix_inv
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hA

theorem lg_contAt (A : Mat n) (hA : A.det ≠ 0) : ContinuousAt lg A := by
  have hi := inv_contAt A hA
  unfold lg
  refine ContinuousAt.log ?_ ?_
  · refine continuousAt_const.add ?_
    refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
    refine ContinuousAt.add (f := fun y : Mat n => ‖y a b‖ ^ 2) (g := fun y : Mat n => ‖y⁻¹ a b‖ ^ 2) ?_ ?_
    · exact ((continuous_norm.comp ((continuous_apply b).comp (continuous_apply a))).continuousAt).pow 2
    · exact (continuous_norm.continuousAt.comp
        (((continuous_apply b).comp (continuous_apply a)).continuousAt.comp hi)).pow 2
  · have : 0 ≤ ∑ a, ∑ b, (‖A a b‖ ^ 2 + ‖A⁻¹ a b‖ ^ 2) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
    positivity

theorem det_ne_of_posDef (x : Mat n) (h : (x * xᴴ).PosDef) : x.det ≠ 0 := by
  intro h0
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  rw [Matrix.det_mul, h0, zero_mul] at hu
  exact not_isUnit_zero hu

theorem det_inv_ne (A : Mat n) (h : A.det ≠ 0) : (A⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero h

theorem det_ct_ne (A : Mat n) (h : A.det ≠ 0) : (Aᴴ).det ≠ 0 := by
  rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 h

theorem hOf_comb (hb : HbFacts) (s : ℝ) (v : Fin n × Fin n → ℝ) :
    hOf (s • v + (1 - s) • oPt n) = (s : ℂ) • hOf v + (((1 - s : ℝ)) : ℂ) • (1 : Mat n) := by
  have h1 : hOf (oPt n) = 1 := (hb n).2.2.1 1 Matrix.isHermitian_one
  rw [← h1]
  unfold hOf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

def Kset (n : ℕ) (B : ℝ) : Set (Mat n × Mat n) :=
  {p | p.1 * p.2 = 1} ∩ {p | ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ B}

theorem isCompact_Kset (B : ℝ) : IsCompact (Kset n B) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.matrix_mul continuous_snd) continuous_const
    · refine isClosed_le (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_) continuous_const
      exact ((continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp continuous_fst))).pow 2).add
        ((continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp continuous_snd))).pow 2)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|B| + 1, fun p hp => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hent : ∀ a b, ‖p.1 a b‖ ≤ |B| + 1 ∧ ‖p.2 a b‖ ≤ |B| + 1 := by
      intro a b
      have hle : ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ B := by
        refine le_trans ?_ hp.2
        refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2))
          (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a))
        exact Finset.single_le_sum (f := fun b => ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)
          (fun b _ => by positivity) (Finset.mem_univ b)
      have h1 : ‖p.1 a b‖ ^ 2 ≤ |B| := le_trans (by nlinarith [sq_nonneg ‖p.2 a b‖]) (le_abs_self B)
      have h2 : ‖p.2 a b‖ ^ 2 ≤ |B| := le_trans (by nlinarith [sq_nonneg ‖p.1 a b‖]) (le_abs_self B)
      constructor
      · nlinarith [norm_nonneg (p.1 a b), abs_nonneg B, sq_nonneg (‖p.1 a b‖ - 1)]
      · nlinarith [norm_nonneg (p.2 a b), abs_nonneg B, sq_nonneg (‖p.2 a b‖ - 1)]
    have hB : 0 ≤ |B| + 1 := by positivity
    rw [Prod.norm_def, max_le_iff]
    exact ⟨(Matrix.norm_le_iff hB).2 fun a b => (hent a b).1, (Matrix.norm_le_iff hB).2 fun a b => (hent a b).2⟩

theorem continuous_coords : Continuous (coords : Mat n → Fin n × Fin n → ℝ) := by
  apply continuous_pi
  intro p
  unfold coords
  exact Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)

theorem ksupp_of (hb : HbFacts) (hc : ConeSt) : KSupp := by
  intro hS n V _ _ σ hσ hσ2 Fr k Γ T R hk z hz hinj c
  obtain ⟨hopen, hconv, -⟩ := hc n
  obtain ⟨R', hR'⟩ := hS n z hz hinj R
  set C : Set (Fin n × Fin n → ℝ) := (fun p : Mat n × Mat n => coords (p.1 * p.1ᴴ)) '' Kset n (Real.exp R') with hCdef
  have hdet : ∀ v ∈ cone n, (σ v).det ≠ 0 := fun v hv =>
    det_ne_of_posDef _ (by rw [hσ2 v hv]; exact hv)
  have hdz : (diagonal z).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => fun h0 => by have := hz a; rw [h0, norm_zero] at this; exact zero_ne_one this
  refine ⟨C, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hd1 : p.1.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hp.1
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hu : IsUnit p.1 := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd1)
    show (hOf (coords (p.1 * p.1ᴴ))).PosDef
    rw [(hb n).2.2.1 _ (Matrix.isHermitian_mul_conjTranspose_self _)]
    have := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := (1 : Mat n)) hu).2 Matrix.PosDef.one
    simpa [Matrix.star_eq_conjTranspose] using this
  · exact (isCompact_Kset _).image (continuous_coords.comp (continuous_fst.matrix_mul continuous_fst.matrix_conjTranspose))
  · intro s hs v hv hvC
    have ho : oPt n ∈ cone n := (hb n).2.2.2.2.2.2.2
    have hP1 : s • v + (1 - s) • oPt n ∈ cone n := hconv hv ho hs.1 (by linarith [hs.2]) (by ring)

    have hgt : R < lg ((σ (s • v + (1 - s) • oPt n))⁻¹ * diagonal z * (σ v)ᴴ⁻¹) := by
      by_contra hle
      push Not at hle
      have hyR := hR' s hs (σ (s • v + (1 - s) • oPt n)) (hdet _ hP1) (σ v) (hdet v hv)
        (by rw [hσ2 _ hP1, hσ2 v hv, hOf_comb hb]) hle
      apply hvC
      refine ⟨(σ v, (σ v)⁻¹), ⟨Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet v hv)), ?_⟩, ?_⟩
      · have h1 : 0 ≤ ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2) :=
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
        have h2 : Real.log (1 + ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2)) ≤ R' := hyR
        have h3 := (Real.log_le_iff_le_exp (by positivity)).1 h2
        show ∑ a, ∑ b, (‖σ v a b‖ ^ 2 + ‖(σ v)⁻¹ a b‖ ^ 2) ≤ Real.exp R'
        linarith
      · show coords (σ v * (σ v)ᴴ) = v
        rw [hσ2 v hv]; exact (hb n).2.2.2.1 v

    have hσc : ∀ w ∈ cone n, ContinuousAt σ w := fun w hw =>
      (hσ.continuousOn).continuousAt (hopen.mem_nhds hw)
    have hA : ((σ (s • v + (1 - s) • oPt n))⁻¹ * diagonal z * (σ v)ᴴ⁻¹).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero (det_inv_ne _ (hdet _ hP1)) hdz) (det_inv_ne _ (det_ct_ne _ (hdet v hv)))
    have hf1 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.1)⁻¹)
        (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := fun B : Mat n => B⁻¹) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ w.1)
        (inv_contAt _ (hdet _ hP1))
        (ContinuousAt.comp (g := σ) (f := Prod.fst) (x := (s • v + (1 - s) • oPt n, v)) (hσc _ hP1) continuousAt_fst)
    have hf2 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.2)ᴴ⁻¹)
        (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := fun B : Mat n => B⁻¹) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.2)ᴴ)
        (inv_contAt _ (det_ct_ne _ (hdet v hv)))
        (ContinuousAt.comp (g := fun B : Mat n => Bᴴ) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ w.2)
          (continuous_id.matrix_conjTranspose).continuousAt
          (ContinuousAt.comp (g := σ) (f := Prod.snd) (x := (s • v + (1 - s) • oPt n, v)) (hσc v hv) continuousAt_snd))
    have hΦ : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
        lg ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹)) (s • v + (1 - s) • oPt n, v) :=
      ContinuousAt.comp (g := lg) (f := fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
          (σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹) (lg_contAt _ hA) (by
        have h3 : ContinuousAt (fun w : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ w.1)⁻¹ * diagonal z)
            (s • v + (1 - s) • oPt n, v) := hf1.mul continuousAt_const
        exact h3.mul hf2)
    have e1 := hΦ.eventually (Ioi_mem_nhds hgt)
    have e2 : ∀ᶠ w in nhds (s • v + (1 - s) • oPt n, v), w ∈ cone n ×ˢ cone n :=
      (hopen.prod hopen).mem_nhds ⟨hP1, hv⟩
    filter_upwards [e1, e2] with w hw1 hw2
    have hGL : ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹) ∈ GLs n := by
      show ((σ w.1)⁻¹ * diagonal z * (σ w.2)ᴴ⁻¹).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero (det_inv_ne _ (hdet _ hw2.1)) hdz) (det_inv_ne _ (det_ct_ne _ (hdet _ hw2.2)))
    have hk0 := hk _ hGL hw1
    simp only [Kc, Kf, hk0, mul_zero, zero_mul, smul_zero]

end PositivityTheory.RgBcC.LfSt.KSuppPf
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.TwMemGLs

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped ContDiff ComplexConjugate Topology

namespace PositivityTheory.RgBcC.LfSt

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isBump_zero_of_neg {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) (hT : T < 0) : IsBump g 0 := by
  refine ⟨h.1, h.2.1, fun t ht => h.2.2 t (lt_trans hT ht)⟩

theorem isMult_nonneg [MeasurableSpace (G n)] {μ : Measure (G n)} {E : KMod n} {k : Mat n → (E.V →L[ℂ] E.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ E k val T) : IsMult μ E k val (max T 0) := by
  obtain ⟨m, c, w, g, ks, hks, hk, hv⟩ := h
  refine ⟨m, c, w, g, ks, fun i => ⟨?_, (hks i).2⟩, hk, hv⟩
  rcases le_or_gt 0 T with hT | hT
  · rw [max_eq_left hT]; exact (hks i).1
  · rw [max_eq_right hT.le]; exact isBump_zero_of_neg (hks i).1 hT

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  have h := Matrix.UnitaryGroup.det_isUnit k
  exact h.ne_zero

theorem isMult_props [MeasurableSpace (G n)] {μ : Measure (G n)} {E : KMod n} {k : Mat n → (E.V →L[ℂ] E.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ E k val T) :
    ContDiffOn ℝ ∞ k (GLs n) ∧
      ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂ := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  refine ⟨?_, fun y hy k₁ k₂ => ?_⟩
  · have hs : ContDiffOn ℝ ∞ (fun y => ∑ i, c i • ks i y) (GLs n) :=
      ContDiffOn.sum fun i _ => ((hks i).2.1).const_smul (c i)
    exact hs.congr fun y hy => hk y hy
  · have hy' : k₁.1 * y * k₂.1 ∈ GLs n := mem_GLs_mul (mem_GLs_mul (unitary_mem_GLs k₁) hy) (unitary_mem_GLs k₂)
    rw [hk _ hy', hk y hy, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hks i).2.2.2.1 y hy k₁ k₂, mul_smul_comm, smul_mul_assoc]

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  exact (Matrix.isUnit_nonsing_inv_det x hu).ne_zero

theorem conjTranspose_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : xᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_conjTranspose, star_ne_zero] at *
  exact hx

theorem tw_mem_GLs {x d : Mat n} (hx : x ∈ GLs n) (hd : d ∈ GLs n) : x⁻¹ * d * xᴴ⁻¹ ∈ GLs n :=
  mem_GLs_mul (mem_GLs_mul (inv_mem_GLs hx) hd) (inv_mem_GLs (conjTranspose_mem_GLs hx))

theorem lAsm : LAsm := by
  classical
  intro hHb _hFD hKC hKS hE1 hE0 _hHom hCone0 _hWE _hWS hKE hMA hCh hCone hHom hSupp
  intro n lam E Fr ε ι S Γ T hCx _ _ μ _ k val τ hk d z hd hz hz2
  obtain ⟨hopen, hconv, σ, hσ, hσ2, hmeas⟩ := hCone n
  obtain ⟨c, -, hform⟩ := hmeas μ
  obtain ⟨hksm, hkeq⟩ := isMult_props hk
  have hdG : d.val ∈ GLs n := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit d)).ne_zero
  have hch := hCh n lam E Fr ε ι S Γ T hCx μ k val τ hk
  have hkΓ : ∀ y ∈ GLs n, Γ * k y = k y * Γ := fun y hy => (hch y hy).1
  obtain ⟨c0, hc0⟩ := hKE n
  have hsuppk : ∀ y ∈ GLs n, c0 * (1 + max τ 0) < lg y → k y = 0 :=
    (hc0 μ E).2 k val (max τ 0) (le_max_right _ _) (isMult_nonneg hk)
  set R := c0 * (1 + max τ 0) with hRdef
  obtain ⟨hKsm, hKΓ, hKch⟩ := hKC n lam E Fr ε ι S Γ T hCx σ hσ hσ2 k hksm hkeq (fun y hy => hch y hy) d.val hdG c
  obtain ⟨C, hCU, hCc, hCsupp⟩ := hKS hSupp n E.V σ hσ hσ2 Fr k Γ T R hsuppk z hz hz2 c
  have hK : Kc σ c Fr k Γ T d.val = Kc σ c Fr k Γ T (diagonal z) := by rw [hd]
  set K' : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) → (E.V →L[ℂ] E.V) := fun y =>
    if y ∈ cone n ×ˢ cone n then Kc σ c Fr k Γ T d.val y else 0 with hK'def
  have hUU : IsOpen (cone n ×ˢ cone n) := hopen.prod hopen
  have hKK' : ∀ y ∈ cone n ×ˢ cone n, K' =ᶠ[𝓝 y] Kc σ c Fr k Γ T d.val := fun y hy =>
    Filter.eventually_of_mem (hUU.mem_nhds hy) fun y' hy' => by simp only [hK'def, if_pos hy']
  obtain ⟨hherm, htr, -, -, -, -, -, hoPt⟩ := hHb n
  have hH := hHom (Fin n × Fin n) E.V (fun i => ε (hb i)) (fun i => ι (hb i)) S Γ (cone n) (oPt n) K' hopen hconv hoPt
    (fun i j => by
      rw [hCx.car (hb i) (hb j) (hherm i) (hherm j), htr i j]
      split_ifs <;> simp)
    (fun i => hCx.Γε _) (fun i => hCx.Γι _) hCx.SΓ hCx.Ssmooth (fun s i => hCx.Sε s _) hCx.Sder
    (hKsm.congr fun y hy => by simp only [hK'def, if_pos hy])
    (fun y => by
      by_cases hy : y ∈ cone n ×ˢ cone n
      · simp only [hK'def, if_pos hy]; exact hKΓ y hy
      · simp only [hK'def, if_neg hy, mul_zero, zero_mul])
    (fun y hy => by
      rw [(hKK' y hy).fderiv_eq]
      exact hKch y hy)
    ⟨C, hCU, hCc, fun s hs v hv hvC => by
      have h1 := hCsupp s hs v hv hvC
      have hmem : (s • v + (1 - s) • oPt n, v) ∈ cone n ×ˢ cone n :=
        ⟨hconv hv hoPt hs.1 (by linarith [hs.2]) (by ring), hv⟩
      filter_upwards [h1, hKK' _ hmem] with y h1y h2y
      rw [h2y, hK]
      exact h1y⟩
  obtain ⟨R', hR'⟩ := hSupp n z hz hz2 R
  have hR1 : ∀ x ∈ GLs n, R' < lg x → k (x⁻¹ * d.val * xᴴ⁻¹) = 0 := by
    intro x hx hlt
    by_contra hne
    have hle : lg (x⁻¹ * diagonal z * xᴴ⁻¹) ≤ R := by
      by_contra hgt
      push_neg at hgt
      exact hne (hd ▸ hsuppk _ (hd ▸ tw_mem_GLs hx hdG) hgt)
    have := hR' 1 ⟨zero_le_one, le_refl _⟩ x hx x hx (by simp) hle
    linarith
  obtain ⟨hint, heq1⟩ := hE1 n lam E Fr ε ι S Γ T hCx μ σ c hσ hσ2 hform k hksm.continuousOn hkeq hkΓ d R' hR1
  have heig := (hMA n μ E k k val val τ τ hk hk).2.2.2
  have heq0 := hE0 n lam E Fr ε ι S Γ T hCx μ σ c hσ hσ2 hform k val hksm.continuousOn hkeq hkΓ ⟨R, hsuppk⟩ heig
    d z hd hz hz2
  refine ⟨hint, ?_⟩
  rw [← heq1, ← heq0]
  have e1 : ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 1 * K' (v, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
      ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) :=
    setIntegral_congr_fun hopen.measurableSet fun v hv => by simp only [hK'def, if_pos (show (v, v) ∈ cone n ×ˢ cone n from ⟨hv, hv⟩)]
  have e0 : ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 0 * K' (oPt n, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
      ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 0 * Kc σ c Fr k Γ T d.val (oPt n, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) :=
    setIntegral_congr_fun hopen.measurableSet fun v hv => by
      simp only [hK'def, if_pos (show (oPt n, v) ∈ cone n ×ˢ cone n from ⟨hoPt, hv⟩)]
  rw [← e1, ← e0]
  exact hH

end PositivityTheory.RgBcC.LfSt
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.LOfOfKChain

section

@[expose] public section

namespace PositivityTheory.RgBcC.LfSt

theorem lOf_of_kChain (h : KChain) : LOf :=
  lAsm GlobalTheory.T.height_bound_facts (GelfandReading.frameDer_of GlobalTheory.T.height_bound_facts) h (KSuppPf.ksupp_of GlobalTheory.T.height_bound_facts GlobalTheory.T.positive_cone_structure) UnitaryConjTransposeTrace.end1 GLSubgroupConjTransposeClosure.end0
    GlobalTheory.T.positive_cone_homotopy GlobalTheory.T.positive_cone_structure

end PositivityTheory.RgBcC.LfSt
end
end
