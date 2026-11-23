module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.SandwichA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RangeDatumEmbedding
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiMExpPmat
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ThmFD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.Imports
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.ImportsAlt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdDefs

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Sandwich

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem fdeg_ratio_V {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hgap : GapAtLeast ε μ h) (hh : thrStar ε + 1 < h) (s : Fin n)
    (hs : StrictAnti (μ + Pi.single s 1))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε μ σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (hσ' : Formalism.MainNotions.S.IsDS ε (μ + Pi.single s 1) σ')
    (ν : Measure (Formalism.REAL.UJ ε)) (hν : ν.IsHaarMeasure) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg ν σ d) :
    Formalism.MainNotions.S.IsFdeg ν σ' (d * ratioV μ s) := by
  exact swC_main false hp hq hμ hgap hh s hs hσ hσ' ν hν hd

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConsA

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_big {ε : Fin n → Bool} {h : ℝ} (hh : thrStar ε + 1 < h) :
    (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := by
  unfold thrStar at hh
  have h1 := le_max_left ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
  linarith

theorem one_le_q0_of_p_q_pos {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) : 1 ≤ S7.q0 ε := by
  show 1 ≤ min (pOf ε) (qOf ε)
  exact le_min hp hq

theorem fdc_eight {ε : Fin n → Bool} {h : ℝ} (hh : thrStar ε + 1 < h) :
    8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
  unfold thrStar at hh
  have h1 := le_max_right ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
  have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
  have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  nlinarith

theorem fdc_stdGap {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrStar ε + 1 < h) : StdGap ε μ :=
  ⟨hμ.1, h, hg, fdc_big hh⟩

theorem fdc_hc_add {μ : Fin n → ℝ} {s : Fin n} (hμ : IsHCParam μ) (hs : StrictAnti (μ + Pi.single s 1)) :
    IsHCParam (μ + Pi.single s 1) := by
  refine ⟨hs, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hμ.2 a
  by_cases has : a = s
  · subst has
    refine ⟨m + 1, ?_⟩
    rw [Pi.add_apply, Pi.single_eq_same]
    push_cast
    linarith
  · refine ⟨m, ?_⟩
    rw [Pi.add_apply, Pi.single_eq_of_ne has, add_zero]
    exact hm

theorem fdc_w_ne {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.w ≠ 0 := by
  letI := T.instNACG
  intro h
  have h1 := T.w_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem fdc_model {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ} {h : ℝ}
    (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (hh : thrStar ε + 1 < h) (T : KType ε (lowK ε μ)) :
    ∃ m : Fin n → ℤ, IsMu μ m ∧ IsPsiFor ε μ T (PsiM T m) := by
  obtain ⟨m, hm⟩ := Lap.LemK.exists_isMu hμ
  exact ⟨m, hm, (Lap.Base.psiFor n ε μ h T m hμ hm hg (one_le_q0_of_p_q_pos hp hq) (fdc_eight hh)).1⟩

abbrev FdcGood (ε : Fin n → Bool) (μ : Fin n → ℝ) (d : ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε μ σ ∧ Formalism.MainNotions.S.IsFdeg (muCD ε) σ d

def fdcD (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := by
  classical
  exact if h : ∃ d, FdcGood ε μ d then h.choose else 0

theorem fdc_fdegOf_eq {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ g x) = σ' g (U x)) (ν : Measure (Formalism.REAL.UJ ε)) (v : H) :
    Formalism.MainNotions.S.fdegOf ν σ' (U v) = Formalism.MainNotions.S.fdegOf ν σ v := by
  have hfun : (fun g : Formalism.REAL.UJ ε => ‖⟪U v, σ' (Formalism.MainNotions.S.umat g) (U v)⟫_ℂ‖ ^ 2) =
      fun g => ‖⟪v, σ (Formalism.MainNotions.S.umat g) v⟫_ℂ‖ ^ 2 := by
    funext g
    rw [← hU (Formalism.MainNotions.S.umat g) g.2 v, LinearIsometryEquiv.inner_map_map]
  simp only [Formalism.MainNotions.S.fdegOf, Formalism.MainNotions.S.coefOn]
  rw [LinearIsometryEquiv.norm_map, hfun]

theorem fdcGood_unique {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrStar ε + 1 < h) {d d' : ℝ} (h1 : FdcGood ε μ d) (h2 : FdcGood ε μ d') : d = d' := by
  obtain ⟨H, _, _, σ, hσ, hd⟩ := h1
  obtain ⟨H', _, _, σ', hσ', hd'⟩ := h2
  have := hσ.1
  have := hσ'.1
  have := hσ.2.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨U, hU⟩ := (isDS_props_of_gap n ε μ hμ h hg (fdc_big hh) H σ hσ).2.2.2.2 H' σ' hσ'
  have hUv : U v ≠ 0 := by simpa using hv
  rw [← fdegOf_of_isFdeg' hd hv, ← fdegOf_of_isFdeg' hd' hUv, fdc_fdegOf_eq U hU]

theorem fdcD_eq {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrStar ε + 1 < h) {d : ℝ} (hd : FdcGood ε μ d) : fdcD ε μ = d := by
  have hex : ∃ d, FdcGood ε μ d := ⟨d, hd⟩
  rw [fdcD, dite_eq_left hex]
  exact fdcGood_unique hμ hg hh hex.choose_spec hd

theorem fdcGood_of_isDS {ε : Fin n → Bool} {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε μ σ) :
    ∃ d, Formalism.MainNotions.S.IsFdeg (muCD ε) σ d := by
  haveI : CompleteSpace H := hσ.1
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS μ σ hσ
  exact isFdeg_muCD hd

theorem fdc_ds_exists {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ} {h : ℝ}
    (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (hh : thrStar ε + 1 < h) : ∃ d, FdcGood ε μ d := by
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨m, -, hP⟩ := fdc_model hp hq hμ hg hh T
  have hDS := isDS_sigLam (fdc_stdGap hμ hg hh) hP (fdc_w_ne T)
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hDS
  exact ⟨d, _, inferInstance, inferInstance, _, hDS, hd⟩

theorem fdc_step {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {h : ℝ} (hh : thrStar ε + 1 < h) :
    ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) →
        fdcD ε (μ + Pi.single s 1) = fdcD ε μ * ratioV μ s := by
  intro μ s hμ hg hg' hs
  have hμ' := fdc_hc_add hμ hs
  obtain ⟨d, hd⟩ := fdc_ds_exists hp hq hμ hg hh
  obtain ⟨H, i1, i2, σ, hσ, hfd⟩ := hd
  obtain ⟨d', hd'⟩ := fdc_ds_exists hp hq hμ' hg' hh
  obtain ⟨H', j1, j2, σ', hσ', hfd'⟩ := hd'
  have h3 := fdeg_ratio_V hp hq hμ hg hh s hs hσ hσ' (muCD ε) (muCD_isHaar ε) hfd
  have hu : d' = d * ratioV μ s :=
    fdcGood_unique hμ' hg' hh ⟨H', j1, j2, σ', hσ', hfd'⟩ ⟨H', j1, j2, σ', hσ', h3⟩
  rw [fdcD_eq hμ hg hh ⟨H, i1, i2, σ, hσ, hfd⟩, fdcD_eq hμ' hg' hh ⟨H', j1, j2, σ', hσ', hfd'⟩, hu]

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrStar ε + 1 < h) : fdcD ε lam = dimVlam lam := by
  have hsa : StrictAnti lam := (fdc_stdGap hlam hgap hh).1
  have key : ∀ t : ℕ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
      (T : KType ε (lowK ε (lamT lam t))) (j : T.V →L[ℂ] H),
      FData ε (lamT lam t) σ T j ∧
      (∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
        (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
          ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
            ⟪T.w, fF ε (lamT lam t) T (pmat z) T.w⟫_ℂ) ∧
      Formalism.MainNotions.S.IsFdeg (muCD ε) σ (fdcD ε (lamT lam t)) := by
    intro t
    have hμ := isHCParam_lamT hlam t
    have hg : GapAtLeast ε (lamT lam t) (h + t) := gap_lamT hsa hgap t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hh' : thrStar ε + 1 < h + t := by linarith
    have hstd := fdc_stdGap hμ hg hh'
    let T : KType ε (lowK ε (lamT lam t)) := (HW.kType_exists ε _ hμ).some
    obtain ⟨m, hm, hP⟩ := fdc_model hp hq hμ hg hh' T
    obtain ⟨d, H, i1, i2, σ, hDS, hd⟩ := fdc_ds_exists hp hq hμ hg hh'
    haveI : CompleteSpace H := hDS.1
    obtain ⟨j, hiso, hk, -, hform⟩ := anyF hDS hstd hP
    have hΨ : ∀ z : PCoord ε → ℂ, PsiM T m (NormedSpace.exp (pmat z)) = fF ε (lamT lam t) T (pmat z) := by
      intro z
      rw [psiM_exp_pmat, psM_exp_pmat hm T z]
    obtain ⟨H', i1', i2', σ', w', hsm, hlink⟩ := Lap.Base.link n ε _ T (PsiM T m) hstd hP
    refine ⟨H, i1, i2, inferInstance, σ, T, j, ⟨hDS.2.2.1, hiso, hk, fun z => ?_⟩,
      ⟨H', i1', i2', σ', w', hsm, fun z => ?_⟩, ?_⟩
    · rw [hform _ (exp_pmat_inUJ z), hΨ]
    · rw [hlink _ (exp_pmat_inUJ z), hΨ]
    · rw [fdcD_eq hμ hg hh' ⟨H, i1, i2, σ, hDS, hd⟩]
      exact hd
  choose H i1 i2 i3 σ T j hF hsm hd using key
  exact thmFD Lap.Base.b3 hp hq hlam hgap hh (fdcD ε) (fdc_step hp hq hh) H σ T j
    (Filter.Eventually.of_forall hF) (Filter.Eventually.of_forall hsm) (Filter.Eventually.of_forall hd)

theorem fdCons_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrStar ε + 1 < h)
    (hΨ : ∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
      ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε lam σ) {v : H} (hv : v ≠ 0) :
    Formalism.MainNotions.S.fdegOf (muCD ε) σ v = dimVlam lam := by
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hσ
  have hgood : FdcGood ε lam d := ⟨H, inferInstance, inferInstance, σ, hσ, hd⟩
  have h1 : fdcD ε lam = d := fdcD_eq hlam hgap hh hgood
  rw [← fdc_cd hp hq hlam hgap hh, h1, fdegOf_of_isFdeg' hd hv]

theorem fdCons_muG (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      thrStar ε + 1 < h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
        ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ) →
      v ≠ 0 → Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  haveI := muCD_isHaar ε
  let κ := Measure.haarScalarFactor (muCD ε) (Formalism.REAL.muG ε)
  have hκpos : (0 : ℝ) < κ :=
    NNReal.coe_pos.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure (muCD ε) (Formalism.REAL.muG ε))
  have hκ : muCD ε = κ • Formalism.REAL.muG ε :=
    Measure.isMulLeftInvariant_eq_smul (muCD ε) (Formalism.REAL.muG ε)
  refine ⟨κ, hκpos, ?_⟩
  intro lam H _ _ _ σ v hlam hσ h hgap hh hp hq hΨ hv
  have hcd := fdCons_cd hp hq hlam hgap hh hΨ hσ hv
  have hfd : Formalism.QuantumDeterminants.fdegHC lam = dimVlam lam := rfl
  rw [hκ] at hcd
  delta Formalism.MainNotions.S.fdegOf at hcd ⊢
  rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at hcd
  rw [hfd, ← hcd]
  rw [div_mul_eq_div_div_swap, mul_comm (κ : ℝ), div_mul_cancel₀ _ hκpos.ne']

end ReciprocityTheory.ChartRestriction.DS
end
end
end
