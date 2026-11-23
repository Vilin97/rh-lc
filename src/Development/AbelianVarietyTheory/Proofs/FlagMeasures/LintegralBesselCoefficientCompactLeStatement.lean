module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeil
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpenStatement
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormIdentityBesselCoefficientQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWN
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeasSset

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem exists_isQuotMeas_Sset : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (GG k r) μG → IsHaarOn (Sset k r z) μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r z μG μS hz hT hG hS
  obtain ⟨μW, hW⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μN, hN⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have conv : ∀ {U : Set (Mat k r)} {μ : Measure (Mt k r)}, Formalism.FourierDecayAlt.B.IsHaarOn U μ → IsHaarOn U μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩
  obtain ⟨hSg, hsub, hH, hR⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT
    (conv hW) (conv hN)
  have hS' : PI.IsHaarOnM (Sset k r z) μS := hS
  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _ hSg hH).1 μS hS'
  have hR' : PI.IsRightInvM (Sset k r z) μS := by
    intro s hs
    rw [hc, Measure.map_smul, hR s hs]
    exact (GlobalTheory.ProdHaar.measurable_rmulQ s).aemeasurable
  obtain ⟨hGg, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  exact GlobalTheory.QuotWeil.exists_isQuotM _ _ _ μG μS hGg hSg hsub (hGH μG hG).1 hS' hR'

end GlobalTheory.SgInf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralCompactLeQuotientMeasureBessel

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.LocEmb

variable {k r : ℕ}

theorem det_ne_zero_of_mem {g : Mat k r} (hg : g ∈ GG k r) : g.det ≠ 0 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH : (Hpk k r).det ≠ 0 := by
    have := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact hH this.symm

theorem isClosed_GG : IsClosed (GG k r) := by
  show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem continuousOn_inv : ContinuousOn (fun b : Mat k r => b⁻¹) {b | b.det ≠ 0} := by
  have : (fun b : Mat k r => b⁻¹) = fun b => (b.det)⁻¹ • b.adjugate := by
    funext b; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact ContinuousOn.smul ((continuous_id.matrix_det).continuousOn.inv₀ fun b hb => hb)
    continuous_id.matrix_adjugate.continuousOn

end GlobalTheory.SgInf.LocEmb

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LocEmb
variable {k r : ℕ}

def quotSet (K : Set (Mt k r)) : Set (Mt k r) :=
  (fun p : Mt k r × Mt k r => ((Matrix.of p.1 : Mat k r) * (Matrix.of p.2 : Mat k r)⁻¹ : Mat k r)) '' (K ×ˢ K)

theorem isCompact_quotSet {K : Set (Mt k r)} (hK : IsCompact K)
    (hd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0) : IsCompact (quotSet K) := by
  refine (hK.prod hK).image_of_continuousOn ?_
  have hc1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have hc2' : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  have hc2 : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)⁻¹) (K ×ˢ K) :=
    continuousOn_inv.comp hc2'.continuousOn fun p hp => hd p.2 hp.2
  exact hc1.continuousOn.mul hc2

end GlobalTheory.SgInf.LocEmb

theorem GlobalTheory.SgInf.lint_compact_le_quot : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r))
    (K₀ : Set (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS →
    IsQuotMeas μG μS ν → IsCompact K₀ → ∃ C : ENNReal, C < ⊤ ∧ ∀ F : Mt k r → ENNReal, Measurable F →
    (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∫⁻ x in K₀, F x ∂μG ≤ C * ∫⁻ x, F x ∂ν := by
  intro k r S μG μS ν K₀ hS hG hSH hU hQ hK₀
  set K : Set (Mt k r) := K₀ ∩ {x | (Matrix.of x : Mat k r) ∈ GG k r} with hKdef
  have hGc : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := LocEmb.isClosed_GG
  have hK : IsCompact K := hK₀.inter_right hGc
  have hKd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0 := fun x hx => LocEmb.det_ne_zero_of_mem hx.2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨μS (LocEmb.quotSet K), (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r S μS hS hSH).1 _ (LocEmb.isCompact_quotSet hK hKd), ?_⟩
  intro F hF hinv

  have hfib : ∀ x : Mt k r, ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
      μS (LocEmb.quotSet K) * F x := by
    intro x
    set A : Set (Mt k r) := {s | (Matrix.of s : Mat k r) ∈ S ∧
      (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K} with hA
    have h1 : ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
        ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := by
      refine lintegral_mono_ae ?_
      have hnull : μS {x | Matrix.of x ∉ S} = 0 := hSH.2.2.1
      filter_upwards [(ae_iff (p := fun s : Mt k r => (Matrix.of s : Mat k r) ∈ S)).2 hnull] with s hs'
      by_cases hsK : (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K
      · rw [Set.indicator_of_mem hsK, Set.indicator_of_mem (show s ∈ A from ⟨hs', hsK⟩)]
        exact le_of_eq (hinv _ hs' x)
      · rw [Set.indicator_of_notMem hsK]; simp
    have h2 : μS A ≤ μS (LocEmb.quotSet K) := by
      rcases A.eq_empty_or_nonempty with hAe | ⟨s₀, hs₀S, hs₀K⟩
      · rw [hAe, measure_empty]; simp
      set t : Mat k r := Matrix.of s₀ with ht
      have htS : t⁻¹ ∈ S := hS.2.2.2.2 _ hs₀S
      have hdx : (Matrix.of x : Mat k r).det ≠ 0 := by
        have := hKd _ hs₀K
        have h' : (Matrix.of (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r) : Mat k r) =
          (Matrix.of s₀ : Mat k r) * Matrix.of x := rfl
        rw [h', Matrix.det_mul] at this
        exact right_ne_zero_of_mul this
      have hsub : A ⊆ rmulM t⁻¹ ⁻¹' LocEmb.quotSet K := by
        intro s ⟨_, hsK⟩
        refine ⟨((fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r),
          (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r)), ⟨hsK, hs₀K⟩, ?_⟩
        show (Matrix.of s : Mat k r) * Matrix.of x * ((Matrix.of s₀ : Mat k r) * Matrix.of x)⁻¹ =
          (Matrix.of s : Mat k r) * t⁻¹
        rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of s : Mat k r),
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdx), Matrix.mul_one]
      calc μS A ≤ μS (rmulM t⁻¹ ⁻¹' LocEmb.quotSet K) := measure_mono hsub
        _ ≤ (μS.map (rmulM t⁻¹)) (LocEmb.quotSet K) :=
          Measure.le_map_apply (continuous_rmulM _).measurable.aemeasurable _
        _ = μS (LocEmb.quotSet K) := by rw [hU.1 _ htS]
    calc _ ≤ ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := h1
      _ ≤ F x * μS A := lintegral_indicator_const_le _ _
      _ ≤ F x * μS (LocEmb.quotSet K) := by gcongr
      _ = μS (LocEmb.quotSet K) * F x := mul_comm _ _
  have hnullG : μG {x | Matrix.of x ∉ GG k r} = 0 := hG.2.2.1
  calc ∫⁻ x in K₀, F x ∂μG = ∫⁻ x, K₀.indicator F x ∂μG :=
        (lintegral_indicator hK₀.isClosed.measurableSet F).symm
    _ ≤ ∫⁻ x, K.indicator F x ∂μG := by
        refine lintegral_mono_ae ?_
        filter_upwards [(ae_iff (p := fun x : Mt k r => (Matrix.of x : Mat k r) ∈ GG k r)).2 hnullG] with x hx'
        by_cases h0 : x ∈ K₀
        · rw [Set.indicator_of_mem h0, Set.indicator_of_mem (show x ∈ K from ⟨h0, hx'⟩)]
        · rw [Set.indicator_of_notMem h0]; simp
    _ = ∫⁻ x, (∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν :=
        hQ _ (hF.indicator hKm)
    _ ≤ ∫⁻ x, μS (LocEmb.quotSet K) * F x ∂ν := lintegral_mono hfib
    _ = μS (LocEmb.quotSet K) * ∫⁻ x, F x ∂ν := lintegral_const_mul _ hF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralCompactLeQuotientMeasureBesselStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lintegral_compact_le_quotientMeasure_bessel : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)) (K₀ : Set (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν → IsCompact K₀ → ∃ C : ENNReal, C < ⊤ ∧ ∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∫⁻ x in K₀, F x ∂μG ≤ C * ∫⁻ x, F x ∂ν := by
  first | exact @GlobalTheory.SgInf.lint_compact_le_quot | exact GlobalTheory.SgInf.lint_compact_le_quot | (intros; apply GlobalTheory.SgInf.lint_compact_le_quot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBesselCoefficientCompactLe

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem lint_Afun_compact_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u ∈ DD σ w, AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ K hK
  classical
  have hStd' := hStd
  have hSide' := hSide
  obtain ⟨-, hrep, -, -, hHaar, hSchur, -, hDecay, -⟩ := hStd'
  obtain ⟨hz, hT, hπ, hμS, -⟩ := hSide'
  obtain ⟨hclG, -, -, hclS, -⟩ := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hUni : IsUnimod (Sset k r z) μS := ((GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1) hμS
  obtain ⟨ν, hν⟩ := exists_isQuotMeas_Sset k r z μG μS hz hT hHaar hμS
  obtain ⟨C₀, hC₀, hC⟩ := GlobalTheory.T.lintegral_compact_le_quotientMeasure_bessel k r (Sset k r z) μG μS ν K hclS hHaar hμS hUni hν hK
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w :=
    (GlobalTheory.SgInfDD.DD_stable_dense k r σ w hrep).1
  have hD1 := fun u (hu : u ∈ DD σ w) => GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide
    (DD σ w : Set H) (fun g hg x hx => hstab g hg x hx) hDecay u hu v hv
  have hPi := (GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hz hT hπ).2.1
  have hD3 := fun u (hu : u ∈ DD σ w) =>
    GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ
  set ψ := psiGen k r z c with hψ
  set bc : ℂ := ⟪ξ, be ψ π μS σ v v ξ⟫_ℂ with hbc
  refine ⟨C₀.toReal * bc.re / d, fun u hu => ?_⟩
  set A : Mt k r → Wp := fun x => Afun ψ π μS σ u v ξ (Matrix.of x) with hA
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  set GM : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hGM
  have hGMc : IsClosed GM := hclG.2.1.preimage hof
  have hAc : ContinuousOn A GM := by
    have h1 : ContinuousOn (fun x : Mat k r => Afun ψ π μS σ u v ξ x) (GG k r) :=
      (hD1 u hu).2.2.2.clm_apply continuousOn_const
    exact h1.comp hof.continuousOn (fun x hx => hx)
  have hae : ∀ᵐ x ∂μG, x ∈ GM := by
    rw [ae_iff]; exact hHaar.2.2.1
  refine ⟨?_, ?_⟩
  · have h1 : AEStronglyMeasurable A (μG.restrict GM) :=
      hAc.aestronglyMeasurable hGMc.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem hae] at h1
    exact h1.restrict
  set F : Mt k r → ENNReal := GM.indicator (fun x => (‖A x‖₊ : ENNReal) ^ 2) with hF
  have hFm : Measurable F := by
    have h1 : ContinuousOn (fun x => (‖A x‖₊ : ENNReal) ^ 2) GM := by
      have h0 : ContinuousOn (fun x => (‖A x‖₊ : ENNReal)) GM :=
        (ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hAc
      exact (ENNReal.continuous_pow 2).comp_continuousOn h0
    have h2 := ContinuousOn.measurable_piecewise h1
      (continuousOn_const (c := (0 : ENNReal)) (s := GMᶜ)) hGMc.measurableSet
    have h3 : F = GM.piecewise (fun x => (‖A x‖₊ : ENNReal) ^ 2) (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ GM <;> simp [hF, hx]
    rw [h3]; exact h2
  have hFinv : ∀ s ∈ Sset k r z, ∀ x, F (lmulM s x) = F x := by
    intro s hs x
    have hsG : s ∈ GG k r := hclS.1 hs
    have hmem : lmulM s x ∈ GM ↔ x ∈ GM := by
      constructor
      · intro h
        have h1 : s⁻¹ * (s * (Matrix.of x : Mat k r)) ∈ GG k r :=
          hclG.2.2.2.1 _ (hclG.2.2.2.2 _ hsG) _ h
        have h2 : s⁻¹ * (s * (Matrix.of x : Mat k r)) = Matrix.of x := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hsG), Matrix.one_mul]
        rw [h2] at h1; exact h1
      · intro h; exact hclG.2.2.2.1 _ hsG _ h
    by_cases hx : x ∈ GM
    · have hx' := hmem.2 hx
      rw [hF, Set.indicator_of_mem hx', Set.indicator_of_mem hx]
      have hAeq : A (lmulM s x) = PiS ψ π s (A x) := by
        show be ψ π μS σ (σ (s * Matrix.of x) u) v ξ =
          PiS ψ π s (be ψ π μS σ (σ (Matrix.of x) u) v ξ)
        have hm : σ (s * Matrix.of x) = (σ s).comp (σ (Matrix.of x)) := hrep.1.2 s hsG _ hx
        have hxu : σ (Matrix.of x) u ∈ DD σ w := hstab _ hx u hu
        have he := ((hD1 _ hxu).2.1 s hs).1
        rw [hm]
        show be ψ π μS σ (σ s (σ (Matrix.of x) u)) v ξ = _
        rw [he]; rfl
      have hn : ‖PiS ψ π s (A x)‖₊ = ‖A x‖₊ := Subtype.ext (hPi.2.1 s hs _)
      rw [hAeq, hn]
    · have hx' : lmulM s x ∉ GM := fun h => hx (hmem.1 h)
      rw [hF, Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
  obtain ⟨-, -, hL2, hnorm, hb0, hbim⟩ := hD3 u hu
  have hint : Integrable (fun x => ‖A x‖ ^ 2) ν := hL2.integrable_norm_pow (by norm_num)
  have hval : ∫ x, ‖A x‖ ^ 2 ∂ν = ‖u‖ ^ 2 * bc.re / d := by
    have h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h2 : bc = (bc.re : ℂ) := by
      apply Complex.ext <;> simp [hbim]
    have h3 : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h4 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖u‖ ^ 2 * bc.re / d : ℝ) : ℂ) := by
      rw [← h1]
      refine hnorm.trans ?_
      rw [h3]
      push_cast
      rw [← h2]
    exact_mod_cast h4
  have hlin : ∫⁻ x, (‖A x‖₊ : ENNReal) ^ 2 ∂ν = ENNReal.ofReal (‖u‖ ^ 2 * bc.re / d) := by
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ← enorm_eq_nnnorm, ofReal_norm_eq_enorm]
  calc ∫⁻ x in K, (‖A x‖₊ : ENNReal) ^ 2 ∂μG = ∫⁻ x in K, F x ∂μG := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hae] with x hx
        rw [hF, Set.indicator_of_mem hx]
    _ ≤ C₀ * ∫⁻ x, F x ∂ν := hC F hFm hFinv
    _ ≤ C₀ * ∫⁻ x, (‖A x‖₊ : ENNReal) ^ 2 ∂ν := by
        refine mul_le_mul_right ?_ _
        exact lintegral_mono fun x => Set.indicator_le_self _ _ x
    _ = ENNReal.ofReal (C₀.toReal * bc.re / d * ‖u‖ ^ 2) := by
        rw [hlin]
        have hC₁ : C₀ = ENNReal.ofReal C₀.toReal := (ENNReal.ofReal_toReal hC₀.ne).symm
        conv_lhs => rw [hC₁]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        congr 1; ring

end GlobalTheory.SgInf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBesselCoefficientCompactLeStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lintegral_besselCoefficient_compact_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u ∈ DD σ w, AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
  first | exact @GlobalTheory.SgInf.lint_Afun_compact_le | exact GlobalTheory.SgInf.lint_Afun_compact_le | (intros; apply GlobalTheory.SgInf.lint_Afun_compact_le <;> assumption)
end
end
