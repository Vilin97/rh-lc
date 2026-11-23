module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalFormStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeArithmetic
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeHsNormLeDegreeBoundRealPlace
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProofStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapHypothesisOfLargenessConstantGeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeightStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBoundedStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBoundProductOverPlacesLabelStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProofStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeLeCovolumeLocalAmplitudesStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsIdentityOfEqualFlags
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWin

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeHsNormLeDegreeBoundRealPlaceStatement

section

@[expose] public section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_hsNorm_le_degreeBound_realPlace : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → ∀ (j : ℕ) (hj : j ≤ D.R.rS) (q : ℕ) (γ : Mat D.R.k D.R.rS) (s H₁ De : ℝ) (μR νR : Measure (Mt D.R.k D.R.rS)), 1 ≤ j → j + 2 ≤ D.R.k → 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ q → 0 < s → 1 ≤ H₁ → TailBd W.z W.νS A.Φ q H₁ → TailBd W.z' W.νS' A.Φ' q H₁ → DeOK D.R.k D.R.rS W.z W.z' γ De → IsNormalFormStabilizerMeasure D.R.k D.R.rS hj W.z W.z' γ s μR → IsQuotMeas W.μG μR νR → Real.sqrt (hsNormSq (A.J νR γ)) ≤ Real.sqrt (Module.finrank ℂ W.Wp) * (((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) / s * degBd D.R.k D.R.rS j q H₁ De (Dj D.R.k D.R.rS hj W.z W.z' γ) (sgV D.R.k D.R.rS W.z W.z' γ H₁)) := by
  first | exact @GlobalTheory.Amp.sqrt_hsNormSq_amplitude_le_degBd | exact GlobalTheory.Amp.sqrt_hsNormSq_amplitude_le_degBd | (intros; apply GlobalTheory.Amp.sqrt_hsNormSq_amplitude_le_degBd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteQuot

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.StabQuot

theorem sigmaFinite_quot {k r : ℕ} {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS]
    (hS : μS ≠ 0) (hq : IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨f, hf0, hfm, hfi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hm : Measurable fun x => (f x : ℝ≥0∞) := hfm.coe_nnreal_ennreal
  have hact : Measurable fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 :=
    (GlobalTheory.Amp.CutQuot.continuous_act k r).measurable
  have hm2 : Measurable fun p : Mt k r × Mt k r => (f (lmulM (Matrix.of p.2) p.1) : ℝ≥0∞) :=
    hm.comp (hact.comp measurable_swap)
  set F : Mt k r → ℝ≥0∞ := fun x => ∫⁻ s, (f (lmulM (Matrix.of s) x) : ℝ≥0∞) ∂μS with hF
  have hFm : Measurable F := hm2.lintegral_prod_right'
  have hFi : ∫⁻ x, F x ∂ν < 1 := (hq _ hm).symm.trans_lt hfi
  have hFpos : ∀ x, 0 < F x := fun x => by
    have hx : Measurable fun s => (f (lmulM (Matrix.of s) x) : ℝ≥0∞) :=
      hm.comp (continuous_rmulM (k := k) (r := r) (Matrix.of x)).measurable
    rw [hF, lintegral_pos_iff_support hx]
    have : Function.support (fun s => (f (lmulM (Matrix.of s) x) : ℝ≥0∞)) = Set.univ := by
      ext s; simp [(hf0 _).ne']
    rw [this]
    exact Measure.measure_univ_pos.mpr hS
  refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ℝ≥0∞))⁻¹ ≤ F x})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e : {x | (((0 : ℕ) : ℝ≥0∞))⁻¹ ≤ F x} = {x | F x = ∞} := by ext x; simp
      show ν {x | (((0 : ℕ) : ℝ≥0∞))⁻¹ ≤ F x} < ∞
      rw [e, measure_eq_top_of_lintegral_ne_top hFm.aemeasurable (hFi.trans ENNReal.one_lt_top).ne]
      simp
    · exact (meas_ge_le_lintegral_div hFm.aemeasurable (by simp) (by simpa using hn.ne')).trans_lt
        (ENNReal.div_lt_top (hFi.trans ENNReal.one_lt_top).ne (by simp))
  · rw [Set.sUnion_range, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hFpos x).ne'
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩

theorem exists_sigmaFinite_quot : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (μG μ : Measure (Mt k r)), IsHaarOn (UH (Hpk k r)) μG → IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ 1 μ → γ ∈ UH (Hpk k r) → SigmaFinite μ ∧ IsHaarOn (Rset k r γ⁻¹) μ ∧ IsNormalFormStabilizerMeasure k r hj z z' γ 1 (μ.map (conjM γ⁻¹)) ∧ ∃ ν : Measure (Mt k r), SigmaFinite ν ∧ ν {x | Matrix.of x ∉ UH (Hpk k r)} = 0 ∧ IsQuotMeas μG (μ.map (conjM γ⁻¹)) ν := by
  intro k r j hj z z' γ μG μ hG hN hγ
  obtain ⟨-, -, a3, -, a5, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z' z γ⁻¹ 1 μ one_pos hN
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG hγ)] at a5
  obtain ⟨-, b2, b3, b4, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' γ 1 _ one_pos a5
  obtain ⟨ν, hν⟩ := GlobalTheory.SgQuot.exists_isQuotMeas k r _ μG _ b2 hG b3 b4
  haveI := hG.1
  haveI := b3.1
  exact ⟨a3.1, a3, a5, ν, sigmaFinite_quot b3.2.1 hν,
    (GlobalTheory.Amp.CutQuot.cut_quotient k r _ μG _ ν b2 hG b3 b4 hν).1, hν⟩

end GlobalTheory.DegVol.StabQuot
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetIntegralStabilizerExists

section

@[expose] public section

noncomputable section
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fundC_holds : FundC := by
  intro D X Y u t
  obtain ⟨K, hK⟩ : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u t
  set Γ0 := Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) t.lam t.lam' t.lin with hΓ0
  refine ⟨K, hK.1, fun r _ => ?_⟩
  obtain ⟨s0, hs0, hs0F⟩ := hK.2.1 r
  refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
  have h2 : (s0 * s'⁻¹) * (s' * r) ∈ K := by simpa [mul_assoc] using hs0F
  have := hK.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
  exact (mul_inv_eq_one.1 this).symm

end GlobalTheory.TypeAsm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetIntegralStabilizerExistsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists : GlobalTheory.TypeAsm.FundC := by
  first | exact @GlobalTheory.TypeAsm.fundC_holds | exact GlobalTheory.TypeAsm.fundC_holds | (intros; apply GlobalTheory.TypeAsm.fundC_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalData

section

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints GlobalTheory.TypeAsm

namespace GlobalTheory.TypeAsm.AmpTerms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_sqrt {ι : Type} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∏ i, Real.sqrt (f i) = Real.sqrt (∏ i, f i) := by
  have h0 : 0 ≤ ∏ i, Real.sqrt (f i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have h2 : (∏ i, Real.sqrt (f i)) ^ 2 = ∏ i, f i := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hf i)
  rw [← h2, Real.sqrt_sq h0]

theorem prod_bound {ι : Type} [Fintype ι] (x d g : ι → ℝ) (A PB : ℝ) (hA : 0 ≤ A)
    (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ Real.sqrt (d i) * (A / 1 * g i)) (hg : ∏ i, g i ≤ PB) :
    ∏ i, x i ≤ (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * PB) := by
  calc ∏ i, x i ≤ ∏ i, (Real.sqrt (d i) * (A / 1 * g i)) :=
        Finset.prod_le_prod₀ (fun i _ => hx i) (fun i _ => h i)
    _ = (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * ∏ i, g i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, div_one]
    _ ≤ (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * PB) := by
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hg (pow_nonneg hA _)

theorem chain {a V L w vol Pr om vk sd A0f PB G : ℝ} (ha : 0 ≤ a) (hV : 1 ≤ V * L) (hL : 0 ≤ L) (hw : 0 ≤ w)
    (hPr0 : 0 ≤ Pr) (hom : 0 ≤ om) (hvk : 0 ≤ vk)
    (hfact : a * V ≤ w * (vol * Pr)) (hvol : vol ≤ om * (vk * L)) (hPr : Pr ≤ sd * (A0f * PB))
    (hG : vk * L * L * A0f * PB ≤ G) (hsd : 0 ≤ sd) : a ≤ w * sd * G * om := by
  have s1 : a ≤ a * V * L := by nlinarith
  have s2 : a * V * L ≤ w * (vol * Pr) * L := mul_le_mul_of_nonneg_right hfact hL
  have s3 : vol * Pr ≤ om * (vk * L) * Pr := mul_le_mul_of_nonneg_right hvol hPr0
  have s4 : om * (vk * L) * Pr ≤ om * (vk * L) * (sd * (A0f * PB)) :=
    mul_le_mul_of_nonneg_left hPr (by positivity)
  have s5 : w * (vol * Pr) * L ≤ w * (om * (vk * L) * (sd * (A0f * PB))) * L := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left (s3.trans s4) hw
  have s6 : w * (om * (vk * L) * (sd * (A0f * PB))) * L = w * sd * om * (vk * L * L * A0f * PB) := by ring
  have s7 : w * sd * om * (vk * L * L * A0f * PB) ≤ w * sd * om * G :=
    mul_le_mul_of_nonneg_left hG (by positivity)
  nlinarith

theorem sizes {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ}
    (hH : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) (hC' : 40 ≤ C') (hCl : 1 ≤ Cl) :
    D.R.m = 2 * D.R.rS + 2 ∧ 1 ≤ D.host.v ∧ 2 * D.host.v ≤ large₂.sc.b ∧ 1 ≤ D.R.f ∧
      40 * D.R.rS ^ 4 ≤ D.R.k ∧ 5 * D.R.rS ≤ D.R.k ∧ (∀ w, 0 < Tr D w) := by
  obtain ⟨⟨-, hCk, hmf, -, -, -, -, -, -, -, hrd, -, -, -, -, -, -, -, hv, -, -, -, hT, -, hCl0⟩, -, -⟩ := hH.1
  have hm : D.R.m = 2 * D.R.rS + 2 := D.R.rS_two.symm
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrdv : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have h2v : 2 * D.host.v ≤ large₂.sc.b := by
    rw [← hrdv, hb]
    have hpos : 0 < D.host.rdE := by rw [hrdv]; linarith
    have hrd' : Real.log D.host.rdE ≤ large₂.sc.L :=
      hrd.trans (div_le_self (by linarith) hCl)
    exact (Real.log_le_iff_le_exp hpos).1 hrd'
  have hk40 : 40 * D.R.rS ^ 4 ≤ D.R.k := by
    have hmr : (D.R.rS : ℝ) ≤ D.R.m := by rw [hm]; push_cast; linarith
    have hm1 : (1 : ℝ) ≤ D.R.m := by rw [hm]; push_cast; linarith
    have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have h4 : (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := by
      calc (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ hr0 hmr 4
        _ ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
    have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hm5 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by positivity
    have hx : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have h1 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f := le_mul_of_one_le_right hm5 hf1
      exact h1.trans (le_mul_of_one_le_right (by positivity) hL.le)
    have hreal : ((40 * D.R.rS ^ 4 : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      calc 40 * (D.R.rS : ℝ) ^ 4 ≤ 40 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by linarith
        _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by
          apply mul_le_mul_of_nonneg_right hC'; positivity
        _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
        _ ≤ D.R.k := hCk
    exact_mod_cast hreal
  refine ⟨hm, hv, h2v, hf, hk40, ?_, fun w => ?_⟩
  · have : D.R.rS ≤ D.R.rS ^ 4 := by
      rcases Nat.eq_zero_or_pos D.R.rS with h | h
      · rw [h]; norm_num
      · exact Nat.le_self_pow (by norm_num) _
    omega
  · have hb0 : 0 < large₂.sc.b := Real.exp_pos _
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) (hT w).1

theorem amplitudeBound_of_localData_of_tailBound : GlobalTheory.TypeAsm.LocDatC → GlobalTheory.TypeAsm.TailP → GlobalTheory.TypeAsm.AmpP := by
  intro hLoc hTailP Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, hCH, hT⟩ := hTailP Cg cb Cw cT CT C0 hcb hcT
  refine ⟨CH, hCH, fun Cs hCs => ?_⟩
  obtain ⟨C₁, hC₁, hProd⟩ := GlobalTheory.T.localBound_productOverPlaces_label Cs hCs
  obtain ⟨Ca, hCa⟩ := GlobalTheory.amplitude_arithmetic CH hCH
  refine ⟨max Ca 0, le_max_right _ _, fun C hC => ?_⟩
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  have hCaC : Ca ≤ C := (le_max_left _ _).trans hC
  obtain ⟨C'₁, Cl₁, hT1⟩ := hT C₁
  obtain ⟨Clg, hGap⟩ := GlobalTheory.T.gapC_holds
  refine ⟨max C'₁ 40, max (max Cl₁ Clg) 1, fun C' Cl hC' hCl => ?_⟩
  intro D large₂ X Y u hTies hH hConc
  have hCl1 : 1 ≤ Cl := (le_max_right _ _).trans hCl
  obtain ⟨hm, hv, h2v, hf, hk40, hk5, hTr⟩ :=
    GlobalTheory.TypeAsm.AmpTerms.sizes hH ((le_max_right _ _).trans hC') hCl1
  have hStd : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩
  have hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := hH.2.2.2.2.2.2.2
  have hgap := hGap C' Cl Cg cb Cw cT CT C0 D large₂ ((le_max_right _ _).trans ((le_max_left _ _).trans hCl)) hH
  obtain ⟨Ch, hBs, hGood⟩ := hLoc D X ⟨u⟩ hgap hTies.dsig_tie
  have hTail := hT1 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans ((le_max_left _ _).trans hCl))
    D large₂ hTies hH hConc.2.2.2.2.2.2.2
  obtain ⟨hcovTop, hcov1⟩ := GlobalTheory.T.integralUnipotent_covolume_finite_bounded D large₂ X Y u Ch hStd
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  intro t ht
  have hj1 : 1 ≤ jT t := Formalism.L2.SG.KappaOffDiagonal.JPosC_holds Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hConc t ht
  have hjr : jT t ≤ D.R.rS := Nat.sub_le _ _
  obtain ⟨De, P, hP, hDel, hDeOK, hprod⟩ := hProd D large₂ X Y u Ch CH hStd hCH hk40 hk5 t ht hjr hj1
  set c : ℝ := Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * k2a large₂ CH Cs C (jT t) (labT t) with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (amplitude_label_nonneg large₂ hC0 _ _)
  have hinf := (GlobalTheory.DegAsm.WeightInf.main _ _ (HV D) hCM D.R.rS).2 (F0 X u) (Ft t) (dI D) t.lam
  have hex : ∃ N, GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N := by
    obtain ⟨N, hN, -⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hStd t ht
    exact ⟨N, hN⟩
  have key : ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N →
      ‖(Y.tO u u).vec t‖ ≤ c * N.om t.lam := by
    intro N hN
    have hNj : N.j = jT t := (GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t N hN).1
    obtain ⟨β, n₁, g, n₂, hfr⟩ := GlobalTheory.T.adaptedNormalForm_gives_real_normal_form D large₂ X Y u Ch hStd t N hN
    obtain ⟨K, hK⟩ := GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists D X Y u t
    set μ : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := fun τ =>
      (ENNReal.ofReal 1 • GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) with hμ
    have hμN : ∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS N.j_le (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ)
        (gamT Ch t τ)⁻¹ 1 (μ τ) := by
      intro τ
      obtain ⟨h1, h2, h3, hfo⟩ := hfr τ
      obtain ⟨-, hz, hz', hTz, ⟨cc, hnorm⟩, -⟩ := hfo
      exact ⟨hz, hz', hTz, n₁ τ, h1, n₂ τ, h2, g τ, β, cc, hnorm, h3, rfl⟩
    have hvol := GlobalTheory.T.integralStabiliser_covolume_le_indexWeight D large₂ X Y u Ch hStd t N hN μ K hμN hK
    have htr : ∀ (a b : ℕ) (e : a = b) (ha : a ≤ D.R.rS) (hb : b ≤ D.R.rS) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
        (γ : GlobalTheory.SgInf.Mat D.R.k D.R.rS) (s : ℝ) (μ' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
        GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS ha z z' γ s μ' → GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS hb z z' γ s μ' := by
      rintro a b rfl _ _ _ _ _ _ _ h; exact h
    have hμJ : ∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS hjr (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ)
        (gamT Ch t τ)⁻¹ 1 (μ τ) := fun τ => htr _ _ hNj _ _ _ _ _ _ _ (hμN τ)
    have hq : ∀ τ, _ := fun τ => GlobalTheory.DegVol.StabQuot.exists_sigmaFinite_quot D.R.k D.R.rS (jT t) hjr
      (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ) (gamT Ch t τ) (muGB X (Ch.Q τ) (Ch.Qi τ) τ) (μ τ)
      ((hGood.2 u τ).1.2.2.2.2.2.2.1) (hμJ τ) (((GlobalTheory.T.realPointGramMinorsAgree_proof D X Y u Ch τ).2 t).1)
    choose hσμ hHaarμ hNR ν hσν hνnull hνq using hq
    have hfact := GlobalTheory.T.termAmplitude_le_covolume_localAmplitudes D X Y u Ch hBs hGood hcovTop t ht.2 μ ν K
      (fun τ => ⟨hσμ τ, hHaarμ τ, hσν τ, hνnull τ, hνq τ⟩) hK
    have hr1 : 1 ≤ D.R.rS := hj1.trans hjr
    have hjk : jT t + 2 ≤ D.R.k := by
      have : D.R.rS ≤ D.R.rS ^ 4 := Nat.le_self_pow (by norm_num) _
      omega
    have hqq : 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ C₁ * D.R.k * D.R.rS := by
      have a1 : D.R.rS ^ 3 ≤ D.R.rS ^ 5 := Nat.pow_le_pow_right hr1 (by norm_num)
      have a2 : D.R.rS ≤ D.R.rS ^ 5 := Nat.le_self_pow (by norm_num) _
      have a3 : 1 ≤ D.R.rS ^ 5 := Nat.one_le_pow _ _ hr1
      have a4 : 40 * D.R.rS ^ 4 * D.R.rS ≤ D.R.k * D.R.rS := Nat.mul_le_mul_right _ hk40
      have a5 : D.R.k * D.R.rS ≤ C₁ * (D.R.k * D.R.rS) := Nat.le_mul_of_pos_left _ hC₁
      have a6 : 40 * D.R.rS ^ 4 * D.R.rS = 40 * D.R.rS ^ 5 := by ring
      rw [mul_assoc]
      omega
    have hH1 : 1 ≤ H1C large₂ CH := by
      unfold H1C
      exact Real.one_le_rpow (by linarith) (by positivity)
    have hloc := fun τ => GlobalTheory.T.amplitude_hsNorm_le_degreeBound_realPlace D τ u u 1 (locW Ch u u τ) _ (locS hBs u u τ) (by linarith) one_pos (hTr u)
      (hTr u) (hGood.2 u τ).1 (hGood.2 u τ).2 (jT t) hjr (C₁ * D.R.k * D.R.rS) (gamT Ch t τ) 1 (H1C large₂ CH) (De τ) _
      (ν τ) hj1 hjk hqq one_pos hH1 (hTail τ u _ (hGood.2 u τ).1 _ (hGood.2 u τ).2).1
      (hTail τ u _ (hGood.2 u τ).1 _ (hGood.2 u τ).2).2 (hDeOK τ) (hNR τ) (hνq τ)
    have hom0 : 0 ≤ N.om t.lam := hinf.1.trans (hinf.2.1 N hN)
    have hL0 : 0 ≤ lossV D := by unfold lossV; have := hv; positivity
    have hvol' : (Measure.pi μ (trI Ch '' K)).toReal ≤
        N.om t.lam * (D.host.v ^ (D.R.k * (D.R.rS - jT t) * D.R.f) * lossV D) := by
      rw [← hNj]
      exact ENNReal.toReal_le_of_le_ofReal (by have := hv; positivity) hvol
    have hcard : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
    have hsd : ∏ τ, Real.sqrt (Module.finrank ℂ (Formalism.L2.SG.LocWSOf.locW Ch u u τ).Wp : ℝ) =
        Real.sqrt (dpiC X u) := by
      rw [prod_sqrt _ (fun τ => Nat.cast_nonneg _)]
      unfold dpiC
      rw [Formalism.L2.SG.Pf.AmpWin.finrank_tau]
      rfl
    have hA0 : (0 : ℝ) ≤ (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) := by have := hv; positivity
    have hPr := prod_bound _ _ _ _ _ hA0 (fun τ => Real.sqrt_nonneg _) hloc hprod
    rw [hsd, hcard] at hPr
    have hG := hCa C hCaC D.R.k D.R.rS D.R.m D.R.f (jT t) large₂.sc.b D.host.v (k2Del D (jT t) (labT t))
      (k2S D (H1C large₂ CH) (jT t) (labT t)) Cs P hm hj1 hjr (by omega) hf hb2 hv h2v hP hDel (one_le_sigma_product _ _ _)
    have hfinal := chain (norm_nonneg _) hcov1 hL0 (Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun τ _ => Real.sqrt_nonneg _) hom0 (by have := hv; positivity) hfact hvol' hPr hG
      (Real.sqrt_nonneg _)
    refine hfinal.trans (le_of_eq ?_)
    rw [hc]
    unfold k2a H1C
    rfl
  have hfin := hinf.2.2 _ c hc0 hex key
  show ‖(Y.tO u u).vec t‖ ≤ Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t))
  have e : Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t)) =
      c * GlobalTheory.DegAsm.omI (F0 X u) (Ft t) (dI D) t.lam := by
    rw [hc]; unfold omT; ring
  rw [e]; exact hfin

end GlobalTheory.TypeAsm.AmpTerms
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalDataStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.amplitudeBound_at_terms_of_localData : GlobalTheory.TypeAsm.LocDatC → GlobalTheory.TypeAsm.TailP → GlobalTheory.TypeAsm.AmpP := by
  first | exact @GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound | exact GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound | (intros; apply GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound <;> assumption)
end
end
