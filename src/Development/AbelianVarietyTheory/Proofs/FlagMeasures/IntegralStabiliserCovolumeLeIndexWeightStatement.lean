module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalFormStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagToFrameOfNonzeroLevelIsotropicEq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLe
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundConjAndMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal
import Formalism.SharpRestriction.CuspSpanNormBounds.JExistsNatSmulMemL
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormalStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsBaseLatticeStabilizerFixedFrameUnipote
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLeStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitian_stabiliser_covolume_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (gg : ℕ) (Λ : Submodule (𝓞 K) V) (Kf : Set (ι → Mt k r)), 1 ≤ gg → N.IsTerm gg Λ → IsFund (realPts Φ (N.Gam Λ : Set (V ≃ₗ[K] V))) (RP k r g) Kf → Measure.pi (fun _ : ι => lebR0 k r N.j β) Kf ≤ ENNReal.ofReal (N.om Λ * (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι))) := by
  first | exact @GlobalTheory.DegVol.Cov.cov_le | exact GlobalTheory.DegVol.Cov.cov_le | (intros; apply GlobalTheory.DegVol.Cov.cov_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundImage

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovFund

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

def reix (X : HidaSetting D) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) ≃ᵐ X.B.I.Ginf :=
  MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm

theorem reix_apply (p : ∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (τ : D.what₂.Tau) :
    reix X p (vOf X τ) = p τ := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm p τ

theorem reix_symm (x : X.B.I.Ginf) (τ : D.what₂.Tau) : (reix X).symm x τ = x (vOf X τ) := by
  conv_rhs => rw [← (reix X).apply_symm_apply x]
  exact (reix_apply _ τ).symm

theorem trI_apply (x : X.B.I.Ginf) (τ : D.what₂.Tau) : trI C x τ = GlobalTheory.PullbackComparison.eM C τ (x (vOf X τ)) := rfl

theorem trI_emb : MeasurableEmbedding (trI C) := by
  choose g hg hgf using fun τ : D.what₂.Tau =>
    (GlobalTheory.PullbackComparison.eM_emb C τ).exists_measurable_extend (g := id) measurable_id (fun _ => ⟨1⟩)
  refine MeasurableEmbedding.of_measurable_inverse
    (g := fun m => reix X (fun τ => g τ (m τ))) ?_ ?_ ?_ ?_
  · exact Measurable.of_eval fun τ =>
      (GlobalTheory.PullbackComparison.eM_emb C τ).measurable.comp (measurable_pi_apply (vOf X τ))
  · have hR : Set.range (trI C) = Set.univ.pi fun τ => Set.range (GlobalTheory.PullbackComparison.eM C τ) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩ τ _
        exact ⟨x (vOf X τ), (trI_apply C x τ).symm⟩
      · intro hm
        choose a ha using fun τ => hm τ (Set.mem_univ τ)
        refine ⟨reix X a, funext fun τ => ?_⟩
        rw [trI_apply, reix_apply, ha]
    rw [hR]
    exact MeasurableSet.univ_pi fun τ => (GlobalTheory.PullbackComparison.eM_emb C τ).measurableSet_range
  · exact (reix X).measurable.comp
      (Measurable.of_eval fun τ => (hg τ).comp (measurable_pi_apply τ))
  · intro x
    have h1 : (fun τ => g τ (trI C x τ)) = (reix X).symm x := by
      funext τ
      rw [trI_apply, reix_symm]
      exact congrFun (hgf τ) _
    simp only [h1, MeasurableEquiv.apply_symm_apply]

theorem trI_mul (q y : X.B.I.Ginf) : GlobalTheory.DegVol.mulP (trI C q) (trI C y) = trI C (q * y) := by
  funext τ
  have hv : (q * y) (vOf X τ) = q (vOf X τ) * y (vOf X τ) := rfl
  rw [trI_apply C (q * y), hv, GlobalTheory.PullbackComparison.eM_mul]
  rfl

theorem exists_pre {Y : Full X} {u : D.what₂.Word} (t : GT Y u) {x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    (hx : x ∈ GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹)) :
    ∃ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, trI C y = x := by
  have hr : ∀ τ, x τ ∈ Set.range (GlobalTheory.PullbackComparison.eM C τ) := fun τ =>
    GlobalTheory.PullbackComparison.uh_range C τ (hx τ).1.1
  choose a ha using hr
  refine ⟨reix X a, ?_, funext fun τ => ?_⟩
  · rw [GlobalTheory.PullbackComparison.rset_iff C t]
    intro τ
    rw [reix_apply, ha]
    exact hx τ
  · rw [trI_apply, reix_apply, ha]

theorem isFund_image : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1) (t : GT Y u) (K : Set X.B.I.Ginf), FundR t K → GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.TermOp.ROinf t) (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹)) (trI C '' K) := by
  intro D X Y u C t K hK
  refine ⟨(trI_emb C).measurableSet_image.2 hK.1, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := exists_pre C t hx
  obtain ⟨q, ⟨hq, hqK⟩, huniq⟩ := hK.2 y hy
  refine ⟨trI C q, ⟨⟨q, hq, rfl⟩, ?_⟩, ?_⟩
  · rw [trI_mul]
    exact ⟨q * y, hqK, rfl⟩
  · rintro m ⟨⟨q', hq', rfl⟩, hm⟩
    rw [trI_mul] at hm
    obtain ⟨z, hz, hzq⟩ := hm
    have hzq' : z = q' * y := (trI_emb C).injective hzq
    rw [huniq q' ⟨hq', by rw [← hzq']; exact hz⟩]

end GlobalTheory.CovFund
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormStabilizerMeasureEqAnyNormalForm

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Amp.StabHaar

theorem normalFormStabilizerMeasure_eq_any_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (n₁ n₂ g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ) (μR : Measure (Mt k r)), n₁ ∈ Nset k r → n₂ ∈ Nset k r → IsNormal0 k r hj β c z z' g₀ → IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 μR → μR = (lebR0 k r j β).map (conjM n₂⁻¹) ∧ SigmaFinite (lebR0 k r j β) := by
  intro k r j hj z z' n₁ n₂ g₀ β c μR hn₁ hn₂ hg₀ hR
  obtain ⟨hz, hz', hT, -⟩ := id hR

  have hN : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 ((lebR0 k r j β).map (conjM n₂⁻¹)) := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by rw [ENNReal.ofReal_one, one_smul]⟩
  obtain ⟨-, hcl, hHaar, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 _ one_pos hN
  obtain ⟨-, -, hHaarR, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 μR one_pos hR

  obtain ⟨huniq, -, -⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1)
    (Rset k r (n₁ * g₀ * n₂)) ((lebR0 k r j β).map (conjM n₂⁻¹)) (matGroup hcl) hHaar
  obtain ⟨t, -, htop, ht⟩ := huniq μR hHaarR

  have hNt : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) t.toReal μR := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by
      rw [ht, ENNReal.ofReal_toReal htop.ne, Measure.map_smul]
      exact (conj_cont n₂⁻¹).measurable.aemeasurable⟩
  have h1 := normalFormStabilizerMeasure_scalar_le hj z z' _ 1 t.toReal μR hR hNt
  have h2 := normalFormStabilizerMeasure_scalar_le hj z z' _ t.toReal 1 μR hNt hR
  rw [ENNReal.ofReal_one, ENNReal.ofReal_toReal htop.ne] at h1 h2
  have ht1 : t = 1 := le_antisymm h2 h1
  obtain ⟨hH, -⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg₀
  obtain ⟨hσ, -⟩ := hH
  exact ⟨by rw [ht, ht1, one_smul], hσ⟩

end GlobalTheory.Amp.StabHaar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPtsEqImage

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.RatIsomReal

theorem realPts_eq_image : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (Γ : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)),
    (∀ n ∈ Γ, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) →
      GlobalTheory.DegVol.realPts (phiV C) Γ = trI C '' {y | ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
        RatLink X x n ∧ y = x.1 ∧ n ∈ Γ} := by
  intro D X C Γ hΓ
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n (hΓ n hn)
    exact ⟨x.1, ⟨x, n, hx, rfl, hn⟩, GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)⟩
  · rintro ⟨_, ⟨x, n, hx, rfl, hn⟩, rfl⟩
    exact ⟨n, hn, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm.RatIsomReal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeight

section

@[expose] public section

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covTC_holds : CovTC := by
  intro D large₂ X Y u C hStd t N hAd μ K hμ hK
  obtain ⟨hCM, hPl, hvI, hv1, -, hcard, -, -, -, hnorm, hrk, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hTerm := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hStd t N hAd
  obtain ⟨β, n₁, g, n₂, hF⟩ := GlobalTheory.T.adaptedNormalForm_gives_real_normal_form D large₂ X Y u C hStd t N hAd
  have hι : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    exact ⟨(hPl.2 w).choose⟩
  obtain ⟨τ0⟩ := id hι

  have hμeq : ∀ τ, μ τ = (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) ∧
      SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := fun τ => by
    obtain ⟨h1, h2, hinv, hFr⟩ := hF τ
    obtain ⟨-, -, -, -, ⟨c, hc⟩, -⟩ := hFr
    have hm := hμ τ
    rw [hinv] at hm
    exact GlobalTheory.Amp.StabHaar.normalFormStabilizerMeasure_eq_any_normalForm _ _ _ N.j_le _ _ _ _ _ β c _ h1 h2 hc hm
  haveI : SigmaFinite (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) := (hμeq τ0).2

  have hrat := GlobalTheory.TypeAsm.gam_iff_nLam D large₂ X Y u hStd t N hAd
  have hGiso : ∀ n ∈ (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    fun n hn => ((hrat n).1 hn).1.1.1
  have hpts : GlobalTheory.DegVol.realPts (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = trI C '' ROinf t := by
    rw [GlobalTheory.TypeAsm.RatIsomReal.realPts_eq_image D X C _ hGiso]
    congr 1
    ext y
    constructor
    · rintro ⟨x, n, hx, rfl, hn⟩
      obtain ⟨h1, h2⟩ := (hrat n).1 hn
      exact ⟨x, n, hx, rfl, h1, h2⟩
    · rintro ⟨x, n, hx, rfl, h1, h2⟩
      exact ⟨x, n, hx, rfl, (hrat n).2 ⟨h1, h2⟩⟩
  have hfund0 := GlobalTheory.CovFund.isFund_image D X Y u C t K hK
  rw [← hpts] at hfund0
  have hRP : GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => (gamT C t τ)⁻¹) =
      GlobalTheory.DegVol.RP D.R.k D.R.rS (fun τ => n₁ τ * g τ * n₂ τ) := by
    congr 1; funext τ; exact (hF τ).2.2.1
  rw [hRP] at hfund0

  have hunit : ∀ τ, n₁ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ n₂ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ IsUnit (g τ).det :=
    fun τ => ⟨(hF τ).1, (hF τ).2.1, GlobalTheory.Amp.StabHaar.unit_of_GG (hF τ).2.2.2.2.2.2.2.1.choose_spec.1⟩
  obtain ⟨hFund, hvol⟩ := GlobalTheory.DegVol.UnipConj.isFund_conj_and_measure D.host.E (VS D).V D.R.k D.R.rS D.what₂.Tau
    (phiV C) (N.Gam t.lam : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) n₁ g n₂ (trI C '' K)
    (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β) inferInstance hunit hfund0
  have hF' : ∀ τ, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) β
      (fun y => n₂ τ *ᵥ phiV C τ y) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (g τ) := fun τ => by
    rw [hvI]; exact (hF τ).2.2.2
  have hle := GlobalTheory.T.hermitian_stabiliser_covolume_le D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D) β
    (fun τ y => n₂ τ *ᵥ phiV C τ y) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) g hPl hrk hF'
    (by rw [hAd.1, hnorm, hvI, hcard]) (by rw [hvI]; exact hv1) (gS D) t.lam _ (by omega) hTerm hFund
  have hμpi : Measure.pi μ = Measure.pi fun τ => (GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) := by
    congr 1; funext τ; exact (hμeq τ).1
  rw [hμpi, hvol]
  refine hle.trans (le_of_eq ?_)
  rw [hvI, hcard]
  rfl

end GlobalTheory.TypeAsm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeightStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.integralStabiliser_covolume_le_indexWeight : GlobalTheory.TypeAsm.CovTC := by
  first | exact @GlobalTheory.TypeAsm.covTC_holds | exact GlobalTheory.TypeAsm.covTC_holds | (intros; apply GlobalTheory.TypeAsm.covTC_holds <;> assumption)
end
end
