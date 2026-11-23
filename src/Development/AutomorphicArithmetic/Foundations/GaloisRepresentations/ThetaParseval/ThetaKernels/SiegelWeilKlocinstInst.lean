module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LongWeylFunctional
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockAlg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.GoodAwayEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.ContAdm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EqZeroOfEvalReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocForm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocNbar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocJJA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocNbar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNM
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepWN
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierTransformMatrixSpaceInvolutionStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocalOperatorLongWeylIntegral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocNbar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopMChar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GoodSigPq
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.POfAddQOf

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocinstCont

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula
open PositivityTheory.SiegelWeilFormula.KFock
namespace PositivityTheory.SiegelWeilFormula.KLI
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem goodAway0_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : ∃ Ψ, R.GoodAway w Ψ ∧ Ψ 0 ≠ 0 := by
  let g := (GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
  have hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  have h0 : Ψ 0 ≠ 0 := by
    have hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0 := by
      funext k
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
      rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
      rfl
    have hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1 := by
      rw [hc]
      exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
    have hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _
    simpa [Ψ, hg0] using hp
  refine ⟨Ψ, ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ, fun hz => h0 (by rw [hz]; rfl), fun f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ⟩, h0⟩
theorem locOp_cont_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    ∀ (P : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ), Continuous fun y => L y (fP P) u := by
  intro P u
  obtain ⟨Ψ, hΨ, hΨ0⟩ := _root_.PositivityTheory.SiegelWeilFormula.KLI.goodAway0_k R w
  obtain ⟨Φ, hΦ, hTΦ⟩ := R.exists_adm hT hΨ (isSw_fP P)
  obtain ⟨Z, hZw, hZf, hZu⟩ := R.loc_surj w 0 u
  have hΨZ : Ψ Z = Ψ 0 := by simpa using hΨ.1 0 Z hZw hZf
  have hZu' : R.loc w Z = u := by simpa using hZu
  have key : ∀ y, L y (fP P) u = d.T (d.om (R.ι w y) Φ) Z / Ψ 0 := by
    intro y
    have e := congrFun ((hL y (fP P) (isSw_fP P)).2 Ψ hΨ.1 Φ hΦ hTΦ) Z
    rw [e]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZu', hΨZ]
    field_simp
  set v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) := Z * (incM F d.b.1.toCols₂)ᵀ with hv_def
  have hfv : finOne F • v = 0 := by rw [hv_def, ← Matrix.smul_mul, hZf, Matrix.zero_mul]
  have hev : finOne F • d.dd.e v = 0 := by rw [← LinearEquiv.map_smul, hfv, map_zero]
  let π2 : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have h1 : π2 (finOne F) = 1 := rfl
  have hv : ∀ i, ((d.dd.e v).1 i).2 = 0 ∧ ((d.dd.e v).2 i).2 = 0 := by
    intro i
    have e1 := congrFun (congrArg Prod.fst hev) i
    have e2 := congrFun (congrArg Prod.snd hev) i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply] at e1 e2
    refine ⟨?_, ?_⟩
    · have := congrArg π2 e1
      rw [map_mul, h1, one_mul, map_zero] at this
      exact this
    · have := congrArg π2 e2
      rw [map_mul, h1, one_mul, map_zero] at this
      exact this
  have hadm := rho_adm F d.B.ψ d.ok.good.std d.ok.dbl.adm (d.dd.e v) hv
  have hc := d.ok.dbl.weil.2.1.cont _ hadm Φ hΦ
  refine ((hc.comp (R.cont w)).div_const (Ψ 0)).congr fun y => (key y).symm
end PositivityTheory.SiegelWeilFormula.KLI
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocJJ

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_nbar_of (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) {ε : ℤˣ} {w₀ : d.G} (hw₀ : d.IsW ε w₀)
    {C s : ℂ} {B : d.MF → d.MF} (hW' : R.StepOK w w₀ (locFT C s) B) :
    ∃ κ : ℂ, κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f) := by
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀] at h4
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΨ.2.1 (funext hc)
  have hB4 : d.IsAwayW w (B (B (B (B Ψ)))) := (h4.2 Ψ hΨ.1).1
  have key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X =
      locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X := by
    intro f hf X
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e := (h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    rw [map_one, Module.End.one_apply, hT'] at e
    exact congrFun e X
  have key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ =
      locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀ := by
    intro f hf u
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
    have := key f hf (X₀ + Z)
    rwa [hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2] at this
  by_cases hb : B (B (B (B Ψ))) X₀ = 0
  · have hz : ∀ f : d.LF, IsSw f → f = 0 := by
      intro f hf
      funext u
      have := key0 f hf u
      rw [hb, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hX₀
    refine ⟨1, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_⟩
    · rw [hz f hf]
      simp [locFT_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
  · set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ
    have hκ0 : κ ≠ 0 := div_ne_zero hX₀ hb
    have h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f := by
      intro f hf
      funext u
      have := key0 f hf u
      simp only [Pi.smul_apply, smul_eq_mul, hκ]
      field_simp
      linear_combination -this
    have hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)))) := by
      intro y c hc hy f hf
      obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y c hc hy
      have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
        have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
          rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
          · rw [hz]; simp
          · rw [hz]; simp [Complex.inv_I]
        rw [Matrix.conjTranspose_smul, hc, hs]
      have hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id :=
        R.stepN w hT y' _ hx hy'
      refine ⟨hN.1 _ (hW'.1 f hf), ?_⟩
      by_cases hf0 : ∀ u, f u = 0
      · have : f = 0 := funext hf0
        rw [this, R.locOp_zero hT hG hL y]
        simp [locFT_zero, chirp_zero]
      push Not at hf0
      obtain ⟨u₀, hu₀⟩ := hf0
      have hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X := by
        intro X
        obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
        have := key f hf (X + Z)
        rw [hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [eq_inv_mul_iff_mul_eq₀ hκ0]
        apply mul_left_cancel₀ hu₀
        linear_combination -this
      have hc3 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'
      obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
      have e := (hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
      have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
      rw [hrel] at e1
      apply R.tens_cancel hΨ.1 hΨ.2.1
      rw [← e1, e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]
      ring
    refine ⟨κ, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2,
      fun y c hc hy f hf => ?_⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.localOperator_longWeyl_integral (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ y : GR d.n, mR y = JJ d.n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have hεR : ε = R.ε := R.isW_eps w hw₀
  obtain ⟨C₀, B, hC₀, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def
  have hW' : R.StepOK w w₀ (locFT C₀ s) B := hW
  obtain ⟨κ, hκ, -, hnb, -⟩ := R.locOp_nbar_of hT hG hL hw₀ hW'
  have hk : ((R.sg w : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Units.ne_zero _)
  have hζn : ‖R.ζ‖ = 1 := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 * |((R.sg w : ℤ) : ℝ)| := by
    have h1 : |((R.sg w : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp
    rw [h1, hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]
    norm_num
  obtain ⟨c, hc, hfres⟩ := GlobalTheory.T.fourier_transform_matrix_space_involution d.m d.n C₀ s ((R.sg w : ℤ) : ℝ) hC₀ hk hsn
  refine ⟨κ⁻¹ * c, mul_ne_zero (inv_ne_zero hκ) hc, fun y hy f hf => ?_⟩
  obtain ⟨y₁, y₂, h1, h2, rfl⟩ := jj_split y hy
  have hb1 : (1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hbm : (-1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = -1 := by rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  have hf1 : IsSw (L y₁ f) := (hL y₁ f hf).1
  have hf2 : IsSw (L y₂ (L y₁ f)) := (hL y₂ _ hf1).1
  rw [R.locOp_mul hT hG hL (y₁ * y₂) y₁ f hf, R.locOp_mul hT hG hL y₁ y₂ _ hf1,
    R.locOp_nU hT hG hL y₁ 1 hb1 h1 _ hf2, hnb y₂ (-1) hbm h2 _ hf1, R.locOp_nU hT hG hL y₁ 1 hb1 h1 f hf]
  have hx : (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • (-1 : Matrix (Fin d.n) (Fin d.n) ℂ) = 1 := by
    rw [hεR]
    rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩ <;> rw [he, hz] <;> simp [Complex.inv_I]
  rw [hx]
  obtain ⟨φ, hφ⟩ := hf
  have hch : ∀ g : d.LF, chirp ((R.sg w : ℤ) : ℂ) (1 : Matrix (Fin d.n) (Fin d.n) ℂ) g =
      fun u => Complex.exp (2 * Real.pi * Complex.I * (((R.sg w : ℤ) : ℝ) : ℂ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u := fun g => by
    funext u
    simp [chirp]
  have hin : (fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) =
      chirp ((R.sg w : ℤ) : ℂ) 1 f := rfl
  have h0 : Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) *
        ((Matrix.of (0 : Fin d.m → Fin d.n → ℂ))ᴴ * Matrix.of (0 : Fin d.m → Fin d.n → ℂ)))) = 1 := by
    simp
  simp only [hin]
  rw [h0, one_mul, Pi.smul_apply, smul_eq_mul, hch, hch, ← hφ]
  have := hfres φ
  simp only [locFT] at this ⊢
  rw [this, hφ]
  ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocinstInst

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.KLI
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem locHyp_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    LocHyp (R.sg w) L := by
  have hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.goodAwayEx_k
  refine
    { sw := fun y f hf => (hL y f hf).1
      one := R.locOp_one hT hG hL
      mul := R.locOp_mul hT hG hL
      lin := R.locOp_lin hT hG hL
      nU := R.locOp_nU hT hG hL
      mM := ?_
      nbar := ?_
      longWeylFunctional := R.localOperator_longWeyl_integral hT hA hG hL
      cont := _root_.PositivityTheory.SiegelWeilFormula.KLI.locOp_cont_k hT R hL }
  · obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
    exact ⟨k, fun y a ha hy f hf => hk y a ha hy f hf⟩
  · obtain ⟨C, s, κ, ε, hs, hκ, h4, hf, -, hs2, hη⟩ := R.locOp_nbar hT hA hG hL
    exact ⟨C, s, κ, ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹, hs, hκ, hs2, hη, h4, fun y c hc hy f hf' => hf y c hc hy f hf'⟩
theorem locInst_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (_hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (_hLi : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k) : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k := by
  intro F E _ _ _ _ _ σ d R w L hL
  obtain ⟨sL, ρ, e, hD, h1, h2⟩ := locData_of (_root_.PositivityTheory.SiegelWeilFormula.KLI.locHyp_of_k hT hA R hL)
  exact ⟨sL, ρ, pOf (R.sg w) d.m, qOf (R.sg w) d.m, e, fun hnm => goodSig_pq _ hnm, hD, h1, h2⟩
end PositivityTheory.SiegelWeilFormula.KLI
end
end
end
end
