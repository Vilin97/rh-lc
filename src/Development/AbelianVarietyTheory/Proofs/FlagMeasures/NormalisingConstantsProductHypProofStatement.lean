module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
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
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarMeasureBesselUnitaryEqPullbackProductStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLocalQuotientMassEqMeasureRatioStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarMeasureUniqueness
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.WeilQuotientGlobalAssumptions
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselLowestVectorLocalMassEqTransported

section

@[expose] public section

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PhiTranslate

variable {D : D7} {X : HidaSetting D}

theorem transp_mem (C : Choice X 1) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * m * C.Qi τ) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  unfold Formalism.REAL.inUJ
  calc (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ)
      = (C.Qi τ)ᴴ * (mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * m) * C.Qi τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by rw [h3, hm']
    _ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [h2]; simp

theorem exists_uj {n : ℕ} {ε : Fin n → Bool} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.inUJ ε M) :
    ∃ γ : Formalism.REAL.UJ ε, uMat γ = M := by
  have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
  have hl : (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]
  have hr : M * (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.1 hl
  exact ⟨⟨⟨M, _, hr, hl⟩, hM⟩, rfl⟩

theorem phiOf_eq (C : Choice X 1) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    phiOf hB u τ m = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hm (C.y_mem τ)
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    exists_uj (transp_mem C τ hmy)
  unfold wT
  rw [dite_eq_left hex, (hB u τ).choose_spec.2 hex.choose, hex.choose_spec]
  unfold phiOf v0Of sigB bOf
  have hmul := (X.ds (vOf X τ)).2.2.1.1.2 _ (transp_mem C τ hm) _ (transp_mem C τ (C.y_mem τ))
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * (m * C.y τ) * C.Qi τ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (C.Qi τ) (C.Q τ), (C.isT τ).1, Matrix.one_mul]
  rw [← ContinuousLinearMap.comp_apply, ← hmul, e]
  rfl

theorem bessel_lowest_vector_local_mass_eq_transported : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  intro D X C hB hG u τ
  obtain ⟨hLF, hGW⟩ := hG
  obtain ⟨hW, -⟩ := hGW u τ
  obtain ⟨hc, -, hz, -, hTz, -, hGm, hWm, -, -, -, -, hq, -⟩ := hW
  obtain ⟨-, -, hSm, hcont, heq, -⟩ := hLF u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    refine lt_of_lt_of_eq ?_ hTz.symm
    unfold Tr
    exact_mod_cast (D.mem u).A.T_prime.pos
  have hN0 : muNB D 1 ≠ 0 := by
    intro h0
    apply hSm.2.1
    show (((C.muW u τ).prod (muNB D 1)).map _ : Measure _) = 0
    rw [h0, Measure.prod_zero, Measure.map_zero]
  have hκ : kapN D 1 ≠ 0 := fun h => hN0 (by simp [muNB, haarLie, h])
  have hN : IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (muNB D 1) :=
    Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ ENNReal.ofReal_ne_top
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular D.R.k D.R.rS
  obtain ⟨hGH1, hGH2⟩ := hGH _ hGm
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar _ _ _ _ _ hz hT hWm hN
  have hset : PI.QuotientSetting (BranchingSupport.GG D.R.k D.R.rS) (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ))
      (muGB X (C.Q τ) (C.Qi τ) τ) (Formalism.FourierDecayAlt.ThreeDimData.muSof (C.muW u τ) (muNB D 1)) (C.nuS u τ) :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hWm hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hGm.2.2.1 h0 h1 hq
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ BranchingSupport.GG D.R.k D.R.rS,
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h', hh, m, hmN, rfl⟩ x hx
    rw [heq h' hh m hmN x hx, norm_smul,
      show ‖psiS D (zB X (C.Qi τ) u τ) m‖ = 1 from Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm _ _ _, one_mul]
    exact Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hc h' hh _
  set A : Set (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := {x | Matrix.of x ∈ BranchingSupport.GG D.R.k D.R.rS} with hA
  have hAm : MeasurableSet A := IsClosed.measurableSet (α := Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) hGG.1
  have hc' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊) A := hcont.nnnorm
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊)
      (fun _ => 0)) :=
    hc'.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, Matrix.of x ∈ BranchingSupport.GG D.R.k D.R.rS →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊) (fun _ => 0) x =
        ‖wT C u τ (Matrix.of x)‖₊ :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ (hm.coe_nnreal_ennreal.pow_const 2) (fun s hs x hx => by
    rw [hval x hx, hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)]
    congr 2
    exact NNReal.eq (hinv s hs _ hx)) (C.y τ) (C.y_mem τ)
  unfold l2SG
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => ?_)))
  · simp only
    rw [hval (fun i j => (Matrix.of x * C.y τ) i j) (hGG.2.2.1 _ hx _ (C.y_mem τ)), phiOf_eq C hB u τ hx]
    rfl
  · simp only
    rw [hval x hx]

end GlobalTheory.PhiTranslate
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselLowestVectorLocalMassEqTransportedStatement

section

@[expose] public section

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.l2SG_phiOf_eq_l2SG_wT_of_goodLoc : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  first | exact @GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported | exact GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported | (intros; apply GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstMulTransportedProduct

section

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
  Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.WuDec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem muN_eq_const_mul_pi_trI : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set X.B.I.Ginf, MeasurableSet A →
      X.muN u A = c * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
  intro D X C hB hG u
  choose hsfN hsfH hN hH hH1 hconc β hβm hβ1 hloc using
    Formalism.L2.SG.Pf.AmpWinGlob.place_all C u hG.1 hB
  have hpiN : Set.pi Set.univ (Nloc X u) = X.NinfU u := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; exact Iff.rfl
  obtain ⟨h1, h2, h3, h4⟩ := X.muN_haar u
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Nloc X u))
    (isClosed_set_pi fun v _ => (place_facts X u v).1) (QPK.isGrp_pi _ fun v => (place_facts X u v).2.2.1)
    (X.muN u) (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C)) ⟨h1, h2, by rw [hpiN]; exact h3, by rw [hpiN]; exact h4⟩
    (QPK.invOn_pi _ _ hN)
  obtain ⟨hemb, hmapT⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C (fun v => hsfN v) one_pos
  refine ⟨cN, hcN0, hcNt, fun A _ => ?_⟩
  have htr : trI C = Formalism.L2.SG.LoopTerm.trInf C := rfl
  have hcov : Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C) A =
      Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
    rw [htr, show Measure.pi (fun _ : D.what₂.Tau => muNB D 1) = Formalism.L2.SG.LoopTerm.dnB D 1 from rfl, ← hmapT,
      hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  rw [hcN, Measure.smul_apply, smul_eq_mul, hcov]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstMulTransportedProductStatement

section

@[expose] public section

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentHaar_eq_const_mul_transported_product : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muN u A = c * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
  first | exact @GlobalTheory.muN_eq_const_mul_pi_trI | exact GlobalTheory.muN_eq_const_mul_pi_trI | (intros; apply GlobalTheory.muN_eq_const_mul_pi_trI <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisingConstantsProductHypProof

section

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalConst

theorem constC : ConstC := by
  intro D X Y u C hB hG hcov
  have hS : ∀ τ, GoodS D (lamD D τ) (locS hB u u τ) := fun τ => (hG.2 u τ).2
  have hc : ∀ τ, 0 < cOf hB u τ := fun τ => (hS τ).2.2.2.2.2.2.2.1
  set d : D.what₂.Tau → ℝ := fun τ => (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) with hd
  set L : D.what₂.Tau → ℝ := fun τ => (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal with hL
  have hcL : ∀ τ, cOf hB u τ = L τ / d τ := fun τ => rfl
  have hdpos : ∀ τ, 0 < d τ := by
    intro τ
    rcases (show (0:ℝ) ≤ d τ by positivity).lt_or_eq with h | h
    · exact h
    · have := hc τ; rw [hcL, ← h, div_zero] at this; exact absurd this (lt_irrefl 0)
  have hLpos : ∀ τ, 0 < L τ := by
    intro τ
    rcases (show (0:ℝ) ≤ L τ from ENNReal.toReal_nonneg).lt_or_eq with h | h
    · exact h
    · have := hc τ; rw [hcL, ← h, zero_div] at this; exact absurd this (lt_irrefl 0)
  refine ⟨fun τ => ⟨hc τ, ?_⟩, ?_⟩
  · have e : cOf hB u τ * (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) /
        (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal = 1 := by
      change L τ / d τ * d τ / L τ = 1
      field_simp [(hdpos τ).ne', (hLpos τ).ne']
    unfold sclOf
    rw [e, Real.sqrt_one, Complex.ofReal_one]
  ·
    obtain ⟨cN, hN0, hNT, hN⟩ := GlobalTheory.T.unipotentHaar_eq_const_mul_transported_product D X C hB hG u
    obtain ⟨cH, hH0, hHT, hHu, hH⟩ := GlobalTheory.T.haarMeasure_besselUnitary_eq_pullback_product D X C hB hG u
    have hP := GlobalTheory.T.prod_localQuotientMass_eq_measureRatio D X C hB hG u cN cH hN0 hNT hH0 hHT hN hH
    have hP' : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = cN * cH := by
      rw [← hP]; exact Finset.prod_congr rfl fun τ _ => GlobalTheory.T.l2SG_phiOf_eq_l2SG_wT_of_goodLoc D X C hB hG u τ
    have hFN : MeasurableSet (Y.FN u) := (Y.FN_fund u).1
    have hmN : (X.muN u (Y.FN u)).toReal = cN.toReal * (covN C Y u).toReal := by
      rw [hN _ hFN, ENNReal.toReal_mul]; rfl
    have hmH : (X.muH u Set.univ).toReal = cH.toReal := by rw [hHu]
    have hkey : (∏ τ, L τ) * (covN C Y u).toReal =
        (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
      have : (∏ τ, L τ) = (∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := by
        rw [ENNReal.toReal_prod]
      rw [this, hP', ENNReal.toReal_mul, hmN, hmH]; ring
    have hdd : (Module.finrank ℂ (X.Vpi u) : ℝ) = ∏ τ, d τ := by
      rw [Formalism.L2.SG.Pf.finrank_Vpi X u, Nat.cast_prod]
      exact (Fintype.prod_equiv X.pl.symm (fun τ => d τ) _ fun τ => rfl).symm
    have hprod : ∏ τ, cOf hB u τ = (∏ τ, L τ) / ∏ τ, d τ := by
      rw [← Finset.prod_div_distrib]; exact Finset.prod_congr rfl fun τ _ => hcL τ
    unfold Formalism.L2.SG.TermOp.scl Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X
    rw [hprod, ← hdd]
    set mN := (X.muN u (Y.FN u)).toReal
    set mH := (X.muH u Set.univ).toReal
    set dd := (Module.finrank ℂ (X.Vpi u) : ℝ)
    set V := X.volK2
    set cv := (covN C Y u).toReal
    have hdd0 : 0 < dd := by rw [hdd]; exact Finset.prod_pos fun τ _ => hdpos τ
    have hmN0 : 0 ≤ mN := ENNReal.toReal_nonneg
    have hmH0 : 0 ≤ mH := ENNReal.toReal_nonneg
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    have hc0 : 0 ≤ V * mN * mH / dd := by positivity
    rw [Real.sqrt_mul_self hc0]
    by_cases h0 : V * mN * mH = 0
    · rw [h0, zero_div, _root_.inv_zero]; simp
    · have hV : V ≠ 0 := by intro h; apply h0; rw [h]; ring
      have hmN : mN ≠ 0 := by intro h; apply h0; rw [h]; ring
      have hmH : mH ≠ 0 := by intro h; apply h0; rw [h]; ring
      have e : (V * mN * mH / dd)⁻¹ * V * ((∏ τ, L τ) / dd) * cv = 1 := by
        field_simp
        linear_combination hkey
      rw [e]

end GlobalTheory.LocalConst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisingConstantsProductHypProofStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.normalisingConstantsProductHyp_proof : GlobalTheory.TypeAsm.ConstC := by
  first | exact @GlobalTheory.LocalConst.constC | exact GlobalTheory.LocalConst.constC | (intros; apply GlobalTheory.LocalConst.constC <;> assumption)
end
end
