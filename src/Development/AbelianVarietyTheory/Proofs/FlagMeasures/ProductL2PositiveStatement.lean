module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBruhatFunctionLocalBesselIntegralEqL2MassStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubgroupHaarEqConstSmulPiLocalMeasuresStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PiMapMulRight
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasurePreservingPiProd
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselNormSqBruhatProductStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LintegralFintypeProd
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiPulledBackUnipotentMeasureEqBesselImage

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

theorem pi_muNl_eq_dnB_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (A : Set X.B.I.Ginf), 0 < θ → MeasurableSet A → Measure.pi (fun v => muNl C (X.pl v) v) A = Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' A) := by
  intro D X θ C A hθ _hA
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ w rfl
      exact sf_muNl C τ hθ
    intro v
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  obtain ⟨hemb, hmap⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have h := congrArg (fun μ => μ (Formalism.L2.SG.LoopTerm.trInf C '' A)) hmap
  rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective] at h
  exact h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiPulledBackUnipotentMeasureEqBesselImageStatement

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

theorem _root_.GlobalTheory.T.pi_pulledBack_unipotentMeasure_eq_besselImage : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (A : Set X.B.I.Ginf), 0 < θ → MeasurableSet A → Measure.pi (fun v => muNl C (X.pl v) v) A = Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' A) := by
  first | exact @GlobalTheory.pi_muNl_eq_dnB_image | exact GlobalTheory.pi_muNl_eq_dnB_image | (intros; apply GlobalTheory.pi_muNl_eq_dnB_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstSmulPiLocalMeasures

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory.MuNPi

open Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem muN_eq_pi_muNl : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muNl C (X.pl v) v) (NGv X u v : Set _) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muNl C τ w) (NGv X u w : Set _) := by
      rintro τ _ rfl
      exact invOn_muNl C u τ
    exact fun v => h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muNl C (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muN_haar u
  haveI := hσ
  rw [← NinfG_coe] at hc hi
  refine PiM.uniq_on_closed (NinfG X u) (NinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [NinfG, Subgroup.coe_pi]
    exact PiM.pi_conc _ _ fun v => (hloc v).2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v) (hg v (Set.mem_univ v))
  · exact PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuNPi
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstSmulPiLocalMeasuresStatement

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

theorem _root_.GlobalTheory.T.unipotentHaar_eq_const_smul_pi_localMeasures : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  first | exact @GlobalTheory.MuNPi.muN_eq_pi_muNl | exact GlobalTheory.MuNPi.muN_eq_pi_muNl | (intros; apply GlobalTheory.MuNPi.muN_eq_pi_muNl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupHaarProductEqPiLocalImage

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section
namespace GlobalTheory.MuSPi

theorem muNH_prod_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) (κN κH : ℝ≥0∞), X.muN u = κN • Measure.pi (fun v => muNl C (X.pl v) v) → X.muH u = κH • Measure.pi (fun v => muHl C u (X.pl v) v) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = (κN * κH) • Measure.pi (fun v => QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
  intro D X θ C u κN κH hN hH
  have hsN : ∀ v, SigmaFinite (muNl C (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ _ rfl; exact sf_muNl C τ (Formalism.L2.SG.Pf.WuBL.theta_pos C u τ)
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsH : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsM : ∀ v, SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl; exact (invOn_mulMap C u τ).1
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  rw [hN, hH, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul _ (measurable_mul.aemeasurable)]
  congr 1
  have mp := Formalism.L2.SG.RealObj.InfCut.ProductExactness.measurePreserving_piProd (fun v => muNl C (X.pl v) v) (fun v => muHl C u (X.pl v) v)
  rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
    mp.measurable]
  haveI : ∀ v, SigmaFinite (((muNl C (X.pl v) v).prod (muHl C u (X.pl v) v)).map
      (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hsM
  exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
    (fun v => measurable_mul.aemeasurable)

end GlobalTheory.MuSPi
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupHaarProductEqPiLocalImageStatement

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

theorem _root_.GlobalTheory.T.unipotentSubgroupHaarProduct_eq_pi_localImage : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) (κN κH : ℝ≥0∞), X.muN u = κN • Measure.pi (fun v => muNl C (X.pl v) v) → X.muH u = κH • Measure.pi (fun v => muHl C u (X.pl v) v) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = (κN * κH) • Measure.pi (fun v => QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
  first | exact @GlobalTheory.MuSPi.muNH_prod_pi | exact GlobalTheory.MuSPi.muNH_prod_pi | (intros; apply GlobalTheory.MuSPi.muNH_prod_pi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductL2Positive

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProductL2
open Formalism.L2.SG.Pf.AmpWinLoc

theorem prod_lint (D : D7) (X : HidaSetting D) (u : D.what₂.Word)
    (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞) (hβm : ∀ v, Measurable (β v)) :
    ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ y, β v y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hW : ∀ x : X.B.I.Ginf, ‖X.Wu u x‖ₑ ^ 2 = ∏ v, ‖X.Wloc u v (x v)‖ₑ ^ 2 := by
    intro x
    have : ‖X.Wu u x‖ₑ = ∏ v, ‖X.Wloc u v (x v)‖ₑ := by
      rw [← ofReal_norm_eq_enorm, Formalism.L2.SG.Pf.WuDec.norm_Wu,
        ENNReal.ofReal_prod_of_nonneg (fun v _ => norm_nonneg _)]
      simp only [ofReal_norm_eq_enorm]
    rw [this, Finset.prod_pow]
  simp_rw [hW, ← Finset.prod_mul_distrib]
  have : ∀ v, SigmaFinite (Formalism.REAL.muG (X.B.I.ε v)) := fun v => inferInstance
  exact QPK.lintegral_fintype_prod (μ := fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v y => β v y * ‖X.Wloc u v y‖ₑ ^ 2)
    (fun v => (hβm v).mul ((X.Wloc_cont u v).enorm.measurable.pow_const 2))

theorem muH_univ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) :
    Measure.pi (fun v => muHl C u (X.pl v) v) Set.univ = 1 := by
  haveI : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := fun v => by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    exact h _ _ (X.pl.symm_apply_apply v)
  rw [Measure.pi_univ]
  refine Finset.prod_eq_one fun v _ => ?_
  have h : ∀ τ w, vOf X τ = w → muHl C u τ w Set.univ = 1 := by
    rintro τ _ rfl
    rw [← Set.preimage_univ (f := eT C τ (vOf X τ)), ← Measure.map_apply (eT_emb C τ _).measurable MeasurableSet.univ,
      map_muHl C u τ, C.muW_one u τ]
  exact h _ _ (X.pl.symm_apply_apply v)

end GlobalTheory.ProductL2

namespace GlobalTheory.ProductL2
open Formalism.L2.SG.Pf.AmpWinLoc

theorem l2prod : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → 0 < (X.muN u (Y.FN u)).toReal → 0 < (X.muH u Set.univ).toReal → (∀ τ, 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) ∧ (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
  intro D X Y θ C hB u hθ _ _ _
  have key : ∀ v, ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) = 1) ∧
      (∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) =
        l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v))) ∧
      SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    intro v
    have h : ∀ τ w, vOf X τ = w → ∃ β : Formalism.REAL.UJ (X.B.I.ε w) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ w) (muHl C u τ w)) = 1) ∧
        (∫⁻ y, β y * ‖X.Wloc u w y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε w)) =
          l2SG (C.nuS u τ) (phiOf hB u τ)) ∧
        SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl
      obtain ⟨β, h1, h2, h3⟩ := GlobalTheory.T.exists_bruhatFunction_localBesselIntegral_eq_L2Mass D X θ C hB u τ
      exact ⟨β, h1, h2, h3, (invOn_mulMap C u τ).1⟩
    exact h (X.pl v) v (X.pl.symm_apply_apply v)
  choose β hβm hβ1 hβl hsf using key
  obtain ⟨κN, hN0, hNt, hN⟩ := GlobalTheory.T.unipotentHaar_eq_const_smul_pi_localMeasures D X θ C u
  obtain ⟨κH, hH0, hHt, hH⟩ := GlobalTheory.T.subgroupHaar_eq_const_smul_pi_localMeasures D X θ C u
  have hS := GlobalTheory.T.unipotentSubgroupHaarProduct_eq_pi_localImage D X θ C u κN κH hN hH
  have hW := GlobalTheory.T.weil_formula_besselNormSq_bruhatProduct D X u (κN * κH) _ hsf hS β hβm hβ1
  rw [prod_lint D X u β hβm] at hW
  simp only [hβl] at hW
  have hP : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = κN * κH := by
    rw [← hW]; exact (Equiv.prod_comp X.pl (fun τ => l2SG (C.nuS u τ) (phiOf hB u τ))).symm
  have hP0 : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 := by rw [hP]; exact mul_ne_zero hN0 hH0
  have hPt : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ ⊤ := by rw [hP]; exact ENNReal.mul_ne_top hNt hHt
  have hne0 : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 := fun τ =>
    (Finset.prod_ne_zero_iff.1 hP0) τ (Finset.mem_univ τ)
  have hnet : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ ⊤ := by
    intro τ ht
    apply hPt
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ht]
    exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun τ' _ => hne0 τ')
  refine ⟨fun τ => ENNReal.toReal_pos (hne0 τ) (hnet τ), ?_⟩
  rw [← ENNReal.toReal_prod, hP, ← GlobalTheory.T.pi_pulledBack_unipotentMeasure_eq_besselImage D X θ C (Y.FN u) hθ (Y.FN_fund u).1, hN, hH,
    Measure.smul_apply, Measure.smul_apply, muH_univ D X θ C u]
  simp only [smul_eq_mul, mul_one, ENNReal.toReal_mul]
  ring

end GlobalTheory.ProductL2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductL2PositiveStatement

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.product_l2_positive : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → 0 < (X.muN u (Y.FN u)).toReal → 0 < (X.muH u Set.univ).toReal → (∀ τ, 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) ∧ (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
  first | exact @GlobalTheory.ProductL2.l2prod | exact GlobalTheory.ProductL2.l2prod | (intros; apply GlobalTheory.ProductL2.l2prod <;> assumption)
end
end
