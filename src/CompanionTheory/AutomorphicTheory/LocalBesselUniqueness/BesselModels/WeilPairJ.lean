module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs2Of
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocDDQ
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingL2
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarOnSkOfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasurableSetNotUH
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntOm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ConjEApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntOm
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MuNcHaar
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MuNcHaar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SsetOfSloc
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralThreeComap

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem sigC_Tm (C : Choice X θ) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    sigB X (Qcs C τ) (Qics C τ) τ (Matrix.of (Tm C τ y)) = X.B.σ (vOf X τ) (uMat y) := by
  have h2 := (transpC' C τ).2.1
  show X.B.σ (vOf X τ) (Qcs C τ * (Qics C τ * uMat y * Qcs C τ) * Qics C τ) = _
  rw [show Qcs C τ * (Qics C τ * uMat y * Qcs C τ) * Qics C τ = (Qcs C τ * Qics C τ) * uMat y * (Qcs C τ * Qics C τ) by
    simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]

theorem lintegral_four_comap (C : Choice X θ) (τ : D.what₂.Tau) {ν0 ν0' μ1 μ1' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (h0 : ν0 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h0' : ν0' {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1 : μ1 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1' : μ1' {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (G : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS →
      Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ x', ∫⁻ s, ∫⁻ s', G (Tm C τ x) (Tm C τ x') (Tm C τ s) (Tm C τ s')
      ∂(μ1'.comap (Tm C τ)) ∂(μ1.comap (Tm C τ)) ∂(ν0'.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) =
    ∫⁻ m, ∫⁻ m', ∫⁻ p, ∫⁻ p', G m m' p p' ∂μ1' ∂μ1 ∂ν0' ∂ν0 := by
  rw [← comap_lint C τ h0 (fun m => ∫⁻ m', ∫⁻ p, ∫⁻ p', G m m' p p' ∂μ1' ∂μ1 ∂ν0')]
  refine lintegral_congr fun x => ?_
  rw [← comap_lint C τ h0' (fun m' => ∫⁻ p, ∫⁻ p', G (Tm C τ x) m' p p' ∂μ1' ∂μ1)]
  refine lintegral_congr fun x' => ?_
  rw [← comap_lint C τ h1 (fun p => ∫⁻ p', G (Tm C τ x) (Tm C τ x') p p' ∂μ1')]
  refine lintegral_congr fun s => ?_
  rw [← comap_lint C τ h1' (fun p' => G (Tm C τ x) (Tm C τ x') (Tm C τ s) p')]

theorem lintegral_three_comap (C : Choice X θ) (τ : D.what₂.Tau) {ν0 μ1 : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (h0 : ν0 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1 : μ1 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (G : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ x', ∫⁻ s, G (Tm C τ x) (Tm C τ x') (Tm C τ s)
      ∂(μ1.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) =
    ∫⁻ m, ∫⁻ m', ∫⁻ p, G m m' p ∂μ1 ∂ν0 ∂ν0 := by
  rw [← comap_lint C τ h0 (fun m => ∫⁻ m', ∫⁻ p, G m m' p ∂μ1 ∂ν0)]
  refine lintegral_congr fun x => ?_
  rw [← comap_lint C τ h0 (fun m' => ∫⁻ p, G (Tm C τ x) m' p ∂μ1)]
  refine lintegral_congr fun x' => ?_
  rw [← comap_lint C τ h1 (fun p => G (Tm C τ x) (Tm C τ x') p)]

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MemOmLoc

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal Classical

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem mem_om_loc {v : InfinitePlace X.B.I.F} {lam : ℂ} (hl : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {sc : ℝ} (hsc : 0 < sc) (u u' : D.what₂.Word) (cv : Fin (D.R.rS + 1) → ℂ)
    (hcv : cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u') (g : Formalism.REAL.UJ (X.B.I.ε v))
    (hg : Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal cv) :
    trG Q Qi g ∈ Formalism.FourierDecayAlt.JF.Om D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u')) := by
  have hsc0 : sc ≠ 0 := hsc.ne'
  set γ : X.B.I.Ginf := Function.update (1 : X.B.I.Ginf) v g with hγdef
  have hγv : γ v = g := by rw [hγdef]; exact Function.update_self _ _ _
  obtain ⟨d, hd⟩ : ∃ d : Fin (D.R.rS + 1) → ℂ, d = fun a => star (dsc (D := D) lam sc a) * dsc (D := D) lam sc a * cv a :=
    ⟨_, rfl⟩
  have hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) (Qi *ᵥ rv X.B.I v (X.zR u'))
      (trG Q Qi g) = Matrix.diagonal d := by
    ext a b
    have := zhat_tr X hQ hsc0 u u' γ a b
    rw [hγv] at this
    rw [this]
    have hZX : ZX X u u' sc γ v = Matrix.diagonal cv := by
      unfold ZX; rw [hγv]; exact hg
    rw [hZX]
    by_cases hab : a = b
    · subst hab; simp [hd]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hd0 : ∀ a, d a ≠ 0 := fun a => by
    rw [hd]; exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr (dsc_ne hl hsc0 a)) (dsc_ne hl hsc0 a)) (hcv.1 a)
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem Q Qi _ hQ.2.1 hQ.2.2.1 g, fun l _ => ?_, ?_⟩
  · rw [dmin_diag _ _ _ d hZ l]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
  · unfold Formalism.QuantumDeterminants.Gf
    rw [dmin_diag _ _ _ d hZ, dmin_diag _ _ _ d hZ,
      (show Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)) = Tw u from (Formalism.L2.SG.Pf.Choice.zTr_of X hQ u).2),
      (show Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) = Tw u' from (Formalism.L2.SG.Pf.Choice.zTr_of X hQ u').2)]
    have hlast := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.normSq_last_gt (Tw u) (Tw u') cv hcv.2
    have hcl : ∀ (h : D.R.rS + 1 ≤ D.R.rS + 1) (i : Fin (D.R.rS + 1)), Fin.castLE h i = i := fun _ _ => Fin.ext rfl
    have hdl : d (Fin.last D.R.rS) = cv (Fin.last D.R.rS) := by simp only [hd, dsc_last, star_one, one_mul]
    obtain ⟨P, hPd⟩ : ∃ P : ℂ, P = ∏ i : Fin D.R.rS, d (Fin.castSucc i) := ⟨_, rfl⟩
    have e1 : ∏ i : Fin (Fin.last (D.R.rS + 1)).val, d (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt) i) =
        P * cv (Fin.last D.R.rS) := by
      show ∏ i : Fin (D.R.rS + 1), d (Fin.castLE _ i) = _
      rw [Fin.prod_univ_castSucc]
      simp only [hcl, hdl, hPd]
    have e2 : ∏ i : Fin (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).val,
        d (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt) i) = P := by
      rw [hPd]; rfl
    rw [e1, e2]
    have hP0 : P ≠ 0 := by rw [hPd]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _
    rw [Complex.normSq_mul]
    have hn : Tw u * Tw u' < Complex.normSq (cv (Fin.last D.R.rS)) := by
      rw [Complex.normSq_eq_norm_sq]; exact hlast
    have hp : 0 < Complex.normSq P := Complex.normSq_pos.mpr hP0
    nlinarith

theorem sideC_SF (C : Choice X θ) (hθ : 0 < θ) (u : D.what₂.Word) (τ : D.what₂.Tau) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h)
    {w0 : X.B.H (vOf X τ)} (hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) w0) :
    ∃ νq, SFinite νq ∧ Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h (sigB X (Qcs C τ) (Qics C τ) τ) w0
      (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ)
      (C.muW u τ) ((muNB D θ).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) (muGB X (Qcs C τ) (Qics C τ) τ) νq := by
  obtain ⟨hz, hT⟩ := zT C u τ
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  have hDS : IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (Qcs C τ) (Qics C τ) τ) := by
    obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
    refine ⟨P, hP, ?_⟩
    exact dsHpk_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
      (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
      (X.B.lam (vOf X τ)) (lamD D τ)
      (fun i => by
        rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
        exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
      (X.B.σ (vOf X τ)) (X.ds (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg P hP
  have hμG := haar_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg
  have hμN := muNc_haar (D := D) hθ
  obtain ⟨νq, hsf, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExistsSF _ _ _ hz hT _ _ hμG
    (isHaarOn_muS_gen hz hT (C.muW_haar u τ) (C.muW_one u τ) (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  exact ⟨νq, hsf, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, hDS, hgap, hok, hlow, hz, hT, cStd_ne, hty_c C u τ,
    C.muW_haar u τ, hμN, hμG, hq⟩

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WeilPairJ

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM

variable {D : D7}

theorem weilPairJ (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C)
    (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : HidaSetting D) (τ : D.what₂.Tau) :
    ∃ (μS ν : D.what₂.Word → Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
      (∀ u, SFinite (μS u) ∧ SFinite (ν u) ∧
        (∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, ∫⁻ s, f (s * x) ∂(μS u) ∂(ν u)) ∧
        (μS u).map (fun x => x⁻¹) = μS u ∧ μS u (Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ))ᶜ = 0 ∧
        ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
            X.B.σ (vOf X τ) (uMat s) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u (vOf X τ) z'‖ₑ ∂(μS u) ∂(ν u) ∂(ν u) < ⊤ ∧
        (∀ s ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ), (μS u).map (fun x => s * x) = μS u) ∧ μS u ≠ 0) ∧
      ∀ (u u' : D.what₂.Word) (sc : ℝ), 0 < sc → ∀ cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u',
        ∀ g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
          Zhat (X.B.I.ε (vOf X τ)) (frm X u sc (vOf X τ)) (frm X u' sc (vOf X τ)) (uMat g) = Matrix.diagonal cv →
          ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
              X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
            ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u' (vOf X τ) z'‖ₑ ∂(μS u') ∂(μS u) ∂(ν u') ∂(ν u) < ⊤ := by
  rcases isEmpty_or_nonempty D.what₂.Word with hEW | hNW
  · exact ⟨fun _ => 0, fun _ => 0, fun u => isEmptyElim u, fun u => isEmptyElim u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have h1 := (transpC' C τ).1
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
  obtain ⟨yc, hyc, hycl⟩ := y_exists (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
    (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
    (X.B.lam (vOf X τ)) (lamD D τ)
    (fun i => by
      rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
      exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
    (X.B.σ (vOf X τ)) (X.ds (vOf X τ)).2.2.1 (X.low (vOf X τ)).2 (Qcs C τ) (Qics C τ) h2 hg P hP
  set σc := sigB X (Qcs C τ) (Qics C τ) τ with hσc
  set w0 := σc yc (X.B.w (vOf X τ)) with hw0
  have hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) σc w0 := by
    refine ⟨P, hP, ?_, hycl⟩
    rw [hw0, sigC_norm C τ hyc]
    exact (X.low (vOf X τ)).1
  obtain ⟨h, hgap, hok⟩ := hGp D hG τ
  set μNc := (muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D)) with hμNc
  have hμN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) μNc := muNc_haar one_pos
  have sN : SigmaFinite (muNB D 1) :=
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D one_pos) (kapN_ne_top D 1)).1

  have hdat : ∀ u : D.what₂.Word, ∃ (l : X.B.H (vOf X τ) → X.Vloc u (vOf X τ)) (a : ℂ) (νq : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
      SFinite νq ∧
      Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h σc w0 (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd
        (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ) (C.muW u τ) μNc
        (muGB X (Qcs C τ) (Qics C τ) τ) νq ∧
      (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
        Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u τ) σc (C.muW u τ) μNc x y =
          (innerSL ℂ (l y)).smulRight (l x)) ∧
      ∀ γ, X.Wloc u (vOf X τ) γ = a • l (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))) := by
    intro u
    obtain ⟨l, a, hbe, hW⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.BM.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u τ
    obtain ⟨νq, hsf, hS⟩ := sideC_SF C one_pos u τ hgap hok hlow
    have hμW := C.muW_haar u τ
    have : SigmaFinite (C.muW u τ) := hμW.1
    refine ⟨l, a, νq, hsf, hS, fun x hx y hy => ?_, hW⟩
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u τ)
      (piB X (Qcs C τ) (Qics C τ) u τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u τ hh) (C.muW u τ) (muNB D 1) hμW.2.2.1 x y]
    exact hbe x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)
  choose l a νq hsf hS hl hW using hdat

  obtain ⟨hyiU, hyi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem yc hyc
  set yi := Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * ycᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS with hyidef
  have hyi' : yc * yi = 1 := mul_eq_one_comm.mp hyi
  set yJ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) :=
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.ujOf _ (inUJ_tr (transpC' C τ) hyiU) with hyJ
  have hTyJ : Matrix.of (Tm C τ yJ) = yi := by
    show Qics C τ * uMat yJ * Qcs C τ = yi
    rw [hyJ, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.uMat_ujOf, show Qics C τ * (Qcs C τ * yi * Qics C τ) * Qcs C τ =
      (Qics C τ * Qcs C τ) * yi * (Qics C τ * Qcs C τ) by simp only [Matrix.mul_assoc], h1, Matrix.one_mul, Matrix.mul_one]
  have hTyJi : Matrix.of (Tm C τ yJ⁻¹) = yc := by
    rw [Tm_inv]
    show (Matrix.of (Tm C τ yJ))⁻¹ = yc
    rw [hTyJ]
    exact Matrix.inv_eq_right_inv hyi
  have key : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)) = σc (Matrix.of (Tm C τ x)) w0 := by
    intro x
    rw [← sigC_Tm C τ (x * yJ⁻¹), hw0, sigC_mul C τ (Tm_mem C τ x) hyc, Tm_mul]
    show σc (Matrix.of (Tm C τ x) * Matrix.of (Tm C τ yJ⁻¹)) (X.B.w (vOf X τ)) = _
    rw [hTyJi]
  have hWl : ∀ u (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), X.Wloc u (vOf X τ) (x * yJ⁻¹) = a u • l u (σc (Matrix.of (Tm C τ x)) w0) := by
    intro u x
    rw [hW u, key]
  have hsig : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), X.B.σ (vOf X τ) (uMat y) = σc (Matrix.of (Tm C τ y)) := fun y =>
    (sigC_Tm C τ y).symm

  have hμGc := haar_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg
  have hSH : ∀ u, Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ))
      (Formalism.MainNotions.S.muS (C.muW u τ) μNc) := fun u =>
    isHaarOn_muS_gen (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ) (C.muW_one u τ)
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN)
  have hSc0 : ∀ u, Formalism.MainNotions.S.muS (C.muW u τ) μNc {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := by
    intro u
    refine measure_mono_null ?_ (hSH u).2.2.1
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm ⊢
    intro hmS
    apply hm
    obtain ⟨h0, hh0, n0, hn0, he⟩ := hmS
    rw [he]
    exact Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hh0.1 hn0.1
  have hνc0 : ∀ u, νq u {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := fun u =>
    quot_conc (hS u).2.2.2.2.2.2.2.2.2.2.2.2 hμGc.2.2.1 (hSc0 u) (hSH u).2.1
  have hcm : ∀ (c : ℝ≥0∞), c ≠ ⊤ → ∀ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞),
      ∫⁻ x, c * f x ∂μ = c * ∫⁻ x, f x ∂μ := fun c hc μ f => lintegral_const_mul' c f hc
  refine ⟨fun u => (Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ),
    fun u => ((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹), fun u => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := (hSH u).1
    have := sigmaFinite_comap C τ (hSc0 u)
    infer_instance
  · have := hsf u
    have := sFinite_comap C τ (μ := νq u)
    infer_instance
  · intro f hf
    have hf' : Measurable (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => f (y * yJ⁻¹)) := hf.comp (measurable_mul_const _)
    have hq : Formalism.MainNotions.S.IsQuotMeas (muGB X (Qcs C τ) (Qics C τ) τ) (Formalism.MainNotions.S.muS (C.muW u τ) μNc) (νq u) :=
      (hS u).2.2.2.2.2.2.2.2.2.2.2.2
    rw [lintegral_map_equiv]
    calc ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
        = ∫⁻ x, f (x * yJ⁻¹) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by
          rw [← lintegral_map hf (measurable_mul_const yJ⁻¹), Formalism.REAL.indefinite_unitary_unimodular _ _ yJ⁻¹]
      _ = _ := weil_J C τ hq (hSc0 u) (hνc0 u) _ hf'
      _ = _ := by
          refine lintegral_congr fun x => lintegral_congr fun s => ?_
          simp only [MeasurableEquiv.coe_mulRight, mul_assoc]
  · exact inv_comap C τ (hSc0 u) (muS_inv (zT C u τ).1 (zT C u τ).2
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ))
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  · rw [(Tm_emb C τ).comap_apply]
    refine measure_mono_null ?_ (hSH u).2.2.1
    rintro _ ⟨x, hx, rfl⟩ hxs
    exact hx (sloc_of_sset C τ u x hxs)
  ·
    have hint := (CompanionTheory.D.Upq.BesselFunctionalConstruction.quadConv CompanionTheory.Lime.BM.inputs D.R.k D.R.rS _ _ (Dc C one_pos u u τ) (epsSH D.R) (lamD D τ) h _
      σc w0 _ _ (νq u) (νq u) (hS u) (hS u) (l u) (l u) (hl u) (hl u)).2
    have e : ∀ x x' s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        ‖⟪X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat s) (X.B.σ (vOf X τ) (uMat (x' * yJ⁻¹)) (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) (x * yJ⁻¹)‖ₑ * ‖X.Wloc u (vOf X τ) (x' * yJ⁻¹)‖ₑ =
        (‖a u‖ₑ * ‖a u‖ₑ) * (((‖⟪σc (Matrix.of (Tm C τ x)) w0, σc (Matrix.of (Tm C τ s))
          (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞)) := by
      intro x x' s
      rw [key, key, hsig s, hWl, hWl, enorm_smul, enorm_smul]
      show _ * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x)) w0)‖ₑ) * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x')) w0)‖ₑ) = _
      simp only [eNorm_eq_nnNorm]
      ring
    have step : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat s)
        (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ * ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u (vOf X τ) z'‖ₑ
          ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹)) =
        (‖a u‖ₑ * ‖a u‖ₑ) * ∫⁻ x, ∫⁻ x', ∫⁻ s, (((‖⟪σc (Matrix.of (Tm C τ x)) w0, σc (Matrix.of (Tm C τ s))
          (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞))
          ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) := by
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x => ?_
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x' => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s => ?_
      exact e x x' s
    rw [step]
    have hL := lintegral_three_comap C τ (hνc0 u) (hSc0 u) (fun m m' p => ((‖⟪σc (Matrix.of m) w0, σc (Matrix.of p)
          (σc (Matrix.of m') w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of m) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of m') w0)‖₊ : NNReal) : ℝ≥0∞))
    beta_reduce at hL
    rw [hL]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hint
  · intro s hs
    have hmap : ((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (Tm C τ) = Formalism.MainNotions.S.muS (C.muW u τ) μNc := by
      rw [(Tm_emb C τ).map_comap, Measure.restrict_eq_self_of_ae_mem]
      rw [ae_iff]
      refine measure_mono_null (fun m hm => ?_) (hSc0 u)
      simp only [Set.mem_ofPred_eq] at hm ⊢
      exact fun h => hm (mem_range_Tm C τ h)
    have hTs := sset_of_sloc C τ u s hs
    have hleft := (hSH u).2.2.2 _ hTs
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) (Matrix.of (Tm C τ s))) :=
      (Formalism.MainNotions.BridgeCSB.continuous_lmulM _).measurable
    have hcomm : Tm C τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (Matrix.of (Tm C τ s)) ∘ Tm C τ := by
      funext y
      exact Tm_mul C τ s y
    rw [← (Tm_emb C τ).comap_map (((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (fun x => s * x)),
      Measure.map_map (Tm_emb C τ).measurable (measurable_const_mul s), hcomm,
      ← Measure.map_map hlm (Tm_emb C τ).measurable, hmap, hleft]
  · intro h0
    beta_reduce at h0
    have hmap : ((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (Tm C τ) = Formalism.MainNotions.S.muS (C.muW u τ) μNc := by
      rw [(Tm_emb C τ).map_comap, Measure.restrict_eq_self_of_ae_mem]
      rw [ae_iff]
      refine measure_mono_null (fun m hm => ?_) (hSc0 u)
      simp only [Set.mem_ofPred_eq] at hm ⊢
      exact fun h => hm (mem_range_Tm C τ h)
    apply (hSH u).2.1
    rw [← hmap, h0, Measure.map_zero]
  ·
    intro u u' sc hsc cv hcv g hgd
    have hom := mem_om_loc (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) hsc u u' cv hcv g hgd
    rw [zc_eq, zc_eq] at hom
    set γc := Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) g with hγc
    have hint := (CompanionTheory.D.Upq.BesselFunctionalConstruction.quadConv CompanionTheory.Lime.BM.inputs D.R.k D.R.rS _ _ (Dc C one_pos u u' τ) (epsSH D.R) (lamD D τ) h _
      σc w0 _ _ (νq u) (νq u') (hS u) (hS u') (l u) (l u') (hl u) (hl u')).1 γc hom
    have hsg : ∀ s s' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) = σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) := by
      intro s s'
      rw [hsig, Tm_mul, Tm_mul, Tm_inv]
      rfl
    have e : ∀ x x' s s' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        ‖⟪X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹))
          (X.B.σ (vOf X τ) (uMat (x' * yJ⁻¹)) (X.B.w (vOf X τ)))⟫_ℂ‖ₑ * ‖X.Wloc u (vOf X τ) (x * yJ⁻¹)‖ₑ * ‖X.Wloc u' (vOf X τ) (x' * yJ⁻¹)‖ₑ =
        (‖a u‖ₑ * ‖a u'‖ₑ) * (((‖⟪σc (Matrix.of (Tm C τ x)) w0,
          σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞)) := by
      intro x x' s s'
      rw [key, key, hsg, hWl, hWl, enorm_smul, enorm_smul]
      show _ * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x)) w0)‖ₑ) * (‖a u'‖ₑ * ‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖ₑ) = _
      simp only [eNorm_eq_nnNorm]
      ring
    have step : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
        X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u' (vOf X τ) z'‖ₑ
          ∂((Formalism.MainNotions.S.muS (C.muW u' τ) μNc).comap (Tm C τ)) ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂(((νq u').comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹)) =
        (‖a u‖ₑ * ‖a u'‖ₑ) * ∫⁻ x, ∫⁻ x', ∫⁻ s, ∫⁻ s', (((‖⟪σc (Matrix.of (Tm C τ x)) w0,
          σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞))
          ∂((Formalism.MainNotions.S.muS (C.muW u' τ) μNc).comap (Tm C τ)) ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂((νq u').comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) := by
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x => ?_
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x' => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s' => ?_
      exact e x x' s s'
    rw [step]
    have hL := lintegral_four_comap C τ (hνc0 u) (hνc0 u') (hSc0 u) (hSc0 u') (fun m m' p p' => ((‖⟪σc (Matrix.of m) w0,
          σc (Matrix.of p * γc * (Matrix.of p')⁻¹) (σc (Matrix.of m') w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of m) w0)‖₊ : NNReal) : ℝ≥0∞) * ((‖l u' (σc (Matrix.of m') w0)‖₊ : NNReal) : ℝ≥0∞))
    beta_reduce at hL
    rw [hL]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hint

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end
end
