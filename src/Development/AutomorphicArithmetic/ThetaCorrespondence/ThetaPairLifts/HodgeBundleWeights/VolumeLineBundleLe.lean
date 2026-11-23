module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeEstimateHypotheses
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefShiftedFubiniStudyOfShortGenerators
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsModelOfImage

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory

open Filter Topology

theorem countVol_le_selfInter : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) (D d a : ℕ) (L : GlobalTheory.HermLB p) (A : ℝ) (m : ℕ → ℕ∞), GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.IsArithVar p D → L.IsNef D → L.IsSelfInter A → 0 < d → 0 < a → (∀ i : ℕ, 1 ≤ i → m (a * i) ≤ (L.pow (a * i)).smallSec.encard) → countVol D d a m ≤ ENNReal.ofReal (A / ((d : ℝ) * ((D : ℝ) + 1))) := by
  intro k _ X _ p D d a L A m hAHS hX hL hA hd ha hm
  have hmul : Tendsto (fun j : ℕ => a * j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j ha) tendsto_id
  have h1 := ((hAHS.tendsto_of_triv hX hL hA).comp hmul).div_const ((d : ℝ) * ((D : ℝ) + 1))
  have h2 := ENNReal.tendsto_ofReal h1
  refine (limsup_le_limsup ?_).trans_eq h2.limsup_eq
  filter_upwards [hmul.eventually (hAHS.of_triv hX hL hA).1, eventually_ge_atTop 1] with j hfin hj
  have hx : 0 ≤ Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hN : (0 : ℝ) < ((a * j : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.mul_pos ha hj)
  have hd' : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have hlog : logCard (m (a * j)) ≤ ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) := by
    rw [← logCard_coe, hfin.cast_ncard_eq]
    exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (hm j hj)))
  have hden : (d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((d : ℝ) * ((a * j : ℕ) : ℝ) ^ (D + 1)) := by
    rw [ENNReal.ofReal_mul hd'.le, ENNReal.ofReal_pow hN.le, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  calc _ ≤ (D.factorial : ℝ≥0∞) * ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) /
        ((d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1)) := by gcongr
    _ = _ := by
      rw [hden, ← ENNReal.ofReal_natCast (D.factorial), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [Function.comp]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical


theorem _root_.GlobalTheory.T.countingVolume_le_selfIntersection_nefHermitianBundle : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) (D d a : ℕ) (L : GlobalTheory.HermLB p) (A : ℝ) (m : ℕ → ℕ∞), GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.IsArithVar p D → L.IsNef D → L.IsSelfInter A → 0 < d → 0 < a → (∀ i : ℕ, 1 ≤ i → m (a * i) ≤ (L.pow (a * i)).smallSec.encard) → countVol D d a m ≤ ENNReal.ofReal (A / ((d : ℝ) * ((D : ℝ) + 1))) := by
  first | exact @GlobalTheory.countVol_le_selfInter | exact GlobalTheory.countVol_le_selfInter | (intros; apply GlobalTheory.countVol_le_selfInter <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefShiftedFubiniStudyOfShortGeneratorsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical


theorem _root_.GlobalTheory.T.isNef_shifted_fubiniStudy_of_short_generators : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → (L.shift (fun _ => t) (fun _ => rfl)).IsNef D := by
  first | exact @GlobalTheory.ImageModel.isNef_shift_of_isShortGen | exact GlobalTheory.ImageModel.isNef_shift_of_isShortGen | (intros; apply GlobalTheory.ImageModel.isNef_shift_of_isShortGen <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsNefModelOfImage

section

@[expose] public section

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
namespace SelfIntersectionVolumeEstimates.ImageNefG
theorem exists_nef_model_of_image : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (abelian₂ t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) w abelian₂ → Real.log abelian₂ ≤ t → ∃ (k : Type) (_ : CommRing k) (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp k) (L : GlobalTheory.HermLB p) (A : ℝ), GlobalTheory.IsArithVar p (dimFlag (T.Q.Dw j)) ∧ L.IsNef (dimFlag (T.Q.Dw j)) ∧ L.IsSelfInter A ∧ A ≤ (Module.finrank ℚ Y.d.c₂.F : ℝ) * ((dimFlag (T.Q.Dw j) : ℝ) + 1) * (Y.dg u Z * (Y.ht u Z + t)) ∧ ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ (L.pow (8 * i)).smallSec.encard := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro hPX hP D T j Y e o hY h2 Z u n w abelian₂ t hG hB hN hd hS hL
  obtain ⟨hgram, hfg, hspan⟩ := hG
  have hK : ∀ σ : Y.d.c₂.F →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ := fun σ => conj_comp_ne σ
  have hconj : ∀ σ (x : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)),
      normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) ((starRingEnd ℂ).comp σ) x =
        normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) σ x :=
    fun σ x => petOn_conj Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) σ (x : Rul Y.d.Xo₂ Y.d.c₂)
  have hdeg : 0 < imageDeg (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) := by
    have := hd
    simp only [Deep.dg, compDeg, Nat.cast_pos] at this
    exact this
  have hB' : GlobalTheory.DegVal.GenRatios (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) := hB
  obtain ⟨X, hX, p, L0, ψ, s, hM⟩ := _root_.GlobalTheory.T.image_admits_model hP Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
    (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
    (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) hK hgram hconj hfg hspan hB hdeg
  obtain ⟨h, hh, -⟩ := hP.q11.existsUnique hM.arith (L0.shift (fun _ => t) (fun _ => rfl))
  refine ⟨𝓞 Y.d.c₂.F, inferInstance, X, hX, p, L0.shift (fun _ => t) (fun _ => rfl),
    h (genericPoint X), hM.arith, ?_, ⟨h, hh, rfl⟩, ?_, ?_⟩
  · exact GlobalTheory.T.isNef_shifted_fubiniStudy_of_short_generators Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
      (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
      (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) X p L0 ψ s n w abelian₂ t hM hB'.1 hS hL
  · have key : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) := by
      exact hPX.1
    exact key hP Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
      (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
      (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) X p L0 ψ s t _ hK hgram hconj hfg hspan
      hB hdeg hM ⟨h, hh, rfl⟩
  · exact hPX.2 hP D T j Y e o hY h2 Z u X p L0 ψ s t ⟨hgram, hfg, hspan⟩ hB hN hd hM
end SelfIntersectionVolumeEstimates.ImageNefG
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeLineBundleLe

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
namespace SelfIntersectionVolumeEstimates.VolUpG
theorem volume_line_bundle_le : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (abelian₂ t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) w abelian₂ → Real.log abelian₂ ≤ t → volL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict 8 Z (wtOf (T.Q.Dw j) u 0) t ≤ ENNReal.ofReal (Y.dg u Z * (Y.ht u Z + t)) := by
  intro hX hP D T j Y e o hG hE Z u n w abelian₂ t hGood hBir hNo hdg hShort hLam
  obtain ⟨k, _, X, _, p, L, A, hV, hN, hS, hA, hinj⟩ :=
    _root_.SelfIntersectionVolumeEstimates.ImageNefG.exists_nef_model_of_image hX hP D T j Y e o hG hE Z u n w abelian₂ t hGood hBir hNo hdg hShort hLam
  have hd : 0 < Module.finrank ℚ Y.d.c₂.F := Module.finrank_pos
  have h2 := GlobalTheory.T.countingVolume_le_selfIntersection_nefHermitianBundle k X p (dimFlag (T.Q.Dw j)) (Module.finrank ℚ Y.d.c₂.F) 8 L A
    (fun τ => (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t).encard)
    hP.q9 hV hN hS hd (by norm_num) hinj
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpos : (0 : ℝ) < (Module.finrank ℚ Y.d.c₂.F : ℝ) * ((dimFlag (T.Q.Dw j) : ℝ) + 1) := by positivity
  rw [div_le_iff₀ hpos]
  linarith [hA]
end SelfIntersectionVolumeEstimates.VolUpG
end
end
end
