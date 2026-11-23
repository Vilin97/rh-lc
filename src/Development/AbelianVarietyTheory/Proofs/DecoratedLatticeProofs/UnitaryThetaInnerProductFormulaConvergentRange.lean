module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMemStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityUnfoldingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSphericalModerateGrowthRealPointStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubledStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernelsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralEqSiegelEisensteinOfWeilRangeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariablesStatement
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightIoLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PeterssonLiftSmulMeasure
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityFlatSectionCuspForms

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem basicIdentity_flat : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → ∀ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ → ∀ A : CptF V, ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ f₂ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → GlobalTheory.Eis.BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂ :=
  fun hE hC D V hV a ha hI μ hμ _ _ hφ _ hθ _ m hm f₁ h₁ f₂ h₂ s hs =>
    GlobalTheory.T.doubling_basicIdentity_unfolding D V a ha μ hμ s hs _ (GlobalTheory.Eis.flat_mem hI hφ s) (GlobalTheory.T.siegelEisenstein_spherical_moderateGrowth_real_point hE D V hV a ha hI s.re hs) m hm f₁ f₂
      (GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2)
      (GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.2)
      (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2

end GlobalTheory.Core.Rk.IP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityFlatSectionCuspFormsStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.doublingBasicIdentity_flatSection_cuspForms : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → ∀ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ → ∀ A : CptF V, ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ f₂ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → GlobalTheory.Eis.BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂ := by
  first | exact @GlobalTheory.Core.Rk.IP.basicIdentity_flat | exact GlobalTheory.Core.Rk.IP.basicIdentity_flat | (intros; apply GlobalTheory.Core.Rk.IP.basicIdentity_flat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelNormSqModerateGrowthLarge

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem normSq_theta_modGrowth_big : GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation →
    ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t →
    ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ →
    (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧
      GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  intro hSWF hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat mH hmH Φ hΦ
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  obtain ⟨ha, ht, hb, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.Core.Rk.exists_doubled_weilDatum hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.DoublingTheta.thetaClause D ψ A B χA χB om omh hP.weil homh
  obtain ⟨hφ, hid⟩ := hTC Φ Φ hΦ.1 hΦ.1
  have hK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ Φ hΦ hΦ
  have h2ab : 2 * A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  obtain ⟨hint, hEV⟩ := GlobalTheory.T.thetaIntegral_eq_siegelEisenstein_of_weilRange hSWF D ψ A B (by omega) h2ab hw χB omh homh ν 𝓕 hP.covol mH hmH
    (delta A B Φ Φ) hφ

  have key : ∀ g h, thetaKO om g h Φ * conj (thetaKO om g h Φ) =
      ((χB (detA A g) : Circle) : ℂ) * thetaKO omh (io A (g, g)) h (delta A B Φ Φ) := by
    intro g h
    rw [(hid g g h).2]
    have e : ((χB (detA A g) : Circle) : ℂ) * (((χB (detA A g))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g h Φ * conj (thetaKO om g h Φ))) * e
  have knorm : ∀ g h, ‖thetaKO om g h Φ‖ ^ 2 = ‖thetaKO omh (io A (g, g)) h (delta A B Φ Φ)‖ := by
    intro g h
    have := congrArg norm (key g h)
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj, ← sq] at this
    rw [this]
  have hleft : ∀ g, LeftInv (GQ B) fun h => thetaKO om g h Φ := fun g γ hγ h => by
    show thetaKO om g (γ * h) Φ = thetaKO om g h Φ
    have e : ((g, γ * h) : GA D A × GA D B) = (1, γ) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hP.weil.om_aut 1 (one_mem _) _ hγ _ (hP.weil.om_pres _ _ hΦ.1)
  have hcont : ∀ g, Continuous fun h => thetaKO om g h Φ := fun g =>
    (hP.weil.om_cont Φ hΦ.1 0).comp (Continuous.prodMk_right g)
  have hL2 : ∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ := by
    intro g
    refine ⟨hleft g, ?_⟩
    have hm : AEStronglyMeasurable (descend (GQ B) fun h => thetaKO om g h Φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ B) mH) := by
      rw [aestronglyMeasurable_quotMeasure_iff_lift, (hleft g).lift_descend]
      exact (hcont g).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hint (io A (g, g))).norm.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend]
    exact (knorm g _).symm
  refine ⟨hL2, ?_⟩

  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ Φ) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hCt, hReg⟩ := hSEC D A (by omega) a hP.maj hI χB⁻¹ B.rank hHk (resEta_inv homh.resT) (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ Φ)) hmem
  obtain ⟨k, hk⟩ := hReg (sZero A B)
  have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
    have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, Complex.div_re]
    rw [e]
    have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast h2ab
    linarith
  have hF := hCt.1
  have hv0 := hF.eisValueAt hF.analyticOnNhd_flat hre
  have hv : GlobalTheory.Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 (delta A B Φ Φ)) (sZero A B)) (sZero A B)
      (ThetaMean.thetaMean omh mH (delta A B Φ Φ)) := by
    rw [hEV]; simpa only [flatH_self] using hv0
  obtain ⟨r, hr, -, -, C₁, N, hC₁⟩ := GlobalTheory.Eis.EisRegularAt.of_eisValueAt hk hv
  have hE : ∀ x, ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) x‖ ≤ C₁ * GlobalTheory.Grow.height (dblSp A) x ^ N := by
    intro x
    have e := hv.eisCont_eq
    have := hC₁ (sZero A B) (Metric.mem_ball_self hr) x
    rw [e] at this
    exact this
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := (norm_nonneg _).trans (hE 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (GlobalTheory.Grow.height_pos _ _) _)
  obtain ⟨C₂, c, hC₂⟩ := GlobalTheory.Grow.IoHeight.main D A
  have hvol := GlobalTheory.RallisIP.Model.vol_pos (B := B) mH
  have hpet : ∀ g, ‖petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ)‖ =
      (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖ := by
    intro g
    have e1 : petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ) =
        ((χB (detA A g) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g, g)) h (delta A B Φ Φ)) q ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g _
    rw [e1, norm_mul, Circle.norm_coe, one_mul, ← measure_smul_average, norm_smul, ThetaMean.thetaMean,
      Real.norm_of_nonneg measureReal_nonneg]
  refine ⟨(autMeasure B mH).real Set.univ * C₁ * C₂ ^ N, 2 * c * N, fun g => ?_⟩
  rw [hpet g]
  have h2 : GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N ≤ (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N := by
    refine pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ?_ N
    have := hC₂ g g
    rwa [← sq, ← pow_mul] at this
  calc (autMeasure B mH).real Set.univ * ‖ThetaMean.thetaMean omh mH (delta A B Φ Φ) (io A (g, g))‖
      ≤ (autMeasure B mH).real Set.univ * (C₁ * GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N) :=
        mul_le_mul_of_nonneg_left (hE _) hvol.le
    _ ≤ (autMeasure B mH).real Set.univ * (C₁ * (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁0) hvol.le
    _ = (autMeasure B mH).real Set.univ * C₁ * C₂ ^ N * GlobalTheory.Grow.height A g ^ (2 * c * N) := by
        rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.Core.Rk.IP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelNormSqModerateGrowthLargeStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.thetaKernel_normSq_moderateGrowth_large : GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧ GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  first | exact @GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big | exact GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big | (intros; apply GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRange

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem innerProduct_convergent : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : GlobalTheory.Core.Rk.IP.WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧ Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m ∧ petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
  intro hC hWS hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  obtain ⟨ha, ht, hb, hθ, hSig, hCart, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  obtain ⟨hφ, hid⟩ := hTC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1
  have hK := GlobalTheory.T.doublingVector_fockPair_isCompactFinite D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ₁ Φ₂ hΦ₁ hΦ₂
  have h2a : 2 * A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

  obtain ⟨-, hEis⟩ := GlobalTheory.T.thetaIntegral_eq_siegelEisenstein_of_weilRange hWS D ψ A B ha h2a hw χB omh homh ν 𝓕 hP.covol mH hmH (delta A B Φ₁ Φ₂) hφ
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ₁ Φ₂) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]

  have hf₁ := GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem D θ A cA hθ u₁ hu₁
  have hf₂ := GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem D θ A cA hθ u₂ hu₂
  have rd : ∀ u ∈ A0 θ A cA, GlobalTheory.Grow.RapidDec A u := fun u hu =>
    GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (mem_cuspForms.1 hu).1.1 (mem_cuspForms.1 hu).1.2

  have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
    have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, Complex.div_re]
    rw [e]
    have : (A.rank : ℝ) < t := by exact_mod_cast hat
    have hb' : (B.rank : ℝ) = A.rank + t := by exact_mod_cast hb
    rw [hb']; linarith
  have hBI := GlobalTheory.T.doublingBasicIdentity_flatSection_cuspForms hSEC hC D A (by omega) a hP.maj hI χB⁻¹ hHk (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)) hmem θ hθ cA m hm _ hf₁ _ hf₂ (sZero A B) hre
  simp only [flatH_self] at hBI
  obtain ⟨-, hZc, hZe⟩ := hBI

  have hpt : ∀ g, swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) *
      conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) =
      wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g := by
    intro g
    have e1 : swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) = wcoef om ν 𝓕 Φ₁ Φ₂ g :=
      (hCC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1).2 g
    have e2 : conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) = rcoef m u₁ u₂ g := by
      simp only [GlobalTheory.Eis.petCoef, rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend]
      rw [← integral_conj]
      congr 1
      ext x
      simp
    rw [e1, e2]
  have hInt : Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m := by
    have e : (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) = fun g =>
        swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) *
          starRingEnd ℂ (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) :=
      funext fun g => (hpt g).symm
    rw [e]
    exact hZc
  have hZ : GlobalTheory.Eis.dblInt A χB⁻¹ m (GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)))
      (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) = ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
    rw [hZe]
    unfold zetaH pairInt
    exact integral_congr_ae (.of_forall fun g => hpt g)

  have hKer : ∀ Φ, IsFockVec ψ θ A B sA sB Φ →
      Continuous (Function.uncurry fun g h => thetaKO om g h Φ) ∧
      (∀ γ ∈ GQ A, ∀ g h, thetaKO om (γ * g) h Φ = thetaKO om g h Φ) ∧
      (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧
      (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ) ∧
      ∀ h, GlobalTheory.Grow.ModGrowth A fun g => thetaKO om g h Φ := by
    intro Φ hΦ
    obtain ⟨hL2, hMG⟩ := GlobalTheory.T.thetaKernel_normSq_moderateGrowth_large hWS hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat mH hmH Φ hΦ
    refine ⟨hP.weil.om_cont Φ hΦ.1 0, fun γ hγ g h => ?_, hL2, hMG, fun h => ?_⟩
    · have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hP.weil.om_aut γ hγ 1 (one_mem _) _ (hP.weil.om_pres _ _ hΦ.1)
    · obtain ⟨C, N, hCN⟩ := GlobalTheory.T.theta_kernel_moderate_growth_both_variables D ψ A B χA χB om hP.weil Φ hΦ.1
      refine ⟨C * GlobalTheory.Grow.height B h ^ N, N, fun g => (hCN g h).trans (le_of_eq ?_)⟩
      rw [mul_pow]; ring
  obtain ⟨i₁, i₂, l₁, l₂, hss⟩ := GlobalTheory.T.seesaw_fubini_two_lifts_moderate_growth_kernels D A B m mH hm hmH (fun g h => thetaKO om g h Φ₁)
    (fun g h => thetaKO om g h Φ₂) (fun K hK => by
      rcases hK with rfl | rfl
      exacts [hKer Φ₁ hΦ₁, hKer Φ₂ hΦ₂]) u₁ u₂ (rd u₁ hu₁) (rd u₂ hu₂)
  refine ⟨⟨i₁, l₁⟩, ⟨i₂, l₂⟩, hInt, ?_⟩
  rw [← hZ, ← hEis]

  have key : ∀ g₁ g₂ h, thetaKO om g₁ h Φ₁ * conj (thetaKO om g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) * thetaKO omh (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂) := by
    intro g₁ g₂ h
    rw [(hid g₁ g₂ h).2]
    have e : ((χB (detA A g₂) : Circle) : ℂ) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g₁ h Φ₁ * conj (thetaKO om g₂ h Φ₂))) * e
  have hpet : ∀ g₁ g₂, petersson B mH (fun h => thetaKO om g₁ h Φ₁) (fun h => thetaKO om g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) *
        ((volQ B mH : ℂ) * GlobalTheory.ThetaMean.thetaMean omh mH (delta A B Φ₁ Φ₂) (io A (g₁, g₂))) := by
    intro g₁ g₂
    have e1 : petersson B mH (fun h => thetaKO om g₁ h Φ₁) (fun h => thetaKO om g₂ h Φ₂) =
        ((χB (detA A g₂) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂)) q
            ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g₁ g₂ _
    rw [e1, ← measure_smul_average, GlobalTheory.ThetaMean.thetaMean, Complex.real_smul]
    rfl
  have hss' : petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = _ := hss
  rw [hss', GlobalTheory.Eis.dblInt, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun q => ?_)
  simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, hpet, MonoidHom.inv_apply, Circle.coe_inv, inv_inv,
    RCLike.conj_conj]
  ring

end GlobalTheory.Core.Rk.IP
end
end
