module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModular
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeOfHighest
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSum
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DstInvContinuousOn
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModule
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesFirst

section

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMass

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}


open scoped Classical in
theorem lintegral_rmul_of_measurable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) (F : Mx k r → ℝ≥0∞)
    (hF : Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)))
    (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x)
    {g : Mx k r} (hg : g ∈ GG k r) :
    ∫⁻ x, F (Matrix.of x * g) ∂νq = ∫⁻ x, F (Matrix.of x) ∂νq := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ hF (fun s hs x hx => by
    rw [hval x hx]
    exact (hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx)) g hg
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => hval x hx)))
  exact (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm

theorem norm_sq_sqrt_scaled {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {t d : ℝ} (ht : 0 ≤ t)
    (hd : 0 ≤ d) (v : Wp) : ‖((Real.sqrt t * Real.sqrt d : ℝ) : ℂ) • v‖ ^ 2 = t * (d * ‖v‖ ^ 2) := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hd]
  ring


open scoped Classical in
theorem measurable_piecewise_mass {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (hφm : Measurable φ) (d : ℝ) (B : Mx k r → Wp) (hB : ContinuousOn B (GG k r)) :
    Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0)) := by
  classical
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hL : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) A :=
    continuousOn_pi.2 fun a => GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a
  have hLm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a)
      (fun _ => (0 : Fin (r + 1) → ℝ))) :=
    hL.measurable_piecewise continuousOn_const hAm
  have hBc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) A :=
    continuousOn_const.mul (hB.norm.pow 2)
  have hBm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ))) :=
    hBc.measurable_piecewise continuousOn_const hAm
  have heq : A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0) =
      A.indicator (fun x => ENNReal.ofReal (φ (A.piecewise
        (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) (fun _ => (0 : Fin (r + 1) → ℝ)) x)) *
        ENNReal.ofReal (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ)) x)) := by
    funext x
    by_cases hx : x ∈ A
    · simp [Set.piecewise, Set.indicator, hx]
    · simp [Set.piecewise, Set.indicator, hx]
  rw [heq]
  exact ((ENNReal.measurable_ofReal.comp (hφm.comp hLm)).mul (ENNReal.measurable_ofReal.comp hBm)).indicator hAm

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

end main

end GlobalTheory.LowTypeMass
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedMassHighestToLowestKTypeLargeGap

section

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMassGap

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset GlobalTheory.LowTypeMass
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

theorem lev_zero_of_wt_gap (hH : HypsG) (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Q : Mx k r}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hE : R.IsE Q E) (S : Submodule ℂ R.H) (hfin : FiniteDimensional ℂ S)
    (hst : PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S)
    (hmax : ∀ (μ : Fin (2 * r + k + 1) → ℝ) (v : R.H), v ∈ S → v ≠ 0 →
      PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) μ v →
      PI.UpqRep.CDom ε μ (Formalism.QuantumDeterminants.lowK ε mu))
    (w : R.smSub) (hwS : (w : R.H) ∈ S)
    (hw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) (w : R.H)) :
    Lev ε E mu 0 w := by
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hRS : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hR
  obtain ⟨-, hS2⟩ := GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r ε mu R hRS Q hQ S hfin hst
  obtain ⟨hw1, hw2⟩ := GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R hRS Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w hw
  have hMod := Gp91.GlobalTheory.isMod_smooth_of_isDS hH k r ε mu R hk hR Q E hQ hE
  refine GlobalTheory.lev_zero_of_kHighest _ _ _ E _ w hMod.1 hMod.2.1 ⟨hw1, ?_⟩ ?_
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he _ hwS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨hwS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

theorem weightedMass_bound_lowestType_largeGap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ)
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg) (ν : Fin (2 * r + k + 1) → ℤ) (hν0 : n1 ν ≤ q0)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞) (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hbd : ∀ (Q : Mx k r) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub),
      PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q →
      (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) →
      ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
        (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd)
    (w : (R ν).H)
    (hw : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w) :
    ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  classical
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  obtain ⟨Q, hQ, hw1, hwL⟩ := hw
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.smooth_gl_module hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hbd' := hbd Q E hQ hE
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) :=
    GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.1 k r lam u b bv ga h q0 R hNum hFam ν hν0
  have hDS := GlobalTheory.isDS_of_isDG hDG
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 _ _ _ hDS Q hQ
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r _ _ (R ν) hDS
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  have hsmS : ∀ S : Submodule ℂ (R ν).H, FiniteDimensional ℂ S →
      PI.UpqRep.IsKStableOn (PI.BesselPeriodGGP.eps48 k r) (fun g => (R ν).σ (Q⁻¹ * g * Q)) S → S ≤ (R ν).smSub :=
    fun S h1 h2 v hv => ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r _ _ (R ν) hDS Q hQ S h1 h2).1 v hv).2
  have hlenv : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) νq :=
    aemeasurable_pi_iff.2 hlen
  rcases eq_or_ne Bd ⊤ with rfl | hBd
  · exact le_top
  have hCB : ENNReal.ofReal Bd.toReal = Bd := ENNReal.ofReal_toReal hBd
  rw [← hCB]
  rw [← hCB] at hbd'
  have key := GlobalTheory.MomOne.lintegral_le_of_highest (m := νq) hD.2.2.1 _ (R ν).smSub hsmS
    (fun v x => ((Real.sqrt (φ (fun a => lenA k r z (Matrix.of x) a)) * Real.sqrt (dg ν) : ℝ) : ℂ) •
      lb ν ((R ν).σ (Matrix.of x) v))
    ?_ ?_ ?_ ?_ Bd.toReal ENNReal.toReal_nonneg ?_ w hwL hw1
  · simpa only [norm_sq_sqrt_scaled (hφ0 _) hdg.le] using key
  · intro v hv v' hv'
    filter_upwards [hG] with x hx
    simp only [Pi.add_apply]
    rw [map_add (f := _), hBeL.1.1 _ (hsm _ hx v hv) _ (hsm _ hx v' hv'), smul_add]
  · intro c v hv
    filter_upwards [hG] with x hx
    simp only [Pi.smul_apply]
    rw [map_smul, hBeL.1.2.1 c _ (hsm _ hx v hv), smul_comm]
  · intro v hv
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable ?_).smul (hmeas (lb ν) hBeL.1 v hv)
    exact (((hφm.comp_aemeasurable hlenv).sqrt).mul_const _).aestronglyMeasurable
  · intro g hg v hv
    obtain ⟨hgG, hgU⟩ := GlobalTheory.MomOne.conj_back hQ hg
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hBc := (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r _ _ (R ν) hDS Wp (lb ν) hBeL.1.1 hBeL.1.2.1
      hBeL.1.2.2.2 v hv).1
    have hF := measurable_piecewise_mass z hSide.1 hT φ hφm (dg ν) (fun x => lb ν ((R ν).σ x v)) hBc
    have := lintegral_rmul_of_measurable hSide
      (fun x => ENNReal.ofReal (φ (fun a => lenA k r z x a)) * ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ x v)‖ ^ 2))
      hF ?_ hgG
    · have e1 : ∀ x : Formalism.QuantumDeterminants.Mt k r, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
          (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2)) =
          ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
            ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) :=
        fun x => ENNReal.ofReal_mul (hφ0 _)
      simp only [e1]
      rw [← this]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      simp only [GlobalTheory.MomOne.lenA_mul_unitary z _ hgU, hmul _ hx _ hgG]
      rw [ENNReal.ofReal_mul (hφ0 _)]
    · intro s hs x hx
      have e := (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.2 s hs
      obtain ⟨h', hh, m, hmN, rfl⟩ := hs
      obtain ⟨u₀, hπ⟩ := hSide.2.2.1
      have hsG : h' * m ∈ GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hmN.1
      beta_reduce
      simp only [e]
      rw [hmul _ hsG _ hx, hBeL.1.2.2.1 h' hh m hmN _ (hsm _ hx v hv), norm_smul,
        Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm, one_mul, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h' hh]
  · intro S hfd hst hcd v hv hv1 hwt
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hvs : v ∈ (R ν).sm := hsmS S hfd hst hv
    have hLev := lev_zero_of_wt_gap hH.1 hk hDG hQ (hE ν hν0).1 S hfd hst hcd ⟨v, hvs⟩ hv hwt
    have hv1' : ‖(⟨v, hvs⟩ : (R ν).smSub)‖ = 1 := hv1
    exact hbd' ⟨v, hvs⟩ hLev hv1'

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem mass_low_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd :=
  fun hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw =>
    weightedMass_bound_lowestType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw

end main

end GlobalTheory.LowTypeMassGap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedMassHighestToLowestKTypeLargeGapStatement

section

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.weightedMass_highestToLowestKType_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  first | exact @GlobalTheory.LowTypeMassGap.mass_low_gap | exact GlobalTheory.LowTypeMassGap.mass_low_gap | (intros; apply GlobalTheory.LowTypeMassGap.mass_low_gap <;> assumption)
end
end
