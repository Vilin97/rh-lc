module

public import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
public import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcBasic
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthOneOrTwoCaseB
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthOneOrTwoCaseC
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeCaseC
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AlgebraMapMemInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
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
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeDescent
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeExistsLiftsAtScalarMul
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthTwoCaseDown
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcSingleTypeBound
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsExponentLeAndLiftsAtArc
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoeffXSubCPowSelf
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThinLetterType
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThinLetterTypeBis
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeConstantTerm

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_constant_term [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))  (X₂ : O) :
    LiftsAt W (arcOf b w S η up size) F c bb sol k₀
      (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂) (rr + (arcOf b w S η up size).σ PD.p) := by
  have hp11 : 11 ≤ PD.p := hB.1
  have hl5 : 5 ≤ PD.p := by omega
  have hSur : Formalism.MainNotions.LiftingTheory.Sur W F := hB.2.1.2.1
  have hthick : ∀ s' < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s' : ZMod n))).thick := by
    intro s' _
    show ((if up (c - (s' : ZMod n)) then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - (s' : ZMod n)))
      else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s' : ZMod n)))).thick) = true
    cases up (c - (s' : ZMod n)) <;> rfl
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hSur rr hkill hbb
  exact LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb
    (liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL
      hFL hO hOv hinj hArc hArcL hW₁ hW₂ hSur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr X₂)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeCaseD

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_case_d [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 22 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨t₂, X₂, f₂, ⟨r₂, hr₂, hr₂b⟩, hsplit, hf₂, hf₂0⟩ := arc_length_three_descent W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy
  obtain ⟨e, t₃, he, ⟨r₃, hr₃, hr₃b⟩, hl⟩ := arc_length_three_exists_liftsAt_scalar_mul W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy f₂ hf₂ hf₂0
  have hc := arc_length_three_constant_term W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy (t₃ * X₂)
  have hadd := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀
    (LiftsAt.liftsAt_mono W (arcOf b w S η up size) F c bb sol k₀ (le_max_right e (rr + (arcOf b w S η up size).σ PD.p)) hc)
    (LiftsAt.liftsAt_mono W (arcOf b w S η up size) F c bb sol k₀ (le_max_left e (rr + (arcOf b w S η up size).σ PD.p)) hl)
  have heq : algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE (t₃ * X₂) + algebraMap O W.EE t₃ * f₂ =
      algebraMap O W.EE t₃ * (algebraMap O W.EE t₂ * f) := by
    rw [hsplit, map_mul]; ring
  rw [heq] at hadd
  have hr₂0 : (0 : ℚ) ≤ r₂ := by
    have h0 := hO t₂; rw [hr₂] at h0; exact_mod_cast h0
  have hr₃0 : (0 : ℚ) ≤ r₃ := by
    have h0 := hO t₃; rw [hr₃] at h0; exact_mod_cast h0
  obtain ⟨N, hNge, hNlt⟩ : ∃ N : ℕ, r₃ + r₂ ≤ (N : ℚ) ∧ (N : ℚ) < r₃ + r₂ + 1 :=
    ⟨⌈r₃ + r₂⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩
  have hv : v (algebraMap O LL t₃ * algebraMap O LL t₂) = ((r₃ + r₂ : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_mul, hr₃, hr₂, WithTop.coe_add]
  have ht0 : algebraMap O LL t₃ * algebraMap O LL t₂ ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hv; exact WithTop.top_ne_coe hv
  have hvx : 0 ≤ v ((PD.p : LL) ^ N * (algebraMap O LL t₃ * algebraMap O LL t₂)⁻¹) := by
    rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_inv, hv, W.v_l]
    have hc' : (N • (1 : WithTop ℚ)) + -(((r₃ + r₂ : ℚ)) : WithTop ℚ) = (((N : ℚ) - (r₃ + r₂) : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
        nsmul_one, sub_eq_add_neg]
    rw [hc']
    exact_mod_cast (by linarith : (0 : ℚ) ≤ (N : ℚ) - (r₃ + r₂))
  obtain ⟨t', ht'⟩ := hOv _ hvx
  have ht'O : t' * (t₃ * t₂) = ((PD.p : ℕ) : O) ^ N := by
    apply hinj
    rw [map_mul, map_mul, ht', map_pow, map_natCast, inv_mul_cancel_right₀ ht0]
  have h2 := liftsAt_algebraMap_mul W (arcOf b w S η up size) F c bb sol k₀ t' hadd
  have heq2 : algebraMap O W.EE t' * (algebraMap O W.EE t₃ * (algebraMap O W.EE t₂ * f)) = lE W N * f := by
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_assoc t' t₃ t₂, ht'O, map_pow, map_natCast]
    rfl
  rw [heq2] at h2
  refine ⟨max e (rr + (arcOf b w S η up size).σ PD.p) + N, ?_, liftsAt_of_scaled_power W (arcOf b w S η up size) F c bb sol k₀ h2⟩
  have hp : (11 : ℝ) ≤ (PD.p : ℝ) := by exact_mod_cast hB.1
  have hh : (1 : ℝ) ≤ (((arcOf b w S η up size).h : ℕ) : ℝ) := by exact_mod_cast hOK.2.2.2.2.2.2.1
  have hlog : 0 ≤ Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ)) :=
    Real.logb_nonneg (by linarith) (by linarith)
  have key : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → z + 1 ≤ x + y + z + 1 := by
    intro x y z hx hy; linarith
  have hSg : Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ)) + 1 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
    unfold Formalism.MainNotions.N.Ln17.Sg
    exact key _ _ _ (by positivity) (by positivity)
  have hband : 0 ≤ bandI PD.p b w S η size Cb ∧ bandI PD.p b w S η size Cb ≤ 1 := by
    unfold bandI; split_ifs <;> norm_num
  have h2b : (2 + Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) * bandI PD.p b w S η size Cb ≤
      2 + Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ)) := by
    nlinarith [hband.1, hband.2]
  have hmax : (max (e : ℝ) ((rr : ℝ) + ((arcOf b w S η up size).σ PD.p : ℝ))) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size :=
    max_le he (by linarith)
  have hN : (N : ℝ) < (r₃ : ℝ) + r₂ + 1 := by exact_mod_cast hNlt
  have hη : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  push_cast
  nlinarith [hband.1, hband.2, hr₂b, hr₃b, hmax, h2b, hSg, hlog, hN]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsLiftsAtArcOfOfUpEqFalse

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem exists_liftsAt_arcOf_of_up_eq_false [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = false) (h2a : Formalism.MainNotions.LiftingTheory.AI W F (c - 1) + η + 1 ≤ size (c - 1)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 9 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨d₁, b₁, sol₁, hb₁, c₁, hlt, hpr⟩ := ArcLengthTwo.lift2a W F hB CR hWR hW₁ hW₂ hArc hO hOv hinj hP9
    hSec hHF hFL c hc bb sol hbb k₀ hk₀ hlen hdiff hOK hup h2a
  exact arc_length_two_reduction W F hB hW₁ hW₂ hArc hO hOv hinj hP2 hP9 hpi0 hSec hGL hFL c hc bb sol hbb k₀ f hf hlen hdiff
    hOK hσ hup b₁ sol₁ hb₁ c₁ hlt hpr

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcPropositionAlternative

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

private theorem sg_nonneg_of {x sg : ℝ} (h0 : 0 ≤ x) (h : x ≤ 3 * sg) : 0 ≤ sg := by linarith

private theorem bandI_nonneg (l b w S η : ℕ) (size : ZMod n → ℕ) (Cb : ℝ) :
    0 ≤ bandI l b w S η size Cb := by
  unfold bandI; split_ifs <;> norm_num

theorem arc_length_one_two_theorem [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 15 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨hOK, -, -, -, hσ⟩ := arcBasic W F hB
  have hSg : 0 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := sg_nonneg_of (Nat.cast_nonneg _) hσ
  have hbd : 0 ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) (bandI_nonneg _ _ _ _ _ _ _)
  cases hup : up c with
  | true =>
    by_cases h1b : PD.p * (size (c - 1) + S + η) + η < size c
    · obtain ⟨e, he, hl⟩ := arc_length_one_or_two_case_b W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb hlen hdiff hOK hσ hup h1b
      exact ⟨e, by linarith, hl⟩
    · obtain ⟨e, he, hl⟩ := arc_length_one_or_two_case_c W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb hlen hdiff hOK hσ hup h1b
      exact ⟨e, by linarith, hl⟩
  | false =>
    by_cases h2a : Formalism.MainNotions.LiftingTheory.AI W F (c - 1) + η + 1 ≤ size (c - 1)
    · obtain ⟨e, he, hl⟩ := exists_liftsAt_arcOf_of_up_eq_false W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb hlen hdiff hOK hσ hup h2a
      exact ⟨e, by linarith, hl⟩
    · obtain ⟨e, he, hl⟩ := arc_length_two_case_down W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb hlen hdiff hOK hσ hup (by omega)
      exact ⟨e, by linarith, hl⟩

theorem exists_liftsAt_of_arc_len_three_of_up [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 34 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨hOK, -, -, -, hσ⟩ := arcBasic W F hB
  have hSg : 0 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := sg_nonneg_of (Nat.cast_nonneg _) hσ
  have hbd : 0 ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) (bandI_nonneg _ _ _ _ _ _ _)
  by_cases hth : size (c - 2) < Formalism.MainNotions.LiftingTheory.AI W F (c - 2) + η + 2 * (arcOf b w S η up size).σ PD.p + 2
  · exact exists_exponent_le_and_liftsAt_arc W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm hlen hU hOK hσ hth
  · obtain ⟨e, he, hl⟩ := exists_liftsAt_le_of_len_three_of_up W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm hlen hU hOK hσ (by omega)
    exact ⟨e, by linarith, hl⟩

theorem arc_length_three_theorem [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 22 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨hOK, -, -, -, hσ⟩ := arcBasic W F hB
  have hSg : 0 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := sg_nonneg_of (Nat.cast_nonneg _) hσ
  have hbd : 0 ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) (bandI_nonneg _ _ _ _ _ _ _)
  by_cases hy : size (c - 1) < PD.p * (size (c - 2) + S + η)
  · exact arc_length_three_case_d W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy
  · obtain ⟨e, he, hl⟩ := arc_length_three_case_c W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ (by omega)
    exact ⟨e, by linarith, hl⟩

theorem arc_proposition_alternative [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hscope : (arcOf b w S η up size).len c ≤ 2 ∨ 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨hOK, -, hlen3, -, hσ⟩ := arcBasic W F hB
  have hSg : 0 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := sg_nonneg_of (Nat.cast_nonneg _) hσ
  have hbd : 0 ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) (bandI_nonneg _ _ _ _ _ _ _)
  have hSg1 : 1 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
    unfold Formalism.MainNotions.N.Ln17.Sg
    have h1 : (0 : ℝ) ≤ (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ ((w : ℝ) + S + η) / PD.p := by positivity
    have h3 : (0 : ℝ) ≤ Real.logb PD.p (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
      rcases Nat.eq_zero_or_pos (TruncatedSeriesCountingBounds.hB b w S η size) with h0 | hpos
      · simp [h0]
      · apply Real.logb_nonneg
        · have : (2 : ℝ) ≤ PD.p := by
            have h11 : 11 ≤ PD.p := hB.1
            exact_mod_cast (by omega : 2 ≤ PD.p)
          linarith
        · have : (1 : ℝ) ≤ (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) := by exact_mod_cast hpos
          linarith
    linarith
  have hl1 : 1 ≤ (arcOf b w S η up size).len c := (hOK.2.2.1 c hc).1
  have hl3 : (arcOf b w S η up size).len c ≤ 3 := hlen3 halt c hc
  rcases (show (arcOf b w S η up size).len c = 1 ∨ (arcOf b w S η up size).len c = 2 ∨ (arcOf b w S η up size).len c = 3 by omega) with h | h | h
  · obtain ⟨e, he, hl⟩ := arc_single_type_bound W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf (by
      intro s hs
      have : s = 0 := by omega
      subst this
      simp)
    exact ⟨e, by linarith, hl⟩
  · have hdiff : up (c - 1) ≠ up c := by
      have := (halt (c - 1)).1
      simp only [sub_add_cancel] at this
      exact fun h => this h.symm
    obtain ⟨e, he, hl⟩ := arc_length_one_two_theorem W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb h hdiff
    exact ⟨e, by linarith, hl⟩
  · have hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4 := by
      rcases hscope with h' | h'
      · omega
      · exact h'
    cases hU : up (c - 2) with
    | false =>
      obtain ⟨e, he, hl⟩ := arc_length_three_theorem W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm h hU
      exact ⟨e, by linarith, hl⟩
    | true =>
      obtain ⟨e, he, hl⟩ := exists_liftsAt_of_arc_len_three_of_up W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm h hU
      exact ⟨e, by linarith, hl⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
end
