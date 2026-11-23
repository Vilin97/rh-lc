module

public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.HerGenC
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaCutFTendsto
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliWordProductDecayBoundUniform
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_PtwCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectorsStatement
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorCutoffEqAndVanishStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCutoffLocality

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem beta_fold_cut_eq_beta_fold_of_cut : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (δ ε ε₁ : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → 0 < ε₁ → ε₁ < δ * ε → B.CkOn ⊤ (B.GV P.k P.r) F → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ F ε₁)) w) (D.cutF p.T.base χ F ε) = B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) (F) w) (D.cutF p.T.base χ F ε) := by
  intro Wp Wq _ _ _ _ _ _ P p s w χ δ ε ε₁ F hχ hδ hε hε₁ hlt hF
  unfold B.beta betaBig
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q = 0
  · simp only [hq, Complex.ofReal_zero, zero_mul]
  obtain ⟨hgG, -⟩ := Formalism.FourierDecayAlt.P.CutBP.bigCell_pos p q hq
  by_cases hG : Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) < δ * ε
  · have h0 : B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) = 0 := by
      rw [Formalism.FourierDecayAlt.P.CutBP.jf_congr_level p.T.base (Y := fun _ => 0) hgG (fun x _ hGx => by
        unfold D.cutF
        rw [hGx, hδ _ ((div_lt_iff₀ hε).2 hG)]
        simp)]
      unfold B.JF besselJ
      simp
    have h1 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    simp only [h0, h1, inner_zero_left]
  · have hge : ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) :=
      lt_of_lt_of_le hlt (not_lt.1 hG)
    have hU : IsOpen {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
      isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
    have he : ∀ x ∈ {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r,
        D.cutF p.T.base χ F ε₁ x = F x := by
      intro x hx
      unfold D.cutF
      rw [hχ.2.2 _ ((one_le_div hε₁).2 (le_of_lt hx.1))]
      simp
    have hcut := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε₁
    have hlev : ∀ x ∈ B.GV P.k P.r, Gf P.k P.r p.T.base.z p.T.base.z' x =
        Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) →
        x ∈ {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r :=
      fun x hx hGx => ⟨by show ε₁ < _; rw [hGx]; exact hge, hx⟩
    have key := Formalism.FourierDecayAlt.P.CutBP.jf_congr_level p.T.base hgG (fun x hx hGx =>
      Formalism.FourierDecayAlt.P.CutBP.fold_congr_open s hU hcut hF he w x (hlev x hx hGx))
    exact congrArg (fun A => (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
        (B.hsVec A)) key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCutoffLocalityStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_cutoff_locality : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (δ ε ε₁ : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → 0 < ε₁ → ε₁ < δ * ε → B.CkOn ⊤ (B.GV P.k P.r) F → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ F ε₁)) w) (D.cutF p.T.base χ F ε) = B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) (F) w) (D.cutF p.T.base χ F ε) := by
  first | exact @GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut | exact GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut | (intros; apply GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemLpAndTendstoIntegralInnerOfEventuallyEq

section

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem memLp_and_tendsto_integral_inner_of_eventually_eq : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ℝ → X → E) (u : X → E) (h : X → ℝ), Integrable h μ → (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (a ε) μ) → (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ, ‖a ε x‖ ^ 2 ≤ h x) → (∀ᵐ x ∂μ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε x = u x) → MemLp u 2 μ ∧ Tendsto (fun ε : ℝ => ∫ x, inner ℂ (a ε x) (u x) ∂μ) (𝓝[>] 0) (𝓝 (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ))) := by
  intro X _ μ E _ _ a u h hh hm hb he

  obtain ⟨s, hs⟩ := (𝓝[>] (0 : ℝ)).exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.eventually (hm.and hb))
  have hs' : Tendsto (fun n => s (n + N)) atTop (𝓝[>] (0 : ℝ)) :=
    hs.comp (tendsto_add_atTop_nat N)
  have hev : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, a (s (n + N)) x = u x := by
    filter_upwards [he] with x hx
    exact hs'.eventually hx
  have hu : AEStronglyMeasurable u μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => a (s (n + N)))
      (fun n => (hN (n + N) (Nat.le_add_left _ _)).1) ?_
    filter_upwards [hev] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun n hn => hn.symm)
  have hub : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ h x := by
    have h1 : ∀ᵐ x ∂μ, ∀ n, ‖a (s (n + N)) x‖ ^ 2 ≤ h x :=
      ae_all_iff.2 fun n => (hN (n + N) (Nat.le_add_left _ _)).2
    filter_upwards [hev, h1] with x hx h1x
    obtain ⟨n, hn⟩ := hx.exists
    rw [← hn]; exact h1x n
  refine ⟨?_, ?_⟩
  · rw [memLp_two_iff_integrable_sq_norm hu]
    refine hh.mono' (hu.norm.pow 2) ?_
    filter_upwards [hub] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hx
  · have key : (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ)) = ∫ x, inner ℂ (u x) (u x) ∂μ := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [key]
    refine tendsto_integral_filter_of_dominated_convergence h ?_ ?_ hh ?_
    · filter_upwards [hm] with ε hε
      exact hε.inner hu
    · filter_upwards [hb] with ε hε
      filter_upwards [hε, hub] with x h1 h2
      have := norm_inner_le_norm (𝕜 := ℂ) (a ε x) (u x)
      nlinarith [sq_nonneg (‖a ε x‖ - ‖u x‖)]
    · filter_upwards [he] with x hx
      exact tendsto_const_nhds.congr' (hx.mono fun ε hε => by simp only [hε])

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellIntegralTopDensityEqLevelZero

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem threshold_le_cut (k r N : ℕ) :
    B.AB k r ≤ 3 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  unfold B.AB
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set D : ℝ := 2 * (r : ℝ) + k + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have h1 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ D * D :=
    mul_le_mul (by rw [hD]; linarith) (by rw [hD]; linarith) (by linarith) (by linarith)
  have h2 : D * D ≤ D ^ 3 := by nlinarith [mul_nonneg (mul_self_nonneg D) (sub_nonneg.2 hD1)]
  have h3 : 1 ≤ D ^ 3 := one_le_pow₀ hD1
  have h4 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have h5 : 0 ≤ (N : ℝ) * D ^ 2 := by positivity
  have h6 : (N : ℝ) * D ^ 2 + D ^ 3 ≤ ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * D ^ 2 + D ^ 3) :=
    le_mul_of_one_le_left (by linarith) h4
  nlinarith

theorem integral_topDensity_eq_levelZero : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c) → ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) = (p.RR f 0 w [] []).re := by
  intro hXi hA Cb
  obtain ⟨Cc, hCc⟩ := GlobalTheory.T.levelZeroPairing_eq_integral_inner_topVectors hA Cb
  refine ⟨max Cc 3, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hDD hχ hf hCC hthr hw hN hdom
  obtain ⟨-, h, hint, hb⟩ := hdom
  have hX : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by positivity
  have hthr1 : Cc * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    refine le_trans ?_ hthr
    rw [mul_assoc Cc, mul_assoc (max Cc 3)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have hAB : B.AB P.k P.r ≤ A := by
    refine le_trans (threshold_le_cut P.k P.r N) (le_trans ?_ hthr)
    rw [mul_assoc (3 : ℝ), mul_assoc (max Cc 3)]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hX
  have hpol := hCc Wp Wq P p f χ A N w hDD hχ hf hCC hthr1 hw hN
  obtain ⟨δ, hδ, hδχ⟩ := hχ.2.1
  have hcut := fun (ε : ℝ) (hε : 0 < ε) (c : Fin (P.r + 1) → ℂ) =>
    GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hDD hw hχ hδχ hε hf
  set X := List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) f w with hXdef
  have hXCC : B.InCC A 5 X := by
    obtain ⟨K, -, hK⟩ := GlobalTheory.capelli_fold_ccle P.k P.r Wp Wq (M.sgn P p.l0) w 5
    obtain ⟨c, hc⟩ := hCC (5 + List.length w * (2 * P.r + P.k + 1))
    exact ⟨K * c, hK A c f hf hc⟩
  have hlimL := GlobalTheory.beta_cutF_tendsto hXi P.k P.r Wp Wq p.T.base χ A X f hχ hAB hXCC (hCC 5)
  have hlimR := (GlobalTheory.memLp_and_tendsto_integral_inner_of_eventually_eq (Fin (P.r + 1) → ℂ) volume _
    (fun ε => tv p (D.cutF p.T.base χ f ε) w) (tv p f w) h hint
    (Eventually.of_forall fun ε => GlobalTheory.T.aestronglyMeasurable_topVector_smoothCoefficient Wp Wq P p Cb _ w hDD hw
      (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε))
    (by
      filter_upwards [hb] with ε hε
      filter_upwards [hε] with c hc
      rw [Ew_eq_norm_tv_sq] at hc
      exact le_trans (le_abs_self _) hc)
    (Eventually.of_forall fun c => by
      by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
      · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
        exact (hcut ε hε.1 c).1 hε.2
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : 0 < ε := hε
        have hG' := not_lt.1 hG
        rw [(hcut ε hε' c).2.2 hG', (hcut ε hε' c).2.1 (lt_of_le_of_lt hG' (mul_pos hδ hε'))])).2
  have heq : (fun ε : ℝ => B.beta p.T.base X (D.cutF p.T.base χ f ε)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε) w c) (tv p f w c) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hδε : 0 < δ * ε := mul_pos hδ hε'
    have h1 : 0 < δ * ε / 2 := by linarith
    have h2 : δ * ε / 2 < δ * ε := by linarith
    rw [hXdef, ← GlobalTheory.T.levelZeroPairing_cutoff_locality Wp Wq P p (M.sgn P p.l0) w χ δ ε (δ * ε / 2) f hχ hδχ hε' h1 h2 hf,
      hpol _ _ h1 hε']
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    by_cases hG : TBB.Gp p (TBB.bigPt P.r c) < δ * ε
    · simp only [(hcut ε hε' c).2.1 hG, inner_zero_left]
    · simp only [(hcut _ h1 c).1 (lt_of_lt_of_le h2 (not_lt.1 hG))]
  have hfin := tendsto_nhds_unique (hlimL.congr' heq) hlimR
  have hRR : p.RR f 0 w [] [] = B.beta p.T.base X f := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hf (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw)]
    rfl
  rw [hRR, hfin, Complex.ofReal_re]
  exact integral_congr_ae (Eventually.of_forall fun c => Ew_eq_norm_tv_sq Wp Wq P p f w c)

end GlobalTheory.TopVec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellIntegralTopDensityEqLevelZeroStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.bigCell_integral_topDensity_eq_levelZero : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c) → ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) = (p.RR f 0 w [] []).re := by
  first | exact @GlobalTheory.TopVec.integral_topDensity_eq_levelZero | exact GlobalTheory.TopVec.integral_topDensity_eq_levelZero | (intros; apply GlobalTheory.TopVec.integral_topDensity_eq_levelZero <;> assumption)
end
end
