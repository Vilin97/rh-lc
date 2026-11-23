module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.LatticeCountingTheorem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRat
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
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeStepOfSiegelWeil

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRatStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.unitaryAutomorphicCounting_of_compactDualVolumeRatio : GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  first | exact @GlobalTheory.CountFinal.countingTheorem_of_volumeStep | exact GlobalTheory.CountFinal.countingTheorem_of_volumeStep | (intros; apply GlobalTheory.CountFinal.countingTheorem_of_volumeStep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSqStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.ncard_primesOver_eq_finrank_of_unramified_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) → (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  first | exact @GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq | exact GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq | (intros; apply GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundled

section

@[expose] public section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CountBridge

theorem fdegOf_eq_of_isFdeg {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (μ : Measure (Formalism.REAL.UJ ε))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (hd : IsFdeg μ σ d) (w : H) (hw : ‖w‖ = 1) :
    fdegOf μ σ w = d := by
  obtain ⟨hpos, h⟩ := hd
  have h2 := (h w w w w).2
  have h3 : (fun g => coefOn (ε := ε) σ w w g * star (coefOn σ w w g)) =
      fun g => (((‖coefOn (ε := ε) σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h3, integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hw] at h2
  have h4 : ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂μ = 1 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  unfold fdegOf
  rw [h4, hw]
  simp

theorem le_exp_of_log_le {x y : ℝ} (h : Real.log x ≤ y) : x ≤ Real.exp y :=
  (Real.le_exp_log x).trans (Real.exp_le_exp.mpr h)

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  apply Real.one_le_rpow
  · have h : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (discr_ne_zero I.E)
    exact_mod_cast h
  · positivity

theorem count_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  intro hT A
  obtain ⟨n₀, hn₀⟩ := hT A
  refine ⟨n₀, max 0 (8 * 10 ^ 14 * (A + 4)), le_max_left _ _, ?_⟩
  intro n₁ hn₁ C hC I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h
    ⟨hn, ⟨p, q, hpq, hq⟩, hb, hrd, hHC, hlam, hadm, hg, hgb, hpr, hg₀, hsplit⟩
    ⟨hDS, hlow, htens, hhaar, hfund, hR, hRe⟩ hgap hh hf hbb
  let B : RowsAut :=
    { I := I, μf := μf, haar := hhaar, fund := fund, fund_spec := hfund, lam := lam, H := H, σ := σ,
      w := w, Hs := Hs, σs := σs, tens := tens, tens_spec := htens, R := R, R_spec := hR, g := g,
      g₀ := g₀, e := e, e_adm := hadm, Re := Re, Re_spec := hRe }
  have hfd : ∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) := by
    intro v
    obtain ⟨_, hnt, hU, hirr, hsq, -⟩ := hDS v
    obtain ⟨d, hd⟩ := GlobalTheory.schur_orthogonality_unitary I.n (I.ε v) (H v) (σ v) hU hirr hsq
    rw [fdegOf_eq_of_isFdeg _ _ d hd _ (hlow v).1]
    exact hd
  have hlog : 0 ≤ Real.log (b * I.rd) := by
    apply Real.log_nonneg
    have := one_le_rd I
    nlinarith
  have hC' : 8 * 10 ^ 14 * (A + 4) ≤ C := (le_max_right _ _).trans hC
  have hH : GlobalTheory.Count.CountHyp B A n₀ (fun v => fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) p q b := by
    refine ⟨fun v => ⟨hHC v, hDS v, hlow v, hfd v⟩, hpq, le_trans hn₁ hn, hq, le_exp_of_log_le hrd, hf, hb,
      le_exp_of_log_le hbb, hlam, hg, hgb, hpr, hg₀, GlobalTheory.T.ncard_primesOver_eq_finrank_of_unramified_split I.E g₀ hpr hsplit, ?_⟩
    intro v a a' haa
    refine le_trans ?_ (hgap v a a' haa)
    refine le_trans ?_ hh
    show 8 * 10 ^ 14 * (A + 4) * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ _
    gcongr
  have hres := (hn₀ B _ p q b hH).2
  have he : -(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) =
      -(1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) := by ring
  rw [he]
  exact hres

end GlobalTheory.CountBridge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundledStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.unitaryAutomorphicCounting_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  first | exact @GlobalTheory.CountBridge.count_unbundled | exact GlobalTheory.CountBridge.count_unbundled | (intros; apply GlobalTheory.CountBridge.count_unbundled <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTypedOfVolumeStep

section

@[expose] public section

open Formalism.MainNotions.PlaceDegreeData

namespace GlobalTheory.CountBridge

theorem count_typed_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀,
      ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.PlaceDegreeData.PointsLemma D n₁ A C (1 / 16) (1 / 16) := by
  intro hV A
  obtain ⟨n₀, C₀, hC₀, hcount⟩ := GlobalTheory.T.unitaryAutomorphicCounting_unbundled (GlobalTheory.T.unitaryAutomorphicCounting_of_compactDualVolumeRatio hV) A
  refine ⟨n₀, C₀, hC₀, fun n₁ hn₁ C hC _D => ?_⟩
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h hSet hData
  exact hcount n₁ hn₁ C hC I b lam g g₀ e H σ w Hs σs tens μf fund R Re h hSet hData

end GlobalTheory.CountBridge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountConstantsOfSiegelWeil

section

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.S MeasureTheory

namespace GlobalTheory.CountConstants

theorem count_constants_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∃ (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants) (cIc : ℝ),
      (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) ∧ 0 < cIc ∧
      (∀ {eps : ℝ} (Fm : FamP eps), cIc ≤ (c30 Fm.cOut).c) ∧
      ∀ (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop) {eps : ℝ} (Fm : FamP eps),
        CountE.CountAllPointsClass P Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb := by
  intro hSW
  have H := GlobalTheory.CountBridge.count_typed_of_volumeStep (GlobalTheory.GaussMean.volumeStep_of_siegelWeil hSW)
  choose n₀ C₀ hC₀ HC using H
  let Af : List ℝ → ℝ := fun l => 2 * (l.getD 6 0 + 1)
  refine ⟨fun l => ⟨0, n₀ (Af l), Af l, 0, C₀ (Af l), 1 / 16, 1 / 16⟩, 1 / 16,
    fun Fm => ⟨hC₀ _, le_refl _⟩, by norm_num, fun Fm => le_refl _, fun P {_} Fm => ⟨by norm_num, by norm_num, ?_⟩⟩
  intro x i
  exact CountE.count_class_of_count P (HC _ _ le_rfl _ le_rfl _)

end GlobalTheory.CountConstants
end
end
