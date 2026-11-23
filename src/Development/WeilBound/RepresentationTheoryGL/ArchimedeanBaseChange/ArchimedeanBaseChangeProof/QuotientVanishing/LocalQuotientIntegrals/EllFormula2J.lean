module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteTopologyProdMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsQuotNormaliserIndicator
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AevalTranspose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCornerGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneAddOfSq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnormOfRealToRealLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImgEqOfInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogSizeNonneg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSdot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceAdelicGLCmField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceFiniteAdeleRingCmField
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ClassVanishOfSteps
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.IsCompactEntryBall
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.QuotVanishL

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralProdSubgroup

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotProduct

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂]
  [MeasurableMul₂ G₁] [MeasurableMul₂ G₂] {T₁ : Subgroup G₁} {T₂ : Subgroup G₂}
  {ν₁ : Measure T₁} [SFinite ν₁] {ν₂ : Measure T₂} [SFinite ν₂] {ν : Measure (T₁.prod T₂)}

def split (t : T₁.prod T₂) : T₁ × T₂ :=
  (⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩)

theorem measurable_split : Measurable (split : T₁.prod T₂ → T₁ × T₂) :=
  ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
    ((measurable_snd.comp measurable_subtype_coe).subtype_mk)

theorem lintegral_prod_subgroup (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : Measurable ρ) (g : G₁ × G₂) :
    ∫⁻ h : T₁.prod T₂, ρ ((h : G₁ × G₂) * g) ∂ν =
      ∫⁻ t₁ : T₁, ∫⁻ t₂ : T₂, ρ ((t₁ : G₁) * g.1, (t₂ : G₂) * g.2) ∂ν₂ ∂ν₁ := by
  have hm : Measurable fun p : T₁ × T₂ => ρ ((p.1 : G₁) * g.1, (p.2 : G₂) * g.2) :=
    hρ.comp ((((measurable_subtype_coe.comp measurable_fst).mul_const g.1)).prodMk
      ((measurable_subtype_coe.comp measurable_snd).mul_const g.2))
  rw [← lintegral_prod _ hm.aemeasurable, ← hν, lintegral_map hm measurable_split]
  rfl

theorem normaliser_fst (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₁ ν₁ fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₁ × T₂ => ρ (p.1, (p.2 : G₂)))
    (hρ.1.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))), fun g => ?_⟩
  have h := hρ.2 (g, 1)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  simpa using h

theorem normaliser_snd (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₂ ν₂ fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₂ × T₁ => ρ ((p.2 : G₁), p.1))
    (hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk measurable_fst)), fun g => ?_⟩
  have h := hρ.2 (1, g)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  rw [lintegral_lintegral_swap]
  · simpa using h
  · have hm : Measurable fun p : T₂ × T₁ => ρ ((p.2 : G₁), (p.1 : G₂) * g) :=
      hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk
        ((measurable_subtype_coe.comp measurable_fst).mul_const g))
    exact hm.aemeasurable

theorem normaliser_mul (hν : ν.map split = ν₁.prod ν₂) {ρ₁ : G₁ → ℝ≥0∞} {ρ₂ : G₂ → ℝ≥0∞}
    (h₁ : IsQuotNormaliser T₁ ν₁ ρ₁) (h₂ : IsQuotNormaliser T₂ ν₂ ρ₂) :
    IsQuotNormaliser (T₁.prod T₂) ν fun x => ρ₁ x.1 * ρ₂ x.2 := by
  have hm : Measurable fun x : G₁ × G₂ => ρ₁ x.1 * ρ₂ x.2 :=
    (h₁.1.comp measurable_fst).mul (h₂.1.comp measurable_snd)
  refine ⟨hm, fun g => ?_⟩
  rw [lintegral_prod_subgroup hν hm]
  have hc : ∀ t₁ : T₁, ∫⁻ t₂ : T₂, ρ₁ ((t₁ : G₁) * g.1) * ρ₂ ((t₂ : G₂) * g.2) ∂ν₂ =
      ρ₁ ((t₁ : G₁) * g.1) := fun t₁ => by
    have hm₂ : Measurable fun t₂ : T₂ => ρ₂ ((t₂ : G₂) * g.2) :=
      h₂.1.comp (measurable_subtype_coe.mul_const g.2)
    rw [lintegral_const_mul _ hm₂, h₂.2, mul_one]
  simp only [hc]
  exact h₁.2 g.1

end GlobalTheory.CompanionTheory.QuotProduct

namespace GlobalTheory.CompanionTheory.QuotProduct

theorem quotProd_holds : PositivityTheory.Rg.BcB.D4.QuotProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν₁ _ _ ν₂ _ _ ν _ _ F hF hν hinv hfib
  by_cases hex : ∃ ρ, IsQuotNormaliser (T₁.prod T₂) ν ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hν' : ν.map split = ν₁.prod ν₂ := hν
    have n₁ := normaliser_fst hν' hρ
    have n₂ := normaliser_snd hν' hρ
    have n := normaliser_mul hν' n₁ n₂
    set ρ₁ : G₁ → ℝ≥0∞ := fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂
    set ρ₂ : G₂ → ℝ≥0∞ := fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁
    rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hinv n]
    by_cases hi : Integrable (fun x : G₁ × G₂ => F x * (((ρ₁ x.1 * ρ₂ x.2).toReal : ℝ) : ℂ)) (μ₁.prod μ₂)
    · rw [integral_prod_symm _ hi]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x₂ => ?_)
      have hFx : Measurable fun x₁ => F (x₁, x₂) := hF.comp (measurable_id.prodMk measurable_const)
      have hinvx : ∀ h ∈ T₁, ∀ g, F (h * g, x₂) = F (g, x₂) := fun h hh g => by
        simpa using hinv (h, 1) (Subgroup.mem_prod.2 ⟨hh, T₂.one_mem⟩) (g, x₂)
      have hq := hfib x₂
      rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hFx hinvx n₁] at hq
      have : ∀ x₁, F (x₁, x₂) * (((ρ₁ x₁ * ρ₂ x₂).toReal : ℝ) : ℂ) =
          (F (x₁, x₂) * (((ρ₁ x₁).toReal : ℝ) : ℂ)) * (((ρ₂ x₂).toReal : ℝ) : ℂ) := fun x₁ => by
        rw [ENNReal.toReal_mul]; push_cast; ring
      simp only [this, Pi.zero_apply]
      rw [integral_mul_const, hq, zero_mul]
    · exact integral_undef hi
  · simp only [quotIntegral, dif_neg hex]

theorem quotProd_of_normEq : PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.D4.QuotProd :=
  fun _ => quotProd_holds

end GlobalTheory.CompanionTheory.QuotProduct

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjCentMul

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.ChiGamGlobal

theorem twConj_cent_mul {G : Type} [Group G] (θ : Monoid.End G) {t δ : G} (x : G) (ht : twConj θ t δ = δ) :
    twConj θ (t * x) δ = twConj θ x δ := by
  have h : t⁻¹ * δ * θ t = δ := ht
  calc twConj θ (t * x) δ = x⁻¹ * (t⁻¹ * δ * θ t) * θ x := by
        simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    _ = twConj θ x δ := by rw [h]; rfl

theorem logSize_nonneg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (g : GA E n) :
    0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)

theorem chiGam_of (hI : OnlyIsotropic) (hP : PosY) (hC : ChainSum) : ChiGam := by
  classical
  intro E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hI E n
  obtain ⟨C₂, h₂⟩ := hP E n
  refine ⟨max C₁ C₂, fun d m Wof a hiso huniq h0 hmeet hle hreg hdeg τ x hτ t ht => ?_⟩
  have hs : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by
    have := logSize_nonneg (twConj (thetaA E n) x (ratGL E n d))
    linarith
  have b₁ := (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hs).trans hτ
  have b₂ := (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hs).trans hτ
  have hconj : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) :=
    twConj_cent_mul _ x ht
  have hind := (hC m).1 _ (a t) (h₂ d m Wof hiso huniq h0 hmeet hle hreg τ x b₂)
  have hiff : t * x ∈ cutSet E n τ ↔
      ∀ e, sdot e (a t) ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e) := by
    rw [h₁ τ (t * x) d (by rw [hconj]; exact b₁)]
    constructor
    · intro h e
      have := h (Wof e) (hiso e).1 (hiso e).2
      rw [hdeg t ht x e] at this
      linarith
    · intro h W hW₁ hW₂
      obtain ⟨e, rfl, _⟩ := huniq W ⟨hW₁, hW₂⟩
      have := h e
      rw [hdeg t ht x e]
      linarith
  rw [hind]
  by_cases hx : t * x ∈ cutSet E n τ
  · have ha : a t ∈ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      hiff.1 hx
    rw [Set.indicator_of_mem ha, chiT, Set.indicator_of_mem hx]
    simp
  · have ha : a t ∉ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      fun h => hx (hiff.2 h)
    rw [Set.indicator_of_notMem ha, chiT, Set.indicator_of_notMem hx]
    simp

end GlobalTheory.CompanionTheory.ChiGamGlobal

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ClassVanish

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB.D1 GlobalTheory.CompanionTheory

theorem classVanish : ClassVanish :=
  classVanish_of_steps QuotNorm.integral_normaliser_eq (QuotProduct.quotProd_of_normEq QuotNorm.integral_normaliser_eq) chainSum
    RatDisc.ratDisc locVanish LocP.main LocFlagPf.locFlag degBdd KerTwFin.kerFin mahler SplitInf.splitAt NonEll.nonEllFlag
    SplitTwo.splitAt2 PairParam.pairParam (TorusCh.torusChar degAdelic)
    (ChiGamGlobal.chiGam_of onlyIsotropic (PosYGlobal.posY_of degSubmod degPairing) chainSum)
    (QuotStageInt.quotStage_of QuotNorm.integral_normaliser_eq) sizeBasic

theorem unfold : Unfold := UnfoldCut.unfold_of_mahler mahler

end PositivityTheory.Rg.BcB.CV
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EllFormula2J

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.D4

theorem classVanish2 : ClassVanish2 := classVanish2_of (GlobalTheory.CompanionTheory.SliceFubini.sliceTerm_of mahler) classVanish sizeBasic

theorem ellFormula2J : EllFormula2J := ellFormula2_of (GlobalTheory.CompanionTheory.TwUnfold.unfold2_of mahler) ellTerm classVanish2 sizeBasic

end PositivityTheory.Rg.BcB.CV
end
end
