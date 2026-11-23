module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegment

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL

theorem isL_map_tw_of_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  intro k _ _ _ _ _ 𝔪 x χ hχ h
  exact (h.tw χ hχ).of_equiv (x.twEquiv χ hχ)

end GlobalTheory.LocGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegmentStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isLanglandsClassification_twist_multisegment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  first | exact @GlobalTheory.LocGL.isL_map_tw_of_isL | exact GlobalTheory.LocGL.isL_map_tw_of_isL | (intros; apply GlobalTheory.LocGL.isL_map_tw_of_isL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompat

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WDListLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpZero (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (WD.lpZero (h := h)).lpTwist ξ hξ = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpTwist_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

theorem lpTwist_lpSum (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpSum_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpSum_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  rfl

theorem lpTwist_lpChar (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpChar_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpChar_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp only [WDRep.tensor_ρ, WDRep.twist_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left,
    LinearMap.smul_apply]

theorem lpChar_lpZero (x : WD h) : x.lpChar (WD.lpZero (h := h)) = WD.lpZero (h := h) := by
  induction x using WD.ind with
  | hP n a =>
  rw [WD.lpZero, WD.lpChar_mk]
  exact WD.sound ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem lpChar_lpSum (x a b : WD h) : x.lpChar (a.lpSum b) = (x.lpChar a).lpSum (x.lpChar b) := by
  induction x using WD.ind with
  | hP n c =>
  induction a using WD.ind with
  | hP m a =>
  induction b using WD.ind with
  | hP k b =>
  rw [WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]
  refine WD.sound ⟨TensorProduct.prodRight ℂ ℂ _ _ _, fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
  · induction v using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ)
    ((WD.charPol_natDegree _ σ).trans (WD.lpDim_zero h))

end GlobalTheory.WDListLaws


open GlobalTheory.WDListLaws in
open GlobalTheory.LocLanglands (sumList) in
theorem GlobalTheory.sumList_laws : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  intro E Ω _ _ _ _ _ A w h
  refine ⟨fun l l' hp => ?_, fun l ξ hξ => ?_, fun x y ξ hξ => ⟨lpTwist_lpSum x y ξ hξ, lpTwist_lpChar x y ξ hξ⟩,
    fun x l => ?_, fun l => ⟨?_, fun σ => ?_⟩⟩
  · induction hp with
    | nil => rfl
    | cons x _ ih =>
      show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
      rw [ih]
    | swap x y l =>
      show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
      rw [← WD.lpSum_assoc, WD.lpSum_comm y x, WD.lpSum_assoc]
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · induction l with
    | nil => exact lpTwist_lpZero ξ hξ
    | cons x l ih =>
      show (WD.lpSum x (sumList l)).lpTwist ξ hξ = WD.lpSum _ (sumList _)
      rw [lpTwist_lpSum, ih]
  · induction l with
    | nil => exact lpChar_lpZero x
    | cons y l ih =>
      show x.lpChar (WD.lpSum y (sumList l)) = WD.lpSum _ (sumList _)
      rw [lpChar_lpSum, ih]
  · induction l with
    | nil => exact WD.lpDim_zero h
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).lpDim = _
      rw [WD.lpDim_sum, ih, List.map_cons, List.sum_cons]
  · induction l with
    | nil => exact charPol_lpZero σ
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).charPol σ = _
      rw [WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompatStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weil_deligne_sum_twist_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  exact @GlobalTheory.sumList_laws
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RcTwOfSegments

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem rc_tw_of_segments {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {r rc : IrrGL (k := w.adicCompletion E) → WD h} (hL : IsLExt r rc)
    (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E))
    (hx : IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (hr : ∀ Δ ∈ l, r (Δ.first.tw χ hχ) = (r Δ.first).lpTwist (χ.comp a) (ha.smooth hχ)) :
    rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  obtain ⟨-, hs, ht, -⟩ := GlobalTheory.T.weil_deligne_sum_twist_compat E Ω A w h
  have h2 := GlobalTheory.T.isLanglandsClassification_twist_multisegment _ (l : Multiset (Segment (w.adicCompletion E))) x χ hχ hx
  rw [hL l x hx, hL (l.map fun Δ : Segment _ => Δ.tw χ hχ) (x.tw χ hχ) h2, segSum, segSum, hs, List.map_map, List.map_map]
  refine congrArg sumList (List.map_congr_left fun Δ hΔ => ?_)
  show ((r (Δ.first.tw χ hχ)).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) = WD.lpTwist _ _ _
  rw [(ht _ _ _ _).2, hr Δ hΔ, WD.lpTw, WD.lpTw, GlobalTheory.LocLanglands.ExtTwist.lpTwist_lpTwist_comm]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extTw :
    UpperTheory.Zero.LLC.ExtTw := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H hL
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  refine ⟨fun x s => ?_, fun x χ hχ hg => ?_⟩
  · obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
    obtain ⟨l, rfl⟩ := Quotient.exists_rep 𝔪
    have key := rc_tw_of_segments ha hL l x h𝔪 (absPow _ (s : ℂ)) (isSmoothChar_absPow _) (fun Δ _ => by
      have h1 := H.nu _ Δ.isCusp_first s
      rw [WD.lpTw] at h1
      refine h1.trans ?_
      congr 1
      exact (ha.absPow_comp s).symm)
    refine key.trans ?_
    rw [WD.lpTw]
    congr 1
    exact ha.absPow_comp s
  · obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
    obtain ⟨l, rfl⟩ := Quotient.exists_rep 𝔪
    have hg' := ((UpperTheory.Zero.LLC.goodSeg _).1 l x h𝔪).1 hg
    rw [lpChar_lpOfChar]
    exact rc_tw_of_segments ha hL l x h𝔪 χ hχ fun Δ hΔ => H.twist _ Δ.isCusp_first (hg' Δ hΔ) χ hχ

end
end
end
