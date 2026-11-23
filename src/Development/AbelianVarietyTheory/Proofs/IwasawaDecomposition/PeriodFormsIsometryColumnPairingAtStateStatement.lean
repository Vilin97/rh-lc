module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZOfSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetricStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainLevelFamilyExtension

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

noncomputable section

namespace GlobalTheory.Mem.ColTie

theorem map_pairV_one {E K ι : Type} [Field E] [Field K] [StarRing K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K)
    (lam : ι → DomWeight n) (σ : K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) (x y : VV K lam) :
    σ (pairV emb lam 1 x y) =
      pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map σ x.1)) (MvPolynomial.map σ y.1) := by
  have e : gramK emb (1 : Matrix (Fin n) (Fin n) E) = fun τ => (((1 : ι → GL (Fin n) K) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    funext τ
    rw [gramK, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  show σ (pairK lam (gramK emb 1) x y) = _
  rw [pairK_apply, e, pairP_eq_pairB, polyAction_one₂, GlobalTheory.PeriodOnStep.map_pairB, MvPolynomial.map_map,
    MvPolynomial.map_map]
  congr 2
  exact congrArg (fun f => MvPolynomial.map f (x : Pol K ι n)) (RingHom.ext fun a => hσ a)

end GlobalTheory.Mem.ColTie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumComplexRowFormColumnsLevelEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.CsumForm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

theorem ipK_zOf_eq (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipK W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      (csdK W Ch sel mu hX).csum (formK W Ch sel mu P hX x).1 (formK W Ch sel mu P hX y).1 := by
  have e : ∀ x, (fun c => (zOf W Ch sel mu P hX x).1 ((mtildeKGSD W Ch sel mu).outSec.rep c)) =
      ((formK W Ch sel mu P hX x).1 : _ → _) := by
    intro x
    funext c
    rw [zOf_val, ← GSD.resOf_apply _ (mtildeKOk W Ch sel mu hX) (mtildeKGSD W Ch sel mu).outSec]
    show (((resK W Ch sel mu hX) ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x))).1 : _ → _) c = _
    rw [LinearEquiv.apply_symm_apply]
  unfold ipK GSD.ip GSD.ipOf
  rw [e, e]

theorem ipLev_zOf_eq (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipLev W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      Formalism.DivisionValues.hform ((csdK W Ch sel mu hX).lvlH (actK W Ch sel mu hX) P.grp P.chr) x y := by
  have hP : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hP ?_
  rw [← ipK_eq_card_mul_ipLev W Ch sel mu P hX, ipK_zOf_eq]
  exact LiftForms.csum_lvlForm _ _ _ _ x y

end Gen

section TC

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hX : B.fields.Ok) (a : I.ι)

theorem cSum_toCx (x : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I))
    (x' : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) :
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x') =
      B.embLL (ipLev (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX x x') := by
  rw [Df.cSum_apply]
  unfold ipLev GSD.ip GSD.ipOf CSD.csum

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold Df.cTerm
  rw [map_mul, map_inv₀, map_natCast, GSD.wt_eq]
  congr 1
  exact (map_pairV_one _ _ (sig B) (fun x => B.starLL_cx x) _ _).symm

end TC

theorem cSum_toCx_rowForm : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  intro X px I hX Xg tr a y x hx
  obtain ⟨F, h, hF, rfl⟩ := hx
  have e1 : ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX F =
      ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y := eq_of_heq hF
  have e2 : (⟨F.1, h⟩ : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) =
      ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y := by
    apply Subtype.ext
    show F.1 = ((ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)).1
    rw [← e1, LinearEquiv.symm_apply_apply]
  rw [cSum_toCx, e2]
  exact congrArg X.B.embLL (ipLev_zOf_eq (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y)

end GlobalTheory.Mem.CsumForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumComplexRowFormColumnsLevelEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  first | exact @GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm | exact GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm | (intros; apply GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsIsometryColumnPairingAtState

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.EmtTw
attribute [local instance] GlobalTheory.Mem.Col2.starE


theorem inner_per_e {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (a : w.C.Tup)
    (y y' : Df.MtCx w.I a) : inner ℂ (P.q.per.e a y) (P.q.per.e a y') = Df.cSum w.I P.hX a y y' := by
  let jA := (P.q.t.tA true a).j
  have hF := (P.q.t.tA true a).forms
  let eS : (P.q.p.sA true a).A.T →ₗ[ℂ] Df.MtCx w.I a := (P.q.per.e a).symm.toLinearMap
  let j' := eS.comp jA
  have hspan : Submodule.span ℂ (Set.range j') = ⊤ := by
    have h0 : Submodule.span ℂ (Set.range jA) = ⊤ := by
      rw [← ColTie.span_single_eq]; exact hF.span
    have h1 : Set.range j' = eS '' Set.range jA := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h0, Submodule.map_top]
    exact LinearMap.range_eq_top.2 (P.q.per.e a).symm.surjective
  obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
  refine Df.inner_eq_of_norm_sq _ j' hspan k hk (P.q.per.e a).toLinearMap (Df.cSum w.I P.hX a) (fun m => ?_) y y'
  obtain ⟨x, hx, hjx⟩ := P.q.per.crd a m
  have hj' : j' m = Df.toCx w.I P.hX a x := by
    show (P.q.per.e a).symm (jA m) = _
    rw [show jA m = _ from hjx, LinearEquiv.symm_apply_apply]
  have he : (P.q.per.e a).toLinearMap (j' m) = jA m := by
    show (P.q.per.e a) ((P.q.per.e a).symm (jA m)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hL := GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr a m x hx
  have hI := hF.inner m m
  rw [he, hj', hL]
  calc ((‖jA m‖ ^ 2 : ℝ) : ℂ) = inner ℂ (jA m) (jA m) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
    _ = _ := hI

theorem eMtTw_isometry_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u (a : (w.D x.o.Z).what₂.Tup), a ≠ (w.D x.o.Z).what₂.mu0 → ∀ F G,
      inner ℂ ((w.D x.o.Z).eMtTw u a F) ((w.D x.o.Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G := by
  intro K B f T w _ _ _ P x _ u a _ F G
  change inner ℂ (P.q.e.eT u a F) (P.q.e.eT u a G) = _
  have key : ∀ F : (TC.per w.I w.l u a).Mt, Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F)) F := fun F => by
    have h := P.q.per.tw u a ((P.q.per.e a).symm (P.q.e.eT u a F))
    rw [LinearEquiv.apply_symm_apply] at h
    exact (congrArg (Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F))) ((P.q.e.eT u a).symm_apply_apply F)).mp h
  have h1 : ∀ F : (TC.per w.I w.l u a).Mt, P.q.e.eT u a F = P.q.per.e a ((P.q.per.e a).symm (P.q.e.eT u a F)) := fun F =>
    ((P.q.per.e a).apply_symm_apply _).symm
  rw [h1 F, h1 G, inner_per_e P a, GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u a F G _ _ (key F) (key G)]

end GlobalTheory.Mem.R3.Rw.EmtTw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsIsometryColumnPairingAtStateStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.periodForms_isometry_columnPairing_at_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u (a : (w.D x.o.Z).what₂.Tup), a ≠ (w.D x.o.Z).what₂.mu0 → ∀ F G,
      inner ℂ ((w.D x.o.Z).eMtTw u a F) ((w.D x.o.Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G := by
  first | exact @GlobalTheory.Mem.R3.Rw.EmtTw.eMtTw_isometry_state | exact GlobalTheory.Mem.R3.Rw.EmtTw.eMtTw_isometry_state | (intros; apply GlobalTheory.Mem.R3.Rw.EmtTw.eMtTw_isometry_state <;> assumption)
end
end
