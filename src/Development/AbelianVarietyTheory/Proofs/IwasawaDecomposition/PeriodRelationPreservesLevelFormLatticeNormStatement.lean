module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZOfSurjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevel
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Formalism.LocalToGlobal.Columns.NonDeg

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueIsCrd

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TieModel

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Forms

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
  (P : LevFam X.E X.K R.r Pr.vGs)

def frm (y : Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) :
    (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).Forms :=
  (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
    (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y)

theorem isFormOf_unique {V : Type} {y : V} {x x' : MtildeV W Ch sel mu P} (h : IsFormOf W Ch sel mu hX P x y)
    (h' : IsFormOf W Ch sel mu hX P x' y) : x = x' := by
  obtain ⟨F, hF, e, rfl⟩ := h
  obtain ⟨F', hF', e', rfl⟩ := h'
  have := ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)).injective (eq_of_heq (e.trans e'.symm))
  subst this
  rfl

end Forms

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)

end Cols

section Core

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

end Core

section Standard

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links



end Standard

end GlobalTheory.Mem.Top.Bl.TieModel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

theorem _root_.GlobalTheory.T.rowFormClassSum_principal_eq_card_mul_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P),
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  first | exact @GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev | exact GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev | (intros; apply GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivFormsTie

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder Matrix

namespace GlobalTheory.Mem.ColTie

section Mat

end Mat

section Gen

def StarCx {X : Fields} (σ : X.K →+* ℂ) : Prop := ∀ x, σ (star x) = starRingEnd ℂ (σ x)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

abbrev HPm : Matrix (Fin (dimP W Ch sel mu P hX)) (Fin (dimP W Ch sel mu P hX)) X.K :=
  (csdK W Ch sel mu hX).lvlH (actK W Ch sel mu hX) P.grp P.chr

theorem ipK_zOf (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
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

theorem ipLev_zOf (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipLev W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      Formalism.DivisionValues.hform (HPm W Ch sel mu P hX) x y := by
  have hP : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hP ?_
  rw [← GlobalTheory.T.rowFormClassSum_principal_eq_card_mul_level W Ch sel mu P hX, ipK_zOf]
  exact LiftForms.csum_lvlForm _ _ _ _ x y

end Gen

section Fam

variable {B : Base} {px : PreX B.toPre} (I : TC B px) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL))
  (tr : TrI B px) (t : TupU I U)

end Fam

section TC

attribute [local instance] starE

theorem sig_starCx (B : Base) : StarCx (X := B.fields) (sig B) := fun x => B.starLL_cx x

variable {B : Base} {px : PreX B.toPre} (I : TC B px)

end TC

end GlobalTheory.Mem.ColTie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRelationPreservesLevelFormLatticeNorm

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.R3.Rw.NormTie

section
open _root_.Formalism.L2.Col
variable {Y : Fields} {Pr : Primes Y} {R : Ranks} (W : Wts Y Pr.Word R) (Ch : Chars Y Pr R.m)
  (sel : HeightOneSpectrum (𝓞 Y.F) → HeightOneSpectrum (𝓞 Y.E)) {S : Set ℕ} (mu : Tup Y.F Y.E Y.K S)
  (P : Formalism.L2.Col.LevFam Y.E Y.K R.r Pr.vGs) (hX : Y.Ok)

theorem isFormOf_zOf (y) : IsFormOf W Ch sel mu hX P (ColTie.zOf W Ch sel mu P hX y) (TieModel.frm W Ch sel mu hX P y) :=
  ⟨(ColTie.resK W Ch sel mu hX).symm (ColTie.formK W Ch sel mu P hX y), ColTie.zOf_mem W Ch sel mu P hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩

end



theorem normAt_eq_norm_tie : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  intro X px I hX Xg tr a O _ φ s t e hcrd x
  have hs := GlobalTheory.Mem.ColTie.zOf_surjective X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX
  obtain ⟨y, rfl⟩ : ∃ y, (GlobalTheory.Mem.ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) = x := hs x
  have hF := isFormOf_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y
  obtain ⟨x', hx', hj⟩ := hcrd y
  have hx2 : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x' (TieModel.frm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) y) := hx'
  have hxx := TieModel.isFormOf_unique (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) hx2 hF
  subst hxx
  rw [← hj]
  have hmk := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX).2
    (InfinitePlace.mk X.B.embLL) (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)
  have hip : (Formalism.L2.Col.mtildeGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)).ip
      (Formalism.L2.Col.mtildeOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I))
      (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 (ColTie.zOf X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y).1 =
      Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y :=
    ColTie.ipLev_zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y
  have hin : inner ℂ (t.j y) (t.j y) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) :=
    t.forms.inner y y
  have hσ : ∀ z : X.B.fields.K, X.B.embLL (star z) = starRingEnd ℂ (X.B.embLL z) := ColTie.sig_starCx X.B
  have hn : ((‖t.j y‖ ^ 2 : ℝ) : ℂ) = X.B.embLL (Formalism.DivisionValues.hform (ColTie.HPm (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX) y y) := by
    rw [← hin, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [LinearEquiv.refl_apply, Formalism.L2.Col.GSD.ipAt_eq_ipEmb] at hmk
  rcases InfinitePlace.embedding_mk_eq X.B.embLL with he | he
  · rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ, hip] at hmk
    have h2 := Complex.ofReal_injective (hmk.trans hn.symm)
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · have hσ' : ∀ w : X.B.fields.K, (ComplexEmbedding.conjugate X.B.embLL) (star w) =
        starRingEnd ℂ ((ComplexEmbedding.conjugate X.B.embLL) w) := by
      intro w
      simp only [ComplexEmbedding.conjugate_coe_eq, hσ]
    rw [he, ← Formalism.L2.Col.GSD.map_ip _ _ _ hσ', hip, ComplexEmbedding.conjugate_coe_eq, ← hn, Complex.conj_ofReal] at hmk
    have h2 := Complex.ofReal_injective hmk
    exact (pow_left_inj₀ (Real.sqrt_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end GlobalTheory.Mem.R3.Rw.NormTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRelationPreservesLevelFormLatticeNormStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  first | exact @GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie | exact GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie | (intros; apply GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie <;> assumption)
end
end
