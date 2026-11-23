module

public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Formalism.LocalToGlobal.Columns.GSetLemmas
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
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
public import Formalism.LocalToGlobal.Columns.Record
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Formalism.LocalToGlobal.Divisibility.RecBridgeTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationDatumOkBaseTuple
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst

-- Source module: Formalism.LocalToGlobal.NumberFieldFamilies.EvRowSurjective

section

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.G.ServJoint
open scoped ComplexOrder

section Row

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (h : (mtildeKGSD W Ch sel mu).Ok) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs)

def evRow0 : (Fin (V0C W Ch sel mu h Xg P).d → X.K) →ₗ[X.K] (mtildeKGSD W Ch sel mu).EqFun :=
  ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).symm.toLinearMap ∘ₗ (V0C W Ch sel mu h Xg P).E.mulVecLin

theorem evRow0_mem (x : Fin (V0C W Ch sel mu h Xg P).d → X.K) : evRow0 W Ch sel mu h Xg P x ∈ V0X W Ch sel mu Xg P := by
  have hx : (V0C W Ch sel mu h Xg P).E.mulVecLin x ∈
      (V0X W Ch sel mu Xg P).map ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).toLinearMap := by
    rw [invariantSubspace_coords_X]
    exact ⟨x, rfl⟩
  obtain ⟨φ, hφ, e⟩ := hx
  have : evRow0 W Ch sel mu h Xg P x = φ := by
    show ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).symm ((V0C W Ch sel mu h Xg P).E.mulVecLin x) = φ
    rw [← e]
    exact LinearEquiv.symm_apply_apply _ φ
  rw [this]
  exact hφ

def evRow : (Fin (V0C W Ch sel mu h Xg P).d → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P :=
  LinearMap.codRestrict _ (evRow0 W Ch sel mu h Xg P) (evRow0_mem W Ch sel mu h Xg P)

theorem evRow_res (x : Fin (V0C W Ch sel mu h Xg P).d → X.K) :
    (mtildeKGSD W Ch sel mu).res h (evRow W Ch sel mu h Xg P x).1 =
      (MtildeKCSD W Ch sel mu h).basis.equivFun.symm ((V0C W Ch sel mu h Xg P).E.mulVec x) := by
  exact ((mtildeKGSD W Ch sel mu).res h).apply_symm_apply _

theorem evRow_res_lvl (hX : X.Ok) {v0 : InfinitePlace X.K} (h0 : IsConjAt v0)
    (hpos : ((MtildeKCSD W Ch sel mu h).H.map v0.embedding).PosDef) (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (x : Fin (V0C W Ch sel mu h Xg P).d → X.K) :
    (mtildeKGSD W Ch sel mu).res h (evRow W Ch sel mu h Xg P x).1 =
      (MtildeKCSD W Ch sel mu h).basis.equivFun.symm
        (((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVec
          (((MtildeKCSD W Ch sel mu h).lvlPr (g0Act W Ch sel mu h) P.grp P.chr *
            (MtildeKCSD W Ch sel mu h).V0E (g0Act W Ch sel mu h) Xg P.grp P.chr).mulVec x)) := by
  rw [lvlE_lvlPr_V0E (MtildeKCSD W Ch sel mu h) (g0Act W Ch sel mu h) Xg P.grp P.chr h0 hpos (unipotentActionForms_good W Ch sel mu hX h) hXg x]
  exact evRow_res W Ch sel mu h Xg P x

end Row

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)

def evC (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) (t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup) :
    (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel t.1 Xg P :=
  evRow W Ch sel t.1 (mtildeKOk W Ch sel t.1 hX) Xg P

theorem evC_res_lvl {s : ℕ} (hOk : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.Ok s)
    (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3)
    (t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup)
    (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K) :
    (mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t F).1 =
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm
        ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
            (lvlIdem ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ)).mulVec
          ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F)) :=
  evRow_res_lvl W Ch sel t.1 _ Xg P hX hOk.conj ((hOk.what₂ t).hpos _) hOk.irr F

variable (σ₀ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok)
  (rd : ∀ t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup,
    (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlDim ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
      P.grp P.chr) → X.K) → Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ)
  (T0 : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup → Prop)

end Fam

end Formalism.L2.DIV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColRecCEvBijective

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev cstT (τ : Tup B.fields.F B.fields.E B.fields.K I.S) : LocCst B.fields (rowSG (B.primes X) I.sel τ) :=
  twCst I.Ch I.sel τ I.glob

abbrev idxT (τ : Tup B.fields.F B.fields.E B.fields.K I.S) :
    ChIdx B.fields (B.primes X) B.R (QE I.sel (τ : Chr B.fields.F B.fields.E B.fields.K)) :=
  twIdx I.Ch I.sel τ (cstT I τ) (B.R.m - 2)

variable {I}

theorem cstT_tup (ht : I.IsTw) (a : I.ι) : cstT I (I.tup a) = I.cst a := (ht.cst_eq a).symm

theorem idxT_tup (ht : I.IsTw) (a : I.ι) : idxT I (I.tup a) = I.idx a := (ht.idx_eq a).symm

theorem of_forall_ix (ht : I.IsTw) {U : Set I.ι}
    (p : ∀ τ : Tup B.fields.F B.fields.E B.fields.K I.S, LocCst B.fields (rowSG (B.primes X) I.sel τ) →
      ChIdx B.fields (B.primes X) B.R (QE I.sel (τ : Chr B.fields.F B.fields.E B.fields.K)) → Prop)
    (hp : ∀ a, p (I.tup a) (I.cst a) (I.idx a)) (t : TupU I U) : p t.1 (cstT I t.1) (idxT I t.1) := by
  rw [← tup_ixOf I t, cstT_tup ht, idxT_tup ht]
  exact hp _

theorem idxT_ok (h : I.Ok) (ht : I.IsTw) {U : Set I.ι} (t : TupU I U) :
    (idxT I t.1).Ok I.Ch I.sel t.1 (cstT I t.1) I.glob (B.R.m - 2) :=
  of_forall_ix ht (fun τ c L => L.Ok I.Ch I.sel τ c I.glob (B.R.m - 2)) h.idx_ok t

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)

def colRecC : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) where
  Pr := B.primes X
  Rk := B.R
  W := B.wts
  Ch := I.Ch
  sel := I.sel
  Sg := I.S
  hX := hX
  Lv := rPsymF (R := B.R) I.Ch
  Xg := Xg
  m2 := B.R.m - 2
  Gc := I.glob
  mu := fun t => t.1
  cst := fun t => cstT I t.1
  Li := fun t => idxT I t.1
  hL := fun t => idxT_ok h ht t
  hP := fun t => mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel t.1 hX _
  Mem := B.Word
  wd := fun u => u
  b := fun t _ => (idxT_ok h ht t).last_uniq.choose
  hY := fun t u => coupling_index_set_finite (Pr := B.primes X) I.sel t.1 (cstT I t.1) (idxT I t.1) u (B.R.m - 2) _
  Am := I.J.amb B χ
  hK := fun t u => of_forall_ix ht
    (fun τ c L => ∀ b hY, KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel τ c L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps)
    (fun a => (RcHyp.hyps_of_isTw I h hp l Z ht hJ χ hχ a u).2.2.2) t _ _
  hF := fun t u => of_forall_ix ht (fun τ _ L => ∀ j, (chF (Pr := B.primes X) B.wts I.sel τ L u j).Ok)
    (fun a => (RcHyp.hyps_of_isTw I h hp l Z ht hJ χ hχ a u).1) t
  hE := fun u => by
    have e := RcHyp.evaluationDatum_ok_baseTuple I u
    rw [I.trueColumn_tuple_trivial_eq_one] at e
    exact e
  ev := evC (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
    (rPsymF (R := B.R) I.Ch)

end GlobalTheory.Mem.R3.SelC

end
end
end
