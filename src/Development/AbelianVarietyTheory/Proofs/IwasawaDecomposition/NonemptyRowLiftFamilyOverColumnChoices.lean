module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsAllTuplesCoordinateLawsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLiftReadingDefiniteFormCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegShaOK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapMemSpanImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFactorisationScalarReferenceTupleEqOne

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodMapFormsEquivRowLiftFormsUpperLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.PerId
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_crd_equiv (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ}
    {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) :
    ∃ e : Df.MtCx I a ≃ₗ[ℂ] s.A.T, ∀ y, IsCrd I hX a e
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y) := by
  obtain ⟨e, he⟩ := ColTie.exists_equiv_of_bases (σ := ColTie.sig X.B)
    (n := ColTie.dimP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX)
    (ColTie.jP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B)) t.j
    (ColTie.linearIndependent_jP_single (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    (ColTie.span_range_jP_single_eq_top (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    t.forms.li t.forms.span
  refine ⟨e, fun y => ⟨ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y, ?_, (he y).symm⟩⟩
  exact ⟨(ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y),
    ColTie.zOf_mem (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩



theorem exists_perT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px)) (tA : ∀ a : w.I.ι, Tie1 (w.st Z).toD7.what₂.embLL (mAU (w.st Z) w.I hX Xg tr true a) (p.sA true a)), ∃ d : PerD p, Nonempty (PerT w Z hX Xg tr p (fun a x => (tA a).j x) d) := by
  intro B f T w Z hX Xg tr p tA
  have hE := fun a : w.I.ι => exists_crd_equiv (w.st Z) w.I hX Xg tr a (tA a)
  choose e he using hE
  have hG : ∀ u a, ∃ g : Df.MtCx w.I a ≃ₗ[ℂ] (TC.per w.I w.l u a).Mt, ∀ F, Df.SameForm w.I w.l u a F (g F) := fun u a =>
    Df.mtCx_equiv_per w.I w.ok w.pins w.l hX u a
  choose g hg using hG
  refine ⟨⟨fun u => (g u w.I.mu0).symm.trans (e w.I.mu0), fun u a => (g u a).symm.trans (e a)⟩, ⟨⟨e, ?_, ?_, he⟩⟩⟩
  · intro u F
    have h1 : ((g u w.I.mu0).symm.trans (e w.I.mu0)).symm (e w.I.mu0 F) = g u w.I.mu0 F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u w.I.mu0 F
  · intro u a F
    have h1 : ((g u a).symm.trans (e a)).symm (e a F) = g u a F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u a F

end GlobalTheory.Mem.R3.Rw.PerId
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodMapFormsEquivRowLiftFormsUpperLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_periodMapForms_equiv_rowLiftForms_upperLevel : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px)) (tA : ∀ a : w.I.ι, Tie1 (w.st Z).toD7.what₂.embLL (mAU (w.st Z) w.I hX Xg tr true a) (p.sA true a)), ∃ d : PerD p, Nonempty (PerT w Z hX Xg tr p (fun a x => (tA a).j x) d) := by
  first | exact @GlobalTheory.Mem.R3.Rw.PerId.exists_perT | exact GlobalTheory.Mem.R3.Rw.PerId.exists_perT | (intros; apply GlobalTheory.Mem.R3.Rw.PerId.exists_perT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsDatumPrescribedTuplesDefinedWeights

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Ex

@[reducible] def reset {B : Base} {C : Cols B} (W : RowsRest B C) (mt ma : B.places.Pl → C.Tup)
    (hmt : ∀ v, mt (B.places.conj v) = mt v) (hma : ∀ v, ma (B.places.conj v) = ma v)
    (hor : ∀ v, ma v = C.mu0 ∨ ma v = mt v) : RowsRest B C :=
  { W with
    muAt := ma
    muAt_conj := hma
    muTw := mt
    muTw_conj := hmt
    muAt_or := hor
    kaBig := GlobalTheory.Mem.DfGen.kaBigB B
    kaSmall := GlobalTheory.Mem.DfGen.kaSmallB B
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host }

theorem kapDef_of_ka {B : Base} {C : Cols B} (W' : RowsRest B C) (hb : W'.kaBig = GlobalTheory.Mem.DfGen.kaBigB B)
    (hs : W'.kaSmall = GlobalTheory.Mem.DfGen.kaSmallB B) : ∀ V S N G, DV.KapDef (assemble B C W' V S N G) := by
  intro V S N G j _ _ τ
  refine ⟨fun i => ?_, fun c => ?_⟩
  · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
    rw [hb]
    exact (GlobalTheory.Mem.DfGen.aPlusB_int B j τ i).choose_spec.symm
  · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
    rw [hs]
    show ((-(GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose : ℤ) : ℚ) = -GlobalTheory.Mem.DfGen.aMinusB B j τ c
    push_cast
    rw [← (GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose_spec]

end GlobalTheory.Mem.R3.Rw.Ex

end

open GlobalTheory.Mem.R3.Rw.Ex in
theorem GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  intro B f T w hX Wt hWt
  classical
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  have hmem : ∀ v, ∃ a, w.I.xi a = T.xiTw f v := fun v => by
    have h : T.xiTw f v ∈ Set.range w.I.xi := by
      rw [w.xi_range]; exact Or.inr ⟨v, rfl⟩
    exact h
  have hconj : ∀ v, T.xiTw f (B.places.conj v) = T.xiTw f v := fun v => by
    unfold TwDat.xiTw
    rw [GlobalTheory.Mem.Top.TwFin.resChar_conj, (T.conj v).1]
  let mt : B.places.Pl → w.C.Tup := fun v => Classical.choose (hmem v)
  have hmt : ∀ v, mt (B.places.conj v) = mt v := fun v => by
    show Classical.choose (hmem (B.places.conj v)) = Classical.choose (hmem v)
    have : ∀ x y (hx : ∃ a, w.I.xi a = x) (hy : ∃ a, w.I.xi a = y), x = y →
        Classical.choose hx = Classical.choose hy := by
      rintro x y hx hy rfl; rfl
    exact this _ _ _ _ (hconj v)
  let ma : B.places.Pl → w.C.Tup := fun v => if v ∈ Wt then mt v else w.C.mu0
  have hma : ∀ v, ma (B.places.conj v) = ma v := fun v => by
    simp only [ma, hWt v, hmt v]
  have hor : ∀ v, ma v = w.C.mu0 ∨ ma v = mt v := fun v => by
    by_cases h : v ∈ Wt
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  refine ⟨reset R.W mt ma hmt hma hor, ⟨fun v => Classical.choose_spec (hmem v), fun v h => if_pos h, fun v h => if_neg h⟩,
    fun W' hb hs => kapDef_of_ka W' hb hs, GlobalTheory.MemN.shaOK_shaTrue B.toPre⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsDatumPrescribedTuplesDefinedWeightsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_rowsDatum_prescribedTuples_definedWeights : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  first | exact @GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW | exact GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW | (intros; apply GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEq

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)



theorem rMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (t : TupU I U) (t' : TupU I U')
    (h : t.1 = t'.1) :
    rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ t = rMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ ⟨τ, hτ⟩)) :))



theorem lMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (i : Fin X.toD7.R.m)
    (t : TupU I U) (t' : TupU I U') (h : t.1 = t'.1) :
    lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i t = lMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ i t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i ⟨τ, hτ⟩)) :))



theorem mAU_mLU_ixOf : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  intro X px I hX U Xg tr t
  refine ⟨fun b => ?_, fun i => ?_⟩
  · cases b
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev1 I) (chr1 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
  · have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ X.toD7.R.m := ⟨by omega, i.2⟩
    unfold mLU
    rw [dite_eq_left hi]
    exact lMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) i (tAll I (ixOf I U t)) t (tup_ixOf I t)

end GlobalTheory.Mem.R3.Rw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  first | exact @GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | exact GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | (intros; apply GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HdExists

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.HdExist

theorem hd_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → D.host.F = maximalRealSubfield D.host.E → Seed.FrmC.StdLat (Yc D 0) → (∀ i, Seed.FrmC.StdLat (Wc D i)) → ∀ (tup : T → D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ t, tupT (tup t) = t) → tup A3.A.μ0 = D.what₂.mu0 → ∃ y : Hd R.toRealDat, y.tup = tup ∧ y.tupT = tupT := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hF hY hW tup tupT htt ht0
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  obtain ⟨hTop, hinj⟩ := GlobalTheory.DefiniteMult.topMult_and_extV_injective D G Pl0 T A3.A Ks R.toRealDat F.lv2 hB
  obtain ⟨PY, PW, ιW, hPY, hPW, hiso, hmatch⟩ := GlobalTheory.StdFrameExist.frames_std_matched D hF hY hW
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  exact ⟨⟨tup, tupT, htt, ht0, hm, hTop, hinj, PY, PW, ιW, hiso, hmatch, hF, hPY, hPW⟩, rfl, rfl⟩

end GlobalTheory.Mem.R3.Rw.HdExist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRowLiftFamilyOverColumnChoices

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.PkExist

theorem rowPk_nonempty : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), Inputs (w.D Z₀) → (w.D Z₀).host.F = maximalRealSubfield (w.D Z₀).host.E → Seed.FrmC.StdLat (Yc (w.D Z₀) 0) → (∀ i, Seed.FrmC.StdLat (Wc (w.D Z₀) i)) → Holds z₀.R z₀.F → (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → Nonempty (RowPk w z₀) := by
  intro B f T w Z₀ hX Wt z₀ hIn hF hY hW hH hWt
  classical
  letI : Algebra z₀.core.Q.c.F (w.D Z₀).what₂.LL := z₀.alg
  let tupT : w.I.ι → TupU w.I (usedOf w.I T Wt) := fun a =>
    if h : ∃ t, ixOf w.I (usedOf w.I T Wt) t = a then h.choose else mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))
  have htt : ∀ t, tupT (ixOf w.I (usedOf w.I T Wt) t) = t := fun t => by
    have h : ∃ t', ixOf w.I (usedOf w.I T Wt) t' = ixOf w.I (usedOf w.I T Wt) t := ⟨t, rfl⟩
    simp only [tupT, dif_pos h]
    exact ixOf_injective w.I _ h.choose_spec
  obtain ⟨y, hy, -⟩ := HdExist.hd_exists (w.D Z₀) (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st Z₀) w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr) z₀.core.Q.c.F z₀.R z₀.F z₀.cG z₀.pins hF hY hW
    (ixOf w.I (usedOf w.I T Wt)) tupT htt (ixOf_mu0F w.I _)
  obtain ⟨hLA, hLL⟩ := GlobalTheory.T.definiteFormsAllTuples_coordinateLaws (w.st Z₀) w.px w.I hX z₀.Xg z₀.tr w.ok z₀.good.irr
  have hU := GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq (w.st Z₀) w.px w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr
  have hO : ∀ o : (w.D Z₀).what₂.O, ∃ k : z₀.core.Q.c.F, algebraMap z₀.core.Q.c.F (w.D Z₀).what₂.LL k = (w.D Z₀).what₂.OtoLL o :=
    fun o => z₀.Ks_le _ (SetLike.coe_mem _)
  obtain ⟨p, hpL, ⟨t⟩⟩ := GlobalTheory.T.exists_rowLiftReading_definiteFormCoordinates (w.D Z₀) (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st Z₀) w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr) z₀.core.Q.c.F z₀.R z₀.F z₀.cG hO hIn z₀.pins hH y
    (mAU (w.st Z₀) w.I hX z₀.Xg z₀.tr) (mLU (w.st Z₀) w.I hX z₀.Xg z₀.tr) hLA hLL
    (fun b t => by rw [hy]; exact (hU t).1 b) (fun i t => by rw [hy]; exact (hU t).2 i)
  obtain ⟨d, ⟨per⟩⟩ := GlobalTheory.T.exists_periodMapForms_equiv_rowLiftForms_upperLevel B f T w Z₀ hX z₀.Xg z₀.tr p (fun a => t.tA true a)
  obtain ⟨W₀, hmu, hkap, hsha⟩ := GlobalTheory.T.exists_rowsDatum_prescribedTuples_definedWeights B f T w hX Wt hWt
  obtain ⟨n, hn⟩ := exists_nums_numOK B w.C (Gc B w.px) p d W₀
  exact ⟨{
    y := y
    tup := fun t => (by rw [hy])
    p := p
    t := t
    mL := fun a j => (by rw [hpL])
    e := d
    per := per
    W₀ := W₀
    mu := hmu
    sha := hsha
    n := n
    kap := fun η hη V S N G' => hkap (p.what₂ d W₀ n η hη) rfl rfl V S N G'
    num := hn }⟩

end GlobalTheory.Mem.R3.Rw.PkExist
end
end
