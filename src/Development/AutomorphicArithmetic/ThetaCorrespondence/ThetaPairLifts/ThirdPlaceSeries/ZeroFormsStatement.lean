module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandard
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandardStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.scalarForm_transportedColumn_stepZero_standard : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  first | exact @GlobalTheory.Fam.rd_zero_std | exact GlobalTheory.Fam.rd_zero_std | (intros; apply GlobalTheory.Fam.rd_zero_std <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIff

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RamZero

open GlobalTheory.Mem.Col2.TwAtStd

theorem levelZero_classTransport_values {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ)
    (c : (I.stp u I.mu0 0).Cl) :
    (I.rec7 l Z).e0Tw u a ψ₀ (I.eCls0 l u a c) = ψ₀ c := by
  show ψ₀ ((I.eCls0 l u a).symm (I.eCls0 l u a c)) = ψ₀ c
  rw [Equiv.symm_apply_apply]

theorem mram_iff_ramT : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Law0 l → ∀ (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ), ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram ↔ GlobalTheory.AdForm.RamT (I := I) (l := l) (u := u) (a := a) 0 ((I.rec7 l Z).e0Tw u a ψ₀) := by
  intro B X I hI l Z _ u a ψ₀
  have hval := levelZero_classTransport_values I l Z u a ψ₀
  have e1 := mem_Fi_of_free (I.stp u I.mu0 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (l.lev u I.mu0).free0 ψ₀
  have e2 := mem_Fi_of_free (I.stp u a 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (l.lev u a).free0
    ((I.rec7 l Z).e0Tw u a ψ₀)
  have hFi : ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mu0 ↔ (I.rec7 l Z).e0Tw u a ψ₀ ∈ (I.fm l u a).Fi 0 := by
    refine e1.trans (Iff.trans ⟨fun h c' => ?_, fun h c => ?_⟩ e2.symm)
    · obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
      have := h c
      rw [← hval c] at this
      exact this
    · have := h (I.eCls0 l u a c)
      rw [hval c] at this
      exact this
  have hN : ∀ (v : ((I.rec7 l Z).mem u).A.vT) (c : (I.stp u I.mu0 0).Cl),
      ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT 0 v s (I.eCls0 l u a c)
        ((I.rec7 l Z).e0Tw u a ψ₀ ((I.fm l u a).dil 0 v s (I.eCls0 l u a c))) = ((I.rec7 l Z).mem u).A.Nm v ψ₀ c := by
    intro v c
    have eR : ∀ c' : ((I.rec7 l Z).mem u).C.cls 0, ((I.rec7 l Z).mem u).A.Nm v ψ₀ c' =
        ∑ s, (((I.rec7 l Z).fm u).dilT 0 v s c') (ψ₀ (((I.rec7 l Z).fm u).dil 0 v s c')) := fun c' => by
      unfold ColumnsAtT.Nm
      rw [LinearMap.sum_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => ((I.rec7 l Z).fm u).rhoT_dil v x ψ₀ c'
    rw [eR c]
    letI := (I.atT l u a).FvFin v
    letI := (I.atT l u a).FvDec v
    rw [finsum_eq_sum_of_fintype]
    refine Fintype.sum_equiv (Equiv.refl _) _ _ fun s => ?_
    show (I.atIn u a).dilT B.fields.emb B.embLL 0 v s (I.eCls0 l u a c)
        ((I.rec7 l Z).e0Tw u a ψ₀ ((I.atIn u a).dil 0 v s (I.eCls0 l u a c))) =
      (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v s c (ψ₀ ((I.atIn u I.mu0).dil 0 v s c))
    rw [dil_eCls0 B X I hI l u a v s c, dilT_eCls0 B X I hI l u a v s c, hval]
  unfold ColumnsAtT.Mram GlobalTheory.AdForm.RamT
  rw [Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hFi.1 h1, fun v c' => ?_⟩
    obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
    refine (hN v c).trans ?_
    exact congrFun (LinearMap.mem_ker.1 (h2 v)) c
  · rintro ⟨h1, h2⟩
    exact ⟨hFi.2 h1, fun v => LinearMap.mem_ker.2 (funext fun c => (hN v c).symm.trans (h2 v (I.eCls0 l u a c)))⟩

end GlobalTheory.RamZero

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_ramifiedForms_transport_iff : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Law0 l → ∀ (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ), ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram ↔ GlobalTheory.AdForm.RamT (I := I) (l := l) (u := u) (a := a) 0 ((I.rec7 l Z).e0Tw u a ψ₀) := by
  first | exact @GlobalTheory.RamZero.mram_iff_ramT | exact GlobalTheory.RamZero.mram_iff_ramT | (intros; apply GlobalTheory.RamZero.mram_iff_ramT <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeroForms

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem zero_forms_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col t (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) ι w c₀, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) c₀ A ι w → (∀ β, A.kb 0 β = TC.kStd X u (B.R.N 0)) → ∀ α, (∀ φ, _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ ∈ ((a.fam row col).t t).Ram 0 ∧ ∀ y, ((a.fam row col).t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) y = (GlobalTheory.Core.Mi.chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ ((I.rec7 l Z).eMu u φ).1 y) ∧ ∀ ψ ∈ ((a.fam row col).t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 row col t Ch₀ A ι w c₀ hP hkb α
  have hr := hP.ram 0 (Nat.zero_le _)
  have hq := hP.rdq 0 (Nat.zero_le _)
  have hl := hP.live
  have hok : I.Ok := hW.tr.ok
  obtain ⟨hpins⟩ := hW.tr.pins
  obtain ⟨hstd⟩ := hW.tr.std
  obtain ⟨l0, -⟩ := hW.tw
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := ha2.pinX.inf
  refine ⟨fun φ => ⟨?_, fun y => ?_⟩, fun ψ hψ => ?_⟩
  · show _ ∈ (col t).Ram 0
    exact (hr _).2 ⟨(GlobalTheory.T.stepZero_ramifiedForms_transport_iff I hok l Z l0 u (W.P.I.tup t) _).1 ((I.rec7 l Z).eMu u φ).2, fun c hc => absurd (hl.first _) hc⟩
  · show (col t).rd 0 α _ y = _
    refine (hq α _ y).trans ?_
    exact GlobalTheory.T.scalarForm_transportedColumn_stepZero_standard I hok hpins l Z _ hstd u (W.P.I.tup t) Ch₀ A hP.is (ι 0 α) (hkb _) _ hθ _ ((I.rec7 l Z).eMu u φ).2 y
  · have h1 : GlobalTheory.AdForm.RamT 0 ψ := ((hr ψ).1 hψ).1
    have h2 : ((I.rec7 l Z).e0Tw u (W.P.I.tup t)).symm ψ ∈ ((I.rec7 l Z).mem u).A.Mram :=
      (GlobalTheory.T.stepZero_ramifiedForms_transport_iff I hok l Z l0 u (W.P.I.tup t) _).2 (by rwa [LinearEquiv.apply_symm_apply])
    obtain ⟨φ, hφ⟩ := EquivLike.surjective ((I.rec7 l Z).eMu u) ⟨_, h2⟩
    refine ⟨φ, ?_⟩
    show ψ = (I.rec7 l Z).e0Tw u (W.P.I.tup t) (((I.rec7 l Z).eMu u) φ).1
    rw [hφ]
    exact (LinearEquiv.apply_symm_apply _ ψ).symm
end GlobalTheory.Fam
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeroFormsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_row_column_entry_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col t (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) ι w c₀, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) c₀ A ι w → (∀ β, A.kb 0 β = TC.kStd X u (B.R.N 0)) → ∀ α, (∀ φ, _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ ∈ ((a.fam row col).t t).Ram 0 ∧ ∀ y, ((a.fam row col).t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) y = (GlobalTheory.Core.Mi.chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ ((I.rec7 l Z).eMu u φ).1 y) ∧ ∀ ψ ∈ ((a.fam row col).t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ := by
  first | exact @_root_.GlobalTheory.Fam.zero_forms_alt | exact _root_.GlobalTheory.Fam.zero_forms_alt | (intros; apply _root_.GlobalTheory.Fam.zero_forms_alt <;> assumption)
end
end
end
