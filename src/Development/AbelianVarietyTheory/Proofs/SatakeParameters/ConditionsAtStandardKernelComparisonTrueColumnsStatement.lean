module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompari
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainStabilisersEqStandardReaderPointsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompariStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coefficientFieldCondition_of_standardKernelComparison : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → t.RK := by
  first | exact @GlobalTheory.Pdv.rk_of_std | exact GlobalTheory.Pdv.rk_of_std | (intros; apply GlobalTheory.Pdv.rk_of_std <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnSidePropertiesTrueColumns

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.Pdv

theorem colSide_of_choices {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hN : GlobalTheory.Pdv.ColNorm I)
    (hX_eq : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hS : t.S = I.S) (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst)
    (hidx : HEq t.idx I.idx) (hm2 : t.m2 = B.R.m - 2) (hglob : HEq t.glob I.glob) : GlobalTheory.KerJ.ColSide t := by
  have hb := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have kCst : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
      (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S') (cst' : ∀ μ, LocCst X' (rowSG Pr' sel' (tup' μ))),
      X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq cst' I.cst →
      ∀ μ, (cst' μ).sharp = true ∧ (I.rec7 l Z).R.m ≤ (cst' μ).A ∧ 2 * (cst' μ).M ≤ twTopDepth (I.rec7 l Z).R := by
    rintro X' Pr' sel' S' tup' cst' rfl h1 h2 rfl h3 h4
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    obtain rfl := eq_of_heq h3
    obtain rfl := eq_of_heq h4
    intro μ
    have h5 := (hN μ)
    refine ⟨hI.sharp μ, h5.1, ?_⟩
    show 2 * (I.cst μ).M ≤ 4 * B.R.m + 1
    omega
  refine ⟨?fields, ?sel, ?bad, ?chOk, ?chars, ?sharp, ?deep, ?repOne⟩
  case fields => exact hX_eq ▸ hb.1
  case sel =>
    have key : ∀ (X' : Fields) (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)),
        X' = B.fields → HEq sel' I.sel → IsSel X' sel' := by
      rintro X' sel' rfl h
      obtain rfl := eq_of_heq h
      exact hI.sel_ok
    exact key _ _ hX_eq hsel
  case bad =>
    have key : ∀ (X' : Fields) (Pr' : Primes X'), X' = B.fields → HEq Pr' (B.primes X) → ∀ v, Pr'.T v ∈ I.S := by
      rintro X' Pr' rfl h
      obtain rfl := eq_of_heq h
      exact hI.T_mem
    rw [hS]
    refine ⟨fun i => ?_, key _ _ hX_eq hPr, fun _ hl => hI.small_mem hl, hI.two_q_d_mem.2.1⟩
    rw [t.g_rec]
    exact hI.g_mem i
  case chOk =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → Ch'.Ok := by
      rintro X' Pr' Ch' rfl h1 h2
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      exact hI.ch_ok
    exact key _ _ _ hX_eq hPr hCh
  case chars =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m) (glob' : ChGlob X' (I.rec7 l Z).R.m)
        (seam' : Seam (I.rec7 l Z) X'), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → HEq glob' I.glob → HEq seam' (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) →
        ∃ eta, Ch'.Tied glob'.σ₀ (fun j τ => ((I.rec7 l Z).hc (seam'.iT τ)).e j) glob'.mu0 eta := by
      rintro X' Pr' Ch' glob' seam' rfl h1 h2 h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      exact ⟨I.C.eta, hI.ch_tied⟩
    exact key _ _ _ _ _ hX_eq hPr hCh hglob hseam
  case sharp => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).1
  case deep => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).2
  case repOne =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
        (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S')
        (idx' : ∀ μ, ChIdx X' Pr' (I.rec7 l Z).R (QE sel' (tup' μ : Chr X'.F X'.E X'.K))),
        X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq idx' I.idx →
        ∀ μ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (idx' μ).β j) (P : rowSG Pr' sel' (tup' μ)), P.1 ∈ Pr'.vGs → (idx' μ).h j b P = 1 := by
      rintro X' Pr' sel' S' tup' idx' rfl h1 h2 rfl h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      intro μ
      exact (hN μ).2.2
    rw [hm2]
    exact key _ _ _ _ _ _ hX_eq hPr hsel hS htup hidx

theorem colSide_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.KerJ.ColSide t := by
  intro B X I hI _ l Z L hT Gi Gl K Y cX ex t hN hS
  exact colSide_of_choices I hI l Z t hN hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.tup hS.cst hS.idx hS.m2 hS.glob

end GlobalTheory.Pdv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnSidePropertiesTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnSide_properties_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.KerJ.ColSide t := by
  first | exact @GlobalTheory.Pdv.colSide_of_std | exact GlobalTheory.Pdv.colSide_of_std | (intros; apply GlobalTheory.Pdv.colSide_of_std <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardBaseLevels

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Pdv.stdKer_stdRd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardReadersStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardKernelData_with_standardBaseLevels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned := by
  first | exact @GlobalTheory.Pdv.stdKer_stdRd | exact GlobalTheory.Pdv.stdKer_stdRd | (intros; apply GlobalTheory.Pdv.stdKer_stdRd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLawStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueChain_complexForms_stabiliser_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ u a, GlobalTheory.KerJ.FormsAre ((I.tw l l0 Z).fm u a) (O u a) (GlobalTheory.Pdv.stabStd I l Z u a) := by
  first | exact @GlobalTheory.Pdv.FormsStd.formsAre_stabStd | exact GlobalTheory.Pdv.FormsStd.formsAre_stabStd | (intros; apply GlobalTheory.Pdv.FormsStd.formsAre_stabStd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumns

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.duty_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → GlobalTheory.Pdv.Duty t := by
  intro B X I hOk hP l Z l0 L hT Gi Gl K Y cX ex t hN hJ htw hS hE
  obtain ⟨t', hS', hR', -⟩ := GlobalTheory.T.standardKernelData_with_standardBaseLevels I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  refine ⟨GlobalTheory.T.columnSide_properties_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t hN hS, hE, GlobalTheory.T.coefficientFieldCondition_of_standardKernelComparison I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS,
    ⟨t', GlobalTheory.T.columnSide_properties_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS', ?_⟩⟩
  intro u μ _
  refine ⟨GlobalTheory.Pdv.stabStd I l Z u μ, ?_, GlobalTheory.T.trueChain_stabilizers_eq_standardBaseLevel_points I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS' hR' u μ⟩
  rw [htw]
  exact GlobalTheory.T.trueChain_complexForms_stabiliser_law I hOk hP l Z l0 Y.Qp t'.O hS'.O u μ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conditions_at_standardKernelComparison_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → GlobalTheory.Pdv.Duty t := by
  first | exact @GlobalTheory.Pdv.duty_of_std | exact GlobalTheory.Pdv.duty_of_std | (intros; apply GlobalTheory.Pdv.duty_of_std <;> assumption)
end
end
