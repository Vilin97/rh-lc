module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiDValuesAndCcTop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTie
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtSplitUnramifiedPlacesOfChainCharts
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnExistsChainChartsKernelDataForms

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdKerStdRdMark

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Pdv.stdKer_stdRd_mark : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t'.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) := by
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
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
  · exact fun u a i c => Iff.rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtSplitUnramifiedPlacesOfChainChartsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.jointsAtSplitUnramifiedPlaces_of_chainCharts : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (μ : D.what₂.Tup), G.LatTied hT Gi Gl → (∀ u, Nonempty (JIn t u μ)) → GlobalTheory.TwV.JointsAt t μ := by
  first | exact @GlobalTheory.TwV.jointsAt_of_jIn | exact GlobalTheory.TwV.jointsAt_of_jIn | (intros; apply GlobalTheory.TwV.jointsAt_of_jIn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroFormIdentificationRefTupleEqId

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem stepZeroFormIdentification_refTuple_eq_id : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), (I.tw l l0 Z).e0 u (I.rec7 l Z).what₂.mu0 = (I.tw l l0 Z).eMu0 u 0 (Nat.zero_le _) := by
  intro B X I _ _ l Z l0 u
  apply LinearEquiv.ext
  intro x
  have h := (l0 u I.mu0).choose_spec.2 x
  rw [stepZeroTwist_reference_tuple_eq_id l u] at h
  exact (I.fm l u I.mu0).emb_inj 0 h

end GlobalTheory.TwU.AtTrue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroFormIdentificationRefTupleEqIdStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tw_e0_mu0_eq_eMu0_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), (I.tw l l0 Z).e0 u (I.rec7 l Z).what₂.mu0 = (I.tw l l0 Z).eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.TwU.AtTrue.stepZeroFormIdentification_refTuple_eq_id | exact GlobalTheory.TwU.AtTrue.stepZeroFormIdentification_refTuple_eq_id | (intros; apply GlobalTheory.TwU.AtTrue.stepZeroFormIdentification_refTuple_eq_id <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnExistsChainChartsKernelDataFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_exists_chainCharts_kernelData_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → ∀ (u : B.Word) (a : I.ι), Nonempty (GlobalTheory.Port.JIn t u a) := by
  first | exact @GlobalTheory.Port.jIn_nonempty_true | exact GlobalTheory.Port.jIn_nonempty_true | (intros; apply GlobalTheory.Port.jIn_nonempty_true <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnJointsHoldAllTuples

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AllTuples

theorem joints_all_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∀ a : I.ι, GlobalTheory.TwV.JointsAt t a) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B X I hOk hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJ htw hpi hK hRd hpin hC hDt hh hf hchi hLat
  refine ⟨fun a => ?_, fun u => ?_⟩
  · exact GlobalTheory.T.jointsAtSplitUnramifiedPlaces_of_chainCharts t a hLat (fun u =>
      GlobalTheory.T.trueColumn_exists_chainCharts_kernelData_forms I hOk hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJ htw hpi hK hRd hpin hC hDt hh hf hchi u a)
  · rw [htw]
    exact GlobalTheory.T.tw_e0_mu0_eq_eMu0_zero I hOk hP l Z l0 u

end GlobalTheory.TwU.AllTuples
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnJointsHoldAllTuplesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_joints_hold_all_tuples : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∀ a : I.ι, GlobalTheory.TwV.JointsAt t a) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.TwU.AllTuples.joints_all_true | exact GlobalTheory.TwU.AllTuples.joints_all_true | (intros; apply GlobalTheory.TwU.AllTuples.joints_all_true <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelRelationTrueColumnsJointsAllTuples

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.oneTie_jointsAt_all : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B X I hOk hP l l0 Z L hT Gi Gl K Y cX ex t C full g nch tp _htp hTw hJ htw hpi hS hC _hLv hDt hg hgf hD hLat
  obtain ⟨t', hS', hR', _, hM'⟩ := GlobalTheory.Pdv.stdKer_stdRd_mark I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  obtain ⟨h1, h2⟩ := GlobalTheory.T.trueColumn_joints_hold_all_tuples I hOk hP l Z l0 L hT Gi Gl K Y cX ex t' C full g hTw hJ htw hpi hS' hR' hM' hC hDt hg hgf hD hLat
  exact ⟨⟨t', h1⟩, h2⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelRelationTrueColumnsJointsAllTuplesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.Pdv.oneTie_jointsAt_all | exact GlobalTheory.Pdv.oneTie_jointsAt_all | (intros; apply GlobalTheory.Pdv.oneTie_jointsAt_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtAllStd

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain



theorem GlobalTheory.Svd.jointsAt_all_std : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → G.LatTied O.gatT O.Gx O.Gy → (∃ t : KerEntTied O.ex, ∀ μ, GlobalTheory.TwV.JointsAt t μ) ∧ ∀ u, O.ex.tw.e0 u (w.D Z).what₂.mu0 = O.ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B f T w Z O P hL
  obtain ⟨htw, -, hpiT, -, t, hstd, -, -⟩ := GlobalTheory.Svd.Part.kerTie B f T w Z O P
  have hchi := (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1
  obtain ⟨L, gatT, Gx, Gy, K, X, cX, ex⟩ := O
  obtain ⟨pin, col, errX, tp, xi, qp, ker0, ker_eq, ker⟩ := P
  simp only [ofObj, extraObj] at ker_eq
  have h1 := congrArg Sigma.fst ker_eq
  simp only at h1
  subst h1
  have h2 := eq_of_heq (Sigma.mk.inj ker_eq).2
  have h3 := congrArg Sigma.fst h2
  simp only at h3
  obtain ⟨lev, th, th_io, cmp, lat, tw, exker⟩ := ex
  simp only at h3
  subst h3
  exact GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples w.I w.ok w.pins w.l w.l0 Z L col.Gt Gx Gy K X cX _ t col.C col.full col.g _ tp xi
    pin.isTw pin.jets htw hpiT hstd col.std col.stdLv col.stdDt col.herm_eq col.forms_eq hchi hL
end
end
