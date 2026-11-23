module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupleFreeLevelLeCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxLeSup

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RdMemKOOffTwist

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
theorem GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ j hj t₀ J₀ hJ₀ α₀ t J _ i _
  have hjm : j ≤ B.R.m := by omega
  obtain ⟨ε, hε, hε'⟩ := (J.G i).q.above
  have und : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.G i).q.v :=
    GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hε'
  have hv := (GlobalTheory.Mem.Col2.TC.underQ_notMem I hW.tr.ok l u (W.P.I.tup t) (J.G i).q.v
    ⟨J.pl i, (hW.tq.Q t _).1 (J.mem i), und⟩).1
  have hlb := (hJ₀.is.reads j hjm).lb (J₀.ι j α₀)
  have hfr : ∀ e : j = (J.G i).s + 1, ∃ pos, IsStdFr pos (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e) := by
    intro e
    subst e
    exact ⟨_, (ha.stdQ _ _).1 _ _⟩
  obtain ⟨pos, hpos⟩ := hfr (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)
  have key : ∀ g ∈ J₀.A.U j (J₀.ι j α₀),
      GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) g ∈ KO (J.G i).k _ := by
    refine GlobalTheory.LevProd.OffTwist.locHom_mem_KO (J.G i).q _ (rankN (I.rec7 l Z) j hjm) _ hpos (B.T u) hv
      (J₀.A.K j hjm (J₀.ι j α₀)).lev.Lb (fun x hx r => ?_) (fun s => ?_) (σ := sigD _) (J := gramN (I.rec7 l Z) j hjm) _ (fun g hg => ?_)
    · obtain ⟨c, hc, -⟩ := (hlb x).1 hx r
      exact ⟨c, hc⟩
    · refine (hlb _).2 fun r => ?_
      by_cases h : r = s
      · subst h
        refine ⟨(B.T u : ℕ), (Pi.single_eq_same _ _).trans (map_natCast (algebraMap (𝓞 B.host.E) B.host.E) _).symm, fun _ => ⟨_, (l.pr.piT_norm u).symm⟩⟩
      · exact ⟨0, (Pi.single_eq_of_ne h _).trans (map_zero (algebraMap (𝓞 B.host.E) B.host.E)).symm, fun _ => dvd_zero _⟩
    · obtain ⟨κ, hκ⟩ := ((hJ₀.is.U j hjm _ g).1 hg).2
      exact ⟨κ.1, hκ, (J₀.A.K j hjm (J₀.ι j α₀)).lev.Uloc_lev _
        ((((J₀.A.K j hjm (J₀.ι j α₀)).lev.U_eq κ.1).1 κ.2).2 _)⟩
  intro g hg
  exact (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).2 (key g hg)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RdMemKOOffTwistStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_tuple_free_index_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  first | exact @_root_.GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt | exact _root_.GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt | (intros; apply _root_.GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxLeSupStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

theorem _root_.GlobalTheory.T.tuple_free_level_step_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J') := by
  first | exact @_root_.GlobalTheory.PenLev.relax_le_sup_alt | exact _root_.GlobalTheory.PenLev.relax_le_sup_alt | (intros; apply _root_.GlobalTheory.PenLev.relax_le_sup_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxedLevelEqTupleFree

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

theorem GlobalTheory.PenLev.rd_mem_KO_same_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i₀ i, (J₀.G i₀).q.v = (J.G i).q.v → ∀ g ∈ GfC _, _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J₀ j hj g i₀ ∈ KO (J₀.G i₀).k _ → _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ j hj t₀ J₀ _ t J _ i₀ i hv g _ h0
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L :=
    (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have h0' : GlobalTheory.LevIdx.locHom (J₀.G i₀).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J₀ j i₀ (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J₀ hj i₀)) g ∈ KO (J₀.G i₀).k _ :=
    (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).1 h0
  have hm := GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J₀.G i₀).q _ hsd
    (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J₀ j i₀ (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J₀ hj i₀)) h0'
  change GlobalTheory.PenBridge.toSum0 _ _ _ ∈ _
  rw [GlobalTheory.PenBridge.toSum0_mem_KO_iff]
  exact GlobalTheory.SplitInt.mem_KO_of_moves (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) (a.g.x j).L
    (· = (J₀.G i₀).q.v) hv.symm (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) g hm _
    ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
theorem GlobalTheory.PenLev.rd_eq_one_of_grpAt_alt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
    (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop} (hP : ¬ P (J.G i).q.v)
    {x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hx : x ∈ GlobalTheory.FinPl.grpAt _ P) : _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj x i = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff _ (· = (J.G i).q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff _ P (· = (J.G i).q.v) (fun p hp e => hP (e ▸ hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off (J.G i).q (P := (· = (J.G i).q.v)) rfl h1
  have h3 : GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) x = 1 := by
    symm
    rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
    simp [(_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)).βγ]
  change GlobalTheory.PenBridge.toSum0 _ _ _ = 1
  rw [h3, map_one]
theorem GlobalTheory.PenLev.relax_rd_mem_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α, ∀ i, _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J' j hj g i ∈ KO (J'.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' g hg i
  obtain ⟨hsup, hgf, hrd⟩ := (_root_.GlobalTheory.PenLev.mem_relax_iff' J j hj α g).1 hg
  by_cases hv : _root_.GlobalTheory.PenBridge.finitePlaceCondition J (J'.G i).q.v
  · obtain ⟨i₀, hi₀⟩ := hv
    exact _root_.GlobalTheory.PenLev.rd_mem_KO_same_alt W hW u a ha hTr j hj t J hJ t' J' hJ' i₀ i hi₀ g hgf (hrd i₀)
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) ≤
        (KO (J'.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J' j hj)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact _root_.GlobalTheory.T.true_geometry_tuple_free_index_alt W hW u a ha hTr j hj t J hJ α t' J' hJ' i hv x hx
      · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
          _root_.GlobalTheory.PenLev.rd_eq_one_of_grpAt_alt J' hj i hv hx]
        exact one_mem _
    exact hle hsup
theorem GlobalTheory.PenLev.relaxed_level_eq_tuple_free_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α = _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α
  have hle : ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j),
      _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ≤ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J' j hj α' := by
    intro t J hJ α t' J' hJ' α' x hx
    have hx' := (_root_.GlobalTheory.PenLev.mem_relax_iff' J j hj α x).1 hx
    exact (_root_.GlobalTheory.PenLev.mem_relax_iff' J' j hj α' x).2
      ⟨_root_.GlobalTheory.T.tuple_free_level_step_alt W hW u a ha hTr j hj t J hJ α t' J' hJ' α' x hx, hx'.2.1,
        _root_.GlobalTheory.PenLev.relax_rd_mem_KO_alt W hW u a ha hTr j hj t J hJ α t' J' hJ' x hx⟩
  obtain ⟨t₀, J₀, α₀, hJ₀, h⟩ := _root_.GlobalTheory.PenLev.base_level_subgroup_eq_relax J j hj hJ α
  rw [h]
  exact le_antisymm (hle _ _ hJ α _ _ hJ₀ α₀) (hle _ _ hJ₀ α₀ _ _ hJ α)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxedLevelEqTupleFreeStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_tuple_free_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α = _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj := by
  exact @_root_.GlobalTheory.PenLev.relaxed_level_eq_tuple_free_alt
end
end
end
