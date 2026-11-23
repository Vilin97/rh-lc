module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupleFreeLevelLeCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutMemU
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BcPrVMemLevelVLOfMoves
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelStep

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem cutG_mem_congGrp (V : HSp D) (I : Ideal (AE D)) (ε : AF D.host.F) (hε : ε * ε = ε) {g : GA D V}
    (hg : g ∈ congGrp V I) : cutG V ε hε g ∈ congGrp V I := by
  rw [mem_congGrp_iff] at hg ⊢
  intro i j
  rw [mt_cutG, cut_sub_one, Matrix.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (hg i j)

theorem grpAt_mono (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : grpAt V P ≤ grpAt V P' := by
  intro g hg
  rw [mem_grpAt_iff_parts] at hg ⊢
  exact fun i j => ⟨(hg i j).1, fun w hw => (hg i j).2 w fun h' => hw (h w h')⟩

theorem grpAt_inf_le (V : HSp D) (Q P R : Pl D → Prop) (h : ∀ p, Q p → ¬ P p → R p) {g : GA D V}
    (h1 : g ∈ grpAt V Q) (h2 : g ∈ grpAt V fun p => ¬ P p) : g ∈ grpAt V R := by
  rw [mem_grpAt_iff_parts] at h1 h2 ⊢
  refine fun i j => ⟨(h1 i j).1, fun w hw => ?_⟩
  by_cases hQ : Q w
  · by_cases hP : P w
    · exact (h2 i j).2 w (not_not.2 hP)
    · exact absurd (h w hQ hP) hw
  · exact (h1 i j).2 w hQ

theorem locHom_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y)
    {P : Pl D → Prop} (hP : P q.v) {g : GA D V} (hg : g ∈ grpOff V P) : GlobalTheory.LevIdx.locHom q V F g = 1 := by
  ext1
  rw [GlobalTheory.LevIdx.locHom_val, GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q hP hg, Matrix.mul_one, F.γβ]
  rfl

end GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
end

noncomputable section

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutMemUStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_row_step_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p → p ∈ Q) → (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p → p ∈ Q) → ∀ x ∈ J.A.U j (J.ι j α), GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') := by
  first | exact @_root_.GlobalTheory.PenLevOff.cut_mem_U_alt | exact _root_.GlobalTheory.PenLevOff.cut_mem_U_alt | (intros; apply _root_.GlobalTheory.PenLevOff.cut_mem_U_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepRelation

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenBridge.SuppLev



theorem bc_prV_eq_one_of_not (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (κ : GA D S)
    (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hg : GlobalTheory.AdForm.finM S hn κ = g.1) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (w : HeightOneSpectrum (𝓞 D.host.F))
    (hw : ¬ P w) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S P) : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g = 1 := by
  subst hn
  have h1 : GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ = 1 :=
    ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff S _ κ).1 hκ).2 w hw
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram w κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ)).val i j =
        GlobalTheory.StabConjIndex.swap w ((GlobalTheory.AdelicU.matHom (Fv D.host.F w) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV w (g.1 i j) = GlobalTheory.StabConjIndex.swap w (GlobalTheory.AdelicU.compFin _ _ w _)
    rw [← hij]
    exact GlobalTheory.FamTrace.prV_toEAf_eq_swap D w _
  rw [hE, h1, map_one]



theorem exists_mem_level_set (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (K : StepLevel D.host.F D.host.E (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) T f bad)
    (t : 𝓞 D.host.E) (ht : t ∣ (T : 𝓞 D.host.E))
    (hLb : ∀ x, x ∈ K.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r))
    (L : GlobalTheory.FinPl.Lat S) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (κ : GA D S) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S P)
    (hP : ∀ v, P v → v ∉ bad ∧ (T : 𝓞 D.host.F) ∉ v.asIdeal ∧ GlobalTheory.FinPl.Moves S κ L L (· = v)) :
    ∃ x : K.U, x.1.1 = GlobalTheory.AdForm.finM S hn κ := by
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ Formalism.UG.UPts (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM S hn κ = g.1 := by
    obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D S n hn
    have hf := GlobalTheory.FinPl.SetCut.grpAt_le_GfC S _ hκ
    exact ⟨(e ⟨κ, hf⟩).1, (e ⟨κ, hf⟩).2, (he ⟨κ, hf⟩).symm⟩
  refine ⟨⟨g, (K.U_eq _).2 ⟨hgU, fun w => ?_⟩⟩, hg.symm⟩
  by_cases hw : P w
  · obtain ⟨hb, hT, hm⟩ := hP w hw
    subst hn
    have key : ∀ j i : Fin S.rank, ∃ r : 𝓞 D.host.E,
        (Pi.single j (T : D.host.E) : Fin S.rank → D.host.E) i = (r : D.host.E) ∧ t ∣ r := fun j i => by
      rw [Pi.single_apply]
      split_ifs
      · exact ⟨T, (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) T).symm, ht⟩
      · exact ⟨0, rfl, dvd_zero _⟩
    have e := GlobalTheory.FamTrace.levelVL_eq_of_std (sigD D) (S.gram.reindex (finCongr rfl) (finCongr rfl)) (Lb := K.Lb) (Λ := L) hT
      (fun x hx j => let ⟨r, hr, _⟩ := (hLb x).1 hx j; ⟨r, hr⟩)
      (fun j => (hLb _).2 fun i => let ⟨r, hr, hd⟩ := key j i; ⟨r, hr, fun _ => hd⟩)
      (fun x hx => (hL x).1 hx) (fun j => (hL _).2 fun i => let ⟨r, hr, _⟩ := key j i; ⟨r, hr⟩)
    rw [K.Uloc_hyp w hb hT, e]
    exact GlobalTheory.FamTrace.bc_prV_mem_levelVL_of_moves D S _ rfl L L hfg (fun _ => Iff.rfl) κ g hg w hm
  · rw [bc_prV_eq_one_of_not D S n hn κ g hg P w hw hκ]
    exact one_mem _

end GlobalTheory.PenBridge.SuppLev


end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SuppMemLevel

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenBridge.SuppLev
end GlobalTheory.PenBridge.SuppLev
open GlobalTheory.PenBridge in

theorem GlobalTheory.PenBridge.supp_mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (P : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p ∈ P, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p ∧ ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p) → ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ P), (∀ i, (J.G i).q.v ∈ P → _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj x i ∈ KO (J.G i).k _) → x ∈ J'.A.U j (J'.ι j α') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ t' J' hJ' α' P hP x hx hrd
  have hjm : j ≤ B.R.m := by omega
  have hok : I.Ok := hW.tr.ok
  have hsd : IsSelfDualC ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (a.g.x j).L := (ha.x j hjm).sd
  haveI : Submodule.IsLattice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (a.g.x j).L := hsd.1
  have hfg : (a.g.x j).L.FG := Submodule.IsLattice.fg (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (a.g.x j).L
  have hlb := (hJ'.is.reads j hjm).lb (J'.ι j α')
  refine (hJ'.is.U j hjm _ _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hx, ?_⟩
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hd : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := ⟨_, (hPr.piT_norm u).symm⟩
  refine GlobalTheory.PenBridge.SuppLev.exists_mem_level_set (I.rec7 l Z) _ _ _ (J'.A.K j hjm (J'.ι j α')).lev (X.piT u) hd hlb
    (a.g.x j).L hfg
    (fun y => ((hat.pinX.xs j hjm).2.2 y).trans
      (forall_congr' fun r => ⟨fun h => ⟨⟨y r, h⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩)) (· ∈ P) x hx ?_
  intro v hvP
  obtain ⟨⟨i, hi⟩, hn'⟩ := hP v hvP
  subst hi
  have hu : I.UnderQ (W.P.I.tup t) (J.G i).q.v :=
    ⟨J.pl i, (hW.tq.Q t (J.pl i)).1 (J.mem i), ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).2 i).symm⟩
  obtain ⟨hTv, hgv⟩ := GlobalTheory.Mem.Col2.TC.underQ_notMem I hok l u _ _ hu
  refine ⟨fun h => ?_, hTv, ?_⟩
  · rcases hJ'.is.bad_le j hjm _ h with (h0 | h0) | ⟨Q, hQ, e⟩
    · exact hgv 0 h0
    · exact hgv 1 h0
    · obtain ⟨i', hi'⟩ := hJ'.surj Q ((hW.tq.Q t' Q).2 hQ)
      refine hn' ⟨i', ?_⟩
      rw [(_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t' J' hJ').2 i', hi']
      exact e
  · have h1 := hrd i hvP
    rw [_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel, MonoidHom.pi_apply, _root_.GlobalTheory.PenBridge.rd_at_apply, toSum0_mem_KO_iff] at h1
    exact GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J.G i).q _ hsd (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) h1
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SuppMemLevelStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_row_step_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (P : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p ∈ P, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p ∧ ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p) → ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ P), (∀ i, (J.G i).q.v ∈ P → _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj x i ∈ KO (J.G i).k _) → x ∈ J'.A.U j (J'.ι j α') := by
  exact @_root_.GlobalTheory.PenBridge.supp_mem_level_alt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxLeSup

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut
variable {D : D7}
end GlobalTheory.PenLev.CongruenceSubgroupLevelSupport
end
noncomputable section
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut GlobalTheory.PenLev.CongruenceSubgroupLevelSupport in
theorem GlobalTheory.PenLev.relax_le_sup_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α t' J' hJ' α' g hg
  classical
  rw [_root_.GlobalTheory.PenLev.mem_relax_iff'] at hg
  obtain ⟨hsup, -, hint⟩ := hg
  let QJ : Finset (Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J.G i).q.v
  let QJ' : Finset (Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J'.G i).q.v
  have hQJ : ∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p ↔ p ∈ QJ := fun p => by simp [QJ, _root_.GlobalTheory.PenBridge.finitePlaceCondition]
  have hQJ' : ∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p ↔ p ∈ QJ' := fun p => by simp [QJ', _root_.GlobalTheory.PenBridge.finitePlaceCondition]
  set Q := QJ ∪ QJ' with hQ
  set P := QJ \ QJ' with hP
  have hN : (grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)).Normal := by
    unfold grpAt congGrp
    infer_instance
  have hmul := Subgroup.mul_normal (J.A.U j (J.ι j α)) (grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J))
  have hg' : g ∈ ((J.A.U j (J.ι j α) ⊔ grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) : Subgroup _) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := hsup
  rw [hmul] at hg'
  obtain ⟨x, hx, n, hn, rfl⟩ := hg'
  beta_reduce at hint ⊢
  have hxf : x ∈ GfC ((I.rec7 l Z).sp.X j) := ((hJ.is.U j (by omega) _ x).1 hx).1
  have huo : cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') :=
    _root_.GlobalTheory.T.true_geometry_row_step_value_alt W hW u a ha hat j hj t J hJ α t' J' hJ' α' Q (fun p hp => Finset.mem_union_left _ ((hQJ p).1 hp))
      (fun p hp => Finset.mem_union_right _ ((hQJ' p).1 hp)) x hx
  set uo := cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self Q) x
  set uq := cutG ((I.rec7 l Z).sp.X j) _ (idemQ_mul_self Q) x
  have huq : uq ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := cutG_mem_Q ((I.rec7 l Z).sp.X j) Q x
  have huoQ : uo ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ Q) := cutG_mem_Qc ((I.rec7 l Z).sp.X j) Q hxf
  have hnQ : n ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := grpAt_mono ((I.rec7 l Z).sp.X j) (fun p hp => Finset.mem_union_left _ ((hQJ p).1 hp)) hn
  set w := uq * n
  have hw : w ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := mul_mem huq hnQ
  have hgw : uq * uo * n = uo * w := by
    rw [comm_Q ((I.rec7 l Z).sp.X j) Q huq huoQ, mul_assoc]
  have hx' : x = uq * uo := (cutG_mul_cutG ((I.rec7 l Z).sp.X j) Q x).symm
  set wp := cutG ((I.rec7 l Z).sp.X j) _ (idemQ_mul_self P) w
  set wr := cutG ((I.rec7 l Z).sp.X j) _ (one_sub_idemQ_mul_self P) w
  have hwp : wp ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ P) := cutG_mem_Q ((I.rec7 l Z).sp.X j) P w
  have hwrP : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ P) := cutG_mem_Qc ((I.rec7 l Z).sp.X j) P (grpAt_le_GfC ((I.rec7 l Z).sp.X j) _ hw)
  have hwrQ : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∈ Q) := cutG_mem_congGrp ((I.rec7 l Z).sp.X j) _ _ _ hw
  have hwr : wr ∈ grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J') :=
    grpAt_inf_le ((I.rec7 l Z).sp.X j) (· ∈ Q) (· ∈ P) _ (fun p h1 h2 => by
      rw [hQJ']
      rw [hQ, Finset.mem_union] at h1
      rw [hP, Finset.mem_sdiff] at h2
      tauto) hwrQ hwrP
  have hww : w = wp * wr := (cutG_mul_cutG ((I.rec7 l Z).sp.X j) P w).symm
  have hgeq : x * n = uo * wp * wr := by
    rw [hx', hgw, hww, mul_assoc]
  have hwp' : wp ∈ J'.A.U j (J'.ι j α') := by
    refine _root_.GlobalTheory.T.true_geometry_row_step_relation_alt W hW u a ha hat j hj t J hJ t' J' hJ' α' P (fun p hp => ?_) wp hwp (fun i hi => ?_)
    · rw [hP, Finset.mem_sdiff] at hp
      exact ⟨(hQJ p).2 hp.1, fun h => hp.2 ((hQJ' p).1 h)⟩
    · have hiQ : (J.G i).q.v ∈ Q := by
        rw [hP, Finset.mem_sdiff] at hi
        exact Finset.mem_union_left _ hi.1
      have e1 : _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj uo i = 1 := by
        show _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i _ uo = 1
        rw [_root_.GlobalTheory.PenBridge.rd_at_apply, locHom_eq_one (J.G i).q ((I.rec7 l Z).sp.X j) _ (P := (· ∈ Q)) hiQ
          (grpAt_le_grpOff ((I.rec7 l Z).sp.X j) (· ∉ Q) (· ∈ Q) (fun p h h' => h h') huoQ), map_one]
      have e2 : _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj wr i = 1 := by
        show _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i _ wr = 1
        rw [_root_.GlobalTheory.PenBridge.rd_at_apply, locHom_eq_one (J.G i).q ((I.rec7 l Z).sp.X j) _ (P := (· ∈ P)) hi
          (grpAt_le_grpOff ((I.rec7 l Z).sp.X j) (· ∉ P) (· ∈ P) (fun p h h' => h h') hwrP), map_one]
      have h := hint i
      rw [hgeq, map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, e1, e2, one_mul, mul_one] at h
      exact h
  rw [hgeq]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem huo hwp')) (Subgroup.mem_sup_right hwr)
end
end
end
end
