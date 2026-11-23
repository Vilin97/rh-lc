module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZeroStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinationsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatVNEqOffLevelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumProdStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataChainStep

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDatum

theorem vac_true_mono {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    (P : GlobalTheory.FinPl.Pl D → Prop) {F : WO S T → ℂ} (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) F) :
    GlobalTheory.FinPl.Vac ψ S T LS LT P F := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

end GlobalTheory.MidDatum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollect

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.CollectComb

theorem foldr_comp_eq {ι X : Type} (c o : ι → X → X) (hc : ∀ a b, a ≠ b → ∀ x, c a (o b x) = o b (c a x)) :
    ∀ (l : List ι), l.Nodup → ∀ F : X,
      l.foldr (fun i g => c i (o i g)) F = l.foldr (fun i g => c i g) (l.foldr (fun i g => o i g) F) := by
  have hpast : ∀ (b : ι) (t : List ι), b ∉ t → ∀ x,
      o b (t.foldr (fun i g => c i g) x) = t.foldr (fun i g => c i g) (o b x) := by
    intro b t hb x
    induction t with
    | nil => rfl
    | cons a t ih =>
      have hab : a ≠ b := fun h => hb (h ▸ List.mem_cons_self)
      have hbt : b ∉ t := fun h => hb (List.mem_cons_of_mem _ h)
      simp only [List.foldr_cons]
      rw [← ih hbt, hc a b hab]
  intro l hl F
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    rw [ih hl.2, hpast a t hl.1]

end GlobalTheory.CollectComb

theorem GlobalTheory.CollectComb.main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e g) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F) := by
  intro D ψ hψ S T M M' hM hM' n L hinj F
  have hat : ∀ i, GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).e ∧ GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).o := fun i =>
    ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).e_is.1 u hu),
     fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).o_at u hu)⟩
  refine GlobalTheory.CollectComb.foldr_comp_eq (fun i g => comb ψ S T (L i).e g) (fun i g => comb ψ S T (L i).o g) ?_ _
    (List.nodup_finRange n) F
  intro a b hab x
  have hdisj : ∀ p, p = (L a).q.v → ¬ p = (L b).q.v := fun p ha hb => hab (hinj (ha.symm.trans hb))
  exact (GlobalTheory.DisjComb.main D ψ hψ S T _ _ hdisj).1 _ _ (hat a).1 (hat b).2 x
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollectStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.heisenbergCombinations_distinct_split_places_collect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e g) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F) := by
  first | exact @GlobalTheory.CollectComb.main | exact GlobalTheory.CollectComb.main | (intros; apply GlobalTheory.CollectComb.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.LocComp

theorem combAt_o {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (l : GlobalTheory.SeeSaw.LocPl ψ S T M M') {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P l.q.v) : GlobalTheory.FinPl.CombAt P l.o :=
  fun x hx i j => GlobalTheory.LocMod.PinInhab.mem_idAt_of_supp l.q hP (l.o_at x hx i j)

theorem combAt_comp {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {P : GlobalTheory.FinPl.Pl D → Prop} {e e' : WO S T →₀ ℂ} (he : GlobalTheory.FinPl.CombAt P e) (he' : GlobalTheory.FinPl.CombAt P e') :
    ∃ e'', GlobalTheory.FinPl.CombAt P e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f) := by
  have h4 := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.2.2.1
  have hm : ∀ {c : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt P c → GlobalTheory.FinPl.CombAt (fun p => P p ∨ False) c :=
    fun hc x hx i j => by simpa only [or_false] using hc x hx i j
  obtain ⟨e'', h1, h2⟩ := h4 e e' (hm he) (hm he')
  exact ⟨e'', fun x hx i j => by simpa only [or_false] using h1 x hx i j, h2⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ i, P (L i).q.v) → ∃ o' : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P o' ∧ ∀ F, comb ψ S T o' F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F := by
  intro D ψ hψ S T M M' _ _ n
  induction n with
  | zero =>
    intro L _ P _
    refine ⟨Finsupp.single 0 1, GlobalTheory.FinPl.OffTest.combAt_single_zero P 1, fun F => ?_⟩
    rw [GlobalTheory.FinPl.OffTest.comb_single_zero]
    simp
  | succ n ih =>
    intro L hinj P hP
    obtain ⟨o₁, h₁, h₁'⟩ := ih (fun i => L i.succ) (fun a b h => Fin.succ_injective _ (hinj h)) P (fun i => hP i.succ)
    obtain ⟨o', h', h''⟩ := combAt_comp hψ (combAt_o (L 0) (hP 0)) h₁
    refine ⟨o', h', fun F => ?_⟩
    rw [h'', h₁', List.finRange_succ, List.foldr_cons, List.foldr_map]

end GlobalTheory.LocComp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.localCombinations_compose_finitely_many_places : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ i, P (L i).q.v) → ∃ o' : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P o' ∧ ∀ F, comb ψ S T o' F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F := by
  first | exact @GlobalTheory.LocComp.main | exact GlobalTheory.LocComp.main | (intros; apply GlobalTheory.LocComp.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsRest

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.MidVacLat
variable {D : D7}
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j hj d₀ hd₀
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sd0 : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY j (by omega))
  have sd1 : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) hj)
  obtain ⟨M, hM, hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd0).1 (f.g.b j)
  obtain ⟨M', hM', hmv'⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd1).1 (f.g.b (j + 1))
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hvth := hd₀.2.1.2.theta
  have hvlat := hd₀.2.1.2.lat
  exact ⟨M, M', hM, hM', hmv _, hmv' _, hWe.om_pres _ _ hvth,
    isLatVac_move hWe sd0 hM sd1 hM' (hmv _) (hmv' _) hvth hvlat⟩
end GlobalTheory.MidVacLat
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsRestStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.descent_data_step_lattice_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
  first | exact @_root_.GlobalTheory.MidVacLat.main_alt_alt | exact _root_.GlobalTheory.MidVacLat.main_alt_alt | (intros; apply _root_.GlobalTheory.MidVacLat.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEq

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.MidDatum
theorem moved_datum_eq_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀
  have hstd : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  obtain ⟨M, M', hM, hM', hmv, hmv', hvac⟩ := _root_.GlobalTheory.T.descent_data_step_lattice_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀
  obtain ⟨κ, hκ, Lp, hq, he, hint, hdat⟩ :=
    _root_.GlobalTheory.T.descent_data_step_vector_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀ M M' hM hM' hmv hmv' hvac
  have hinj : Function.Injective fun i => (Lp i).q.v := by
    intro a b h
    apply hPin.inj
    simpa only [hq] using h
  have hP : ∀ i, (Lp i).q.v ∈ v.gP := fun i => (hPin.places _).2 ⟨i, hq i⟩
  obtain ⟨o', ho', hcomb⟩ := GlobalTheory.T.localCombinations_compose_finitely_many_places D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj (· ∈ v.gP) hP
  have hN : IsSelfDualC (Yc D j) (v.N j) := hv.sd j (by omega)
  have hN' : IsSelfDualC (Yc D (j + 1)) (v.N (j + 1)) := hv.sd (j + 1) hj
  have hoff := _root_.GlobalTheory.T.descent_data_step_self_dual_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj M M' hmv hmv'
  obtain ⟨F₀, hF₀t, hF₀at, -⟩ := hdat d₀ hd₀
  have hV := (GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ F₀ hvac hF₀at hF₀t).2 (v.N j) (v.N (j + 1)) hN hN' hint
    (fun p hp => hoff p (by
      rw [hPin.places]
      rintro ⟨i, rfl⟩
      exact hp i (hq i).symm))
  have hth : IsThetaFunO f.c.ψ _ _ (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
    rw [hcomb]; exact hV.1
  refine ⟨M, M', o', hM, hM', ho', vac_true_mono _ hvac, ?_, ?_, κ, hκ, ?_⟩
  · rw [hcomb]; exact vac_true_mono _ hV
  · intro hne; rw [hcomb]; exact GlobalTheory.T.foldr_splitPlaceSecondCombinations_vacuum_ne_zero D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ hvac hne
  · intro d hd
    obtain ⟨F, hFt, hFat, hFeq⟩ := hdat d hd
    rw [hFeq]
    congr 1
    rw [(GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ F hvac hFat hFt).1, GlobalTheory.T.heisenbergCombinations_distinct_split_places_collect D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj, ← hcomb,
      hPin.eG j hj _ hth]
    simp only [he]
end GlobalTheory.MidDatum
end
end
end
