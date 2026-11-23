module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CosetLevelEqOfReadsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTrans
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepValue

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLevOff

section Cut

open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut



variable {D : D7}

theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add (f := _)]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_congr (v : GlobalTheory.FinPl.Pl D) {y y' : AE D} (h : GlobalTheory.FinPl.compAt D v y = GlobalTheory.FinPl.compAt D v y') :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = Formalism.UG.prV (E := D.host.E) v (toEAf D y') := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  generalize finPart D y' = z' at h ⊢
  refine (prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)
  rw [h]

theorem bc_congr (V : HSp D) {n : ℕ} (hn : V.rank = n) (v : GlobalTheory.FinPl.Pl D) {g h : GA D V} {x y : GL (Fin n) (EF D)}
    (hx : x.1 = finM V hn g) (hy : y.1 = finM V hn h)
    (e : ∀ i j, GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V g i j) = GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V h i j)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) y := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = Formalism.UG.prV (E := D.host.E) v (y.1 i j)
  rw [hx, hy]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  exact prV_toEAf_congr v (e _ _)

theorem bc_eq_one (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : ¬ P v) {g : GA D V}
    (hg : g ∈ grpAt V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  have h1 : (1 : GL (Fin n) (EF D)).1 = finM V hn 1 := by
    subst hn
    rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  rw [bc_congr V hn v hx h1 fun i j => ?_, map_one]
  have := ((mem_grpAt_iff_parts V P g).1 hg i j).2 v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [this, GlobalTheory.SplitCut.mt_one]

abbrev cutAt (V : HSp D) (v : GlobalTheory.FinPl.Pl D) : GA D V →* GA D V := cutG V _ (idemQ_mul_self {v})

theorem cutAt_mem (V : HSp D) (v : GlobalTheory.FinPl.Pl D) (g : GA D V) : cutAt V v g ∈ grpAt V (· ∈ ({v} : Finset (GlobalTheory.FinPl.Pl D))) :=
  cutG_mem_Q V {v} g

theorem compAt_cutAt (V : HSp D) (v : GlobalTheory.FinPl.Pl D) (g : GA D V) (i j) :
    GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V (cutAt V v g) i j) = GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V g i j) := by
  rw [mt_cutG, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.map_add (f := _), RingHom.map_mul,
    RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ {v}).2 v, if_pos (Finset.mem_singleton_self v), sub_self,
    zero_mul, one_mul, add_zero]

theorem grpAt_mono (V : HSp D) {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → Q v) : grpAt V P ≤ grpAt V Q := fun g hg =>
  (mem_grpAt_iff_parts V Q g).2 fun i j =>
    ⟨((mem_grpAt_iff_parts V P g).1 hg i j).1, fun w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => hw (h w h')⟩

theorem cutAt_eq_one (V : HSp D) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : ¬ P v) {g : GA D V} (hg : g ∈ grpAt V P) :
    cutAt V v g = 1 := by
  have h := cutG_left V {v} (one_mem _) (grpAt_mono V (Q := (· ∉ ({v} : Finset (GlobalTheory.FinPl.Pl D))))
    (fun w hw hm => hv (Finset.mem_singleton.1 hm ▸ hw)) hg)
  rwa [one_mul] at h

end Cut

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}



theorem mem_U_iff (hA : A.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    g ∈ A.U j β ↔ g ∈ GfC _ ∧ ∀ v, cutAt _ v g ∈ A.U j β := by
  have ex := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
  constructor
  · intro hg
    obtain ⟨hC, κ, hκ⟩ := (hA.U j hj β g).1 hg
    refine ⟨hC, fun v => (hA.U j hj β _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (cutAt_mem _ v g), ?_⟩⟩
    obtain ⟨x, hx⟩ := ex (cutAt _ v g)
    refine ⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩
    by_cases hw : w = v
    · subst hw
      rw [bc_congr _ _ w hx hκ (compAt_cutAt _ w g)]
      exact (((A.K j hj β).lev.U_eq _).1 κ.2).2 w
    · rw [bc_eq_one _ _ (P := (· ∈ ({v} : Finset _))) (fun h => hw (Finset.mem_singleton.1 h)) (cutAt_mem _ v g) hx]
      exact one_mem _
  · rintro ⟨hC, h⟩
    refine (hA.U j hj β _).2 ⟨hC, ?_⟩
    obtain ⟨x, hx⟩ := ex g
    refine ⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩
    obtain ⟨-, κ, hκ⟩ := (hA.U j hj β _).1 (h w)
    rw [← bc_congr _ _ w hκ hx (compAt_cutAt _ w g)]
    exact (((A.K j hj β).lev.U_eq _).1 κ.2).2 w



theorem mem_of_uloc_le {a' : I.ι} {Ch' : ℕ → Type} {A' : TwDat I l Z u a' Ch'} (hA : A.Is) (hA' : A'.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j)
    (β' : Ch' j) (v : GlobalTheory.FinPl.Pl (I.rec7 l Z)) (hle : (A.K j hj β).lev.Uloc v ≤ (A'.K j hj β').lev.Uloc v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hv : g ∈ GlobalTheory.FinPl.grpAt _ (· ∈ ({v} : Finset _))) (hg : g ∈ A.U j β) :
    g ∈ A'.U j β' := by
  obtain ⟨hC, κ, hκ⟩ := (hA.U j hj β g).1 hg
  refine (hA'.U j hj β' g).2 ⟨hC, ⟨κ.1, ((A'.K j hj β').lev.U_eq _).2 ⟨(((A.K j hj β).lev.U_eq _).1 κ.2).1, fun w => ?_⟩⟩, hκ⟩
  by_cases hw : w = v
  · subst hw
    exact hle ((((A.K j hj β).lev.U_eq _).1 κ.2).2 w)
  · rw [bc_eq_one _ _ (P := (· ∈ ({v} : Finset _))) (fun h => hw (Finset.mem_singleton.1 h)) hv hκ]
    exact one_mem _

end Level

end GlobalTheory.PenLevOff
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLevelComparison

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLevPrime

section Comp



variable {D : D7}

theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add (f := _)]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_congr (v : GlobalTheory.FinPl.Pl D) {y y' : AE D} (h : GlobalTheory.FinPl.compAt D v y = GlobalTheory.FinPl.compAt D v y') :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = Formalism.UG.prV (E := D.host.E) v (toEAf D y') := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  generalize finPart D y' = z' at h ⊢
  refine (prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)
  rw [h]

theorem bc_eq_one_of_off (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : P v)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  subst hn
  have h := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V P g).1 hg i j v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  have e : x.1 i j = toEAf D (Formalism.L2.Theta.mt V g i j) := by rw [hx]; rfl
  rw [e, prV_toEAf_congr v h]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end Comp

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}

theorem exists_splitPt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) : ∃ i, v = (p i).v := by
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  obtain ⟨w, hw, rfl⟩ := (GlobalTheory.NormPlaces.places_dvd_iff (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl
    (l.pr.piT_norm u) hne v).1 hv
  obtain ⟨e, he⟩ := hS.1
  refine ⟨e.symm ⟨w, hw⟩, ?_⟩
  have h := he (e.symm ⟨w, hw⟩)
  rw [e.apply_symm_apply] at h
  exact (GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ h).symm



theorem uloc_le_of_std (hOk : I.Ok) (hP : TC.Pins B X) {a a' : I.ι} {Ch Ch' : ℕ → Type} {A : TwDat I l Z u a Ch}
    {A' : TwDat I l Z u a' Ch'} (hA : A.Is) (hA' : A'.Is)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (J : List ι) (hn : J.Nodup) (hall : ∀ i, i ∈ J) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j) (b' : Ch' j)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ∃ i, v = (p i).v) :
    (A.K j hj b).lev.Uloc v ≤ (A'.K j hj b').lev.Uloc v := by
  intro h hh
  obtain ⟨x, hxU, hxv⟩ : ∃ x ∈ (A.K j hj b).lev.U, Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) x = h := by
    refine ⟨Formalism.UG.P.afsplitU v h 1, ?_, Formalism.UG.P.afsplit_right1 v h 1⟩
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ h 1 ((A.K j hj b).lev.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, Formalism.UG.P.afsplit_right1 v h 1]; exact hh
    · have hxw : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
          Units.val_one, Units.val_one]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [hxw]; exact one_mem _
  obtain ⟨g, hgC, hg⟩ := GlobalTheory.ChartLevRead.exists_finM_GfC _ (rankN (I.rec7 l Z) j hj) ⟨x, (((A.K j hj b).lev.U_eq x).1 hxU).1⟩
  have hgU : g ∈ A.U j b := (hA.U j hj b g).2 ⟨hgC, ⟨x, hxU⟩, hg.symm⟩
  obtain ⟨g', hg', κ', hκ', hκe⟩ := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hS J hn hall j hj b).2 g hgU
  have hst := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a' Ch' A' hA' k ι p β Q L hS J hn hall j hj b').1
  have hprod : (J.map fun i => (β j i).gl (g' i)).prod ∈ A'.U j b' := Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact (hst i _ (hg' i)).1
  obtain ⟨-, y, hy⟩ := (hA'.U j hj b' _).1 hprod
  obtain ⟨z, hz⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl κ'
  have e : x = y.1 * z.1 := by
    apply Units.ext
    have hg2 : finM _ (rankN (I.rec7 l Z) j hj) g = x.1 := hg
    rw [Units.val_mul, hy, hz, ← hg2, hκe]
    exact GlobalTheory.AdForm.StabMove.finM_mul _ _ _ _
  have hz1 := bc_eq_one_of_off _ (rankN (I.rec7 l Z) j hj) (v := v) hv hκ' hz
  rw [← hxv, e, map_mul, hz1, mul_one]
  exact (((A'.K j hj b').lev.U_eq _).1 y.2).2 v

end Level


end GlobalTheory.PenLevPrime
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocLeLevelPrime

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
namespace GlobalTheory.PenLevPrime
section Comp

variable {D : D7}
end Comp
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}
end Level

theorem uloc_le_levelPrime_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v hv
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  exact uloc_le_of_std hW.tr.ok hW.tr.pins.some hJ.is hJ'.is hTr.std a.o.I ha.shape.pre.nodup ha.shape.pre.all j _ _ _ v
    (exists_splitPt hTr.std v hv)
end GlobalTheory.PenLevPrime
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UlocLeLevelPrimeStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_coset_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)), ((B.T u : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  exact @_root_.GlobalTheory.PenLevPrime.uloc_le_levelPrime_alt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutMemU

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
namespace GlobalTheory.PenLevOff
section Cut
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut

variable {D : D7}
end Cut
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}
end Level
end GlobalTheory.PenLevOff
end

theorem GlobalTheory.PenLevOff.uloc_le_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J v → ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hv hv'
  have hjm : j ≤ B.R.m := by omega
  by_cases hTv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · exact _root_.GlobalTheory.T.true_geometry_coset_value_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hTv
  by_cases hb : v ∈ J'.A.bad j
  · rcases hJ'.is.bad_le j hjm v hb with hg | hq
    · exact _root_.GlobalTheory.T.true_geometry_coset_relation_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hg hTv hv hv'
    · exfalso
      obtain ⟨P, hP, hPv⟩ := hq
      obtain ⟨i, hi⟩ := hJ'.surj P ((hW.tq.Q t' P).2 hP)
      exact hv' ⟨i, (((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha haT t' J' hJ').2 i).trans (congrArg _ hi)).trans hPv⟩
  · rw [(J'.A.K j hjm (J'.ι j α')).lev.Uloc_hyp v hb hTv]
    refine ((J.A.K j hjm (J.ι j α)).lev.Uloc_lev v).trans (le_of_eq ?_)
    congr 1
    ext z
    exact ((hJ.is.reads j hjm).lb _ z).trans ((hJ'.is.reads j hjm).lb _ z).symm

theorem GlobalTheory.PenLevOff.cut_mem_U_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j) (Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J p → p ∈ Q) → (∀ p, _root_.GlobalTheory.PenBridge.finitePlaceCondition J' p → p ∈ Q) → ∀ x ∈ J.A.U j (J.ι j α), GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj t J hJ α t' J' hJ' α' Q hQ hQ' x hx
  have hjm : j ≤ B.R.m := by omega
  have hxG : x ∈ GfC _ := ((hJ.is.U j hjm _ x).1 hx).1
  have h1 := GlobalTheory.FinPl.SetCut.cutG_mem_Q _ Q x
  have h2 := GlobalTheory.FinPl.SetCut.cutG_mem_Qc _ Q hxG
  have e := GlobalTheory.FinPl.SetCut.cutG_mul_cutG _ Q x
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.idemQ_mul_self Q) x = g₁ at h1 e
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x = g₂ at h2 e ⊢
  refine (GlobalTheory.PenLevOff.mem_U_iff hJ'.is j hjm _ g₂).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h2, fun v => ?_⟩
  by_cases hv : v ∈ Q
  · rw [GlobalTheory.PenLevOff.cutAt_eq_one _ (P := (· ∉ Q)) (not_not.2 hv) h2]
    exact one_mem _
  · have h4 := ((GlobalTheory.PenLevOff.mem_U_iff hJ.is j hjm _ x).1 hx).2 v
    rw [← e, map_mul, GlobalTheory.PenLevOff.cutAt_eq_one _ (P := (· ∈ Q)) hv h1, one_mul] at h4
    exact GlobalTheory.PenLevOff.mem_of_uloc_le hJ.is hJ'.is j hjm _ _ v
      (_root_.GlobalTheory.PenLevOff.uloc_le_alt W hW u a ha haT j hj t J hJ α t' J' hJ' α' v (fun h => hv (hQ v h)) (fun h => hv (hQ' v h)))
      (GlobalTheory.PenLevOff.cutAt_mem _ v _) h4
end
end
end
