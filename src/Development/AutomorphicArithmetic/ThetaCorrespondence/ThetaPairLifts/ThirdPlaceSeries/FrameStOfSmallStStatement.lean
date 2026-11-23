module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HalfAtInRangeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PermStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameStStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtSmallPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharExp

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

theorem pow_of_dvd {G : Type} [Monoid G] {x : G} {n M : ℕ} (h : x ^ n = 1) (hd : n ∣ M) : x ^ M = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_mul, h, one_pow]

theorem prod_pow_eq_one {ι G : Type} [CommMonoid G] (s : Finset ι) (f : ι → G) (M : ℕ) (h : ∀ i ∈ s, f i ^ M = 1) :
    (∏ i ∈ s, f i) ^ M = 1 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one h

theorem residue_char_pow {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) {LL : Type} [Monoid LL]
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* LL) (u : (Formalism.L2.DIV.kP PP)ˣ) : χ u ^ Nat.card (Formalism.L2.DIV.kP PP)ˣ = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem card_units_pos {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) : 0 < Nat.card (Formalism.L2.DIV.kP PP)ˣ := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact Nat.card_pos


open Classical in
def expOf {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : ℕ :=
  ∏ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ

theorem expOf_pos {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : 0 < expOf L :=
  Finset.prod_pos fun PP _ => card_units_pos PP

open Classical in
theorem levFn_flag1_pow {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    Formalism.L2.DIV.levFn β (flag1L L) x ^ expOf L = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    Formalism.IndefR.Lev.subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1, one_mul, mul_pow]
  have hd : ∀ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ ∣ expOf L := fun PP hP =>
    Finset.dvd_prod_of_mem (fun PP => Nat.card (Formalism.L2.DIV.kP PP)ˣ) hP
  rw [prod_pow_eq_one _ _ _ ?_, prod_pow_eq_one _ _ _ ?_, one_mul]
  · intro PP hP
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_right _ hP))
  · intro PP hP
    refine prod_pow_eq_one _ _ _ fun c _ => ?_
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_left _ hP))

theorem levEnv_chi_pow : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), (levEnv V β L).χ k ^ expOf L = 1 := by
  intro D V β L k
  exact levFn_flag1_pow V β L _

end GlobalTheory.LevelCharExp

end

namespace GlobalTheory.LevelCharExp

end GlobalTheory.LevelCharExp
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiAtInRange

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevelCharExp
open Formalism.BasicNotions.TH Formalism.IndefR.Lev
end GlobalTheory.LevelCharExp
end
namespace GlobalTheory.LevelCharExp
theorem chiAt_inRange_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → ChiAt p j w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ j P W _ _ w _ _ _ => ?_
  refine ⟨expOf (p.R.datVt j (p.R.mu w)), expOf_pos _, fun κ => ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg Units.val (levEnv_chi_pow _ _ _ κ)
end GlobalTheory.LevelCharExp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiAtInRangeStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.chiAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → ChiAt p j w := by
  first | exact @_root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt | exact _root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt | (intros; apply _root_.GlobalTheory.LevelCharExp.chiAt_inRange_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfSmallStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

theorem _root_.GlobalTheory.T.readsAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => SmallAt p j P w → ReadsAt p j P W w := by
  first | exact @_root_.GlobalTheory.FrameRead.reads_of_small_alt | exact _root_.GlobalTheory.FrameRead.reads_of_small_alt | (intros; apply _root_.GlobalTheory.FrameRead.reads_of_small_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameStOfSmallSt

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameOf
end GlobalTheory.FrameOf
namespace GlobalTheory.FrameOf
theorem inRange_and_alt {Q1 Q2 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i)
      (_ : Fin (Fm.D x i).R.m) (_ : Par) (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop}
    (h1 : _root_.GlobalTheory.ExpTie.InRangeAlt Q1) (h2 : _root_.GlobalTheory.ExpTie.InRangeAlt Q2) :
    _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x hx i p j P W w => Q1 Fm x hx i p j P W w ∧ Q2 Fm x hx i p j P W w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt at h1 h2 ⊢
  refine Closed.imp (Closed.and h1 h2) fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and h.1 h.2
  exact ⟨x0, fun x hx hle i p hp hM j P W hD hN w hw hR =>
    ⟨(hx0 x hx hle i p hp).1 hM j P W hD hN w hw hR, (hx0 x hx hle i p hp).2 hM j P W hD hN w hw hR⟩⟩
theorem inRange_of_dict_imp {Q1 Q2 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i)
      (_ : Fin (Fm.D x i).R.m) (_ : Par) (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop}
    (h1 : _root_.GlobalTheory.ExpTie.InRangeAlt Q1) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i)
      (j : Fin (Fm.D x i).R.m) (P : Par) (W : Wts (Fm.D x i).what₂.Tau) (w : HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL)),
      Dict (Fm.L x i) j P W → Q1 Fm x hx i p j P W w → Q2 Fm x hx i p j P W w) : _root_.GlobalTheory.ExpTie.InRangeAlt Q2 := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt at h1 ⊢
  refine Closed.imp h1 fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hle i p hp hM j P W hD hN w hw hR => f Fm x hx i p j P W w hD (hx0 x hx hle i p hp hM j P W hD hN w hw hR)⟩
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
theorem frameSt_of_smallSt' : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.ExpTie.FrameStatement' := by
  intro hS
  have h := _root_.GlobalTheory.FrameOf.inRange_and_alt hS (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.inRange_halfAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.inRange_kapAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.chiAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.tame_at_of_small_at
    (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.permAt_of_smallAt (_root_.GlobalTheory.FrameOf.inRange_and_alt _root_.GlobalTheory.T.commAt_of_smallAt_in_range _root_.GlobalTheory.T.readsAt_of_smallAt))))))
  refine _root_.GlobalTheory.FrameOf.inRange_of_dict_imp h fun Fm x hx i p j P W w hD hq => ?_
  obtain ⟨hs, hh, hk, hc, ht, hp, hcm, hr⟩ := hq
  exact frameAt_of p j P W w hD.Nr (hh hs) (hk hs) (hc hs) (ht hs) (hp hs) (hcm hs) (hr hs)
end GlobalTheory.FrameOf
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameStOfSmallStStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.frame_statement_of_small_statement : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.ExpTie.FrameStatement' := by
  first | exact @_root_.GlobalTheory.FrameOf.frameSt_of_smallSt' | exact _root_.GlobalTheory.FrameOf.frameSt_of_smallSt' | (intros; apply _root_.GlobalTheory.FrameOf.frameSt_of_smallSt' <;> assumption)
end
end
end
