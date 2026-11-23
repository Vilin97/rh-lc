module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GaloisRepDescendsAtRealPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefficientFieldRingOfIntegersThird
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemPartitionLambda
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLaws
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PinOfNTrue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Auxiliary

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameWithLoc

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CenFrame
section Mat
variable {k : Type} [CommRing k] {n n' r t : ℕ}
end Mat
section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Loc
section Lev
variable {D : D7}
end Lev
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end Core
section Main
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Main
end GlobalTheory.CenFrame
namespace GlobalTheory.SerThird
open Formalism.MainNotions.N Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.CenFrame
attribute [local instance] GlobalTheory.TypeRec.factG

theorem cenLoc_third_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (Lc : LocAll (lay0 (Dof x))) : CenLoc (withLoc Lc) (mtL Lc l.mt.M) := by
  intro i
  have h := cen_twisted x.r.Y x.m.z.cG x.m.z.pins.char.base x.m.z.pins.keep x.m.intersectionNumber_baseChange.ok.ok2 (cenRead_state x) l.mt.M l.mt.ad l.mt.mt
    ((withLoc Lc).nd.w i) ((withLoc Lc).nd.w_tw i) ((withLoc Lc).nd.mu i) ((withLoc Lc).nd.mu_w i) ((withLoc Lc).nd.j i)
    ((withLoc Lc).nd.j_range i).1 ((withLoc Lc).nd.j_range i).2
  exact (by with_unfolding_all exact (h :))

theorem tame_coupled_with_loc {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (Lc : LocAll (lay0 (Dof x))) :
    ∀ k v, ∃ κ : IsLocalRing.ResidueField ((withLoc Lc).nd.plOm.1 ((withLoc Lc).naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar ((withLoc Lc).host.g k),
      Formalism.L2.NT.TameCoupled ((withLoc Lc).nd.plOm.1 ((withLoc Lc).naut.plGw k v)) κ ((withLoc Lc).ntypes.tg k v)
        (GlobalTheory.Mem.TypePl.labDat ((withLoc Lc).host.g k)).gen :=
  fun k v => ⟨l.a.A.grp.kv k v, by
    have h := l.a.A.grp.tg_tame k v
    rw [l.a.zeta k] at h
    exact h⟩
end GlobalTheory.SerThird
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdSeriesWithLocalConditions

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CenFrame
section Mat
variable {k : Type} [CommRing k] {n n' r t : ℕ}
end Mat
section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Loc
section Lev
variable {D : D7}
end Lev
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end Core
section Main
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Main
end GlobalTheory.CenFrame
namespace GlobalTheory.SerThird
open Formalism.MainNotions.N Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.CenFrame
attribute [local instance] GlobalTheory.TypeRec.factG

theorem exists_character_choice_with_loc_of_built (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ)
    (L : LocAll (lay0 (Dof x))) (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L) :
    ∃ Q : _root_.GlobalTheory.NPin.CharacterChoiceData hL (withLoc L), Q.M = mtL L l.mt.M := by
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hB
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have key : ∀ (xi : (Dof x).what₂.Tup → HChar (Dof x).host.E) (Q : (Dof x).what₂.places.Pl → Finset (PlE (Dof x).host)),
        MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * xi μ) Q → l.c.tp.xi = xi → l.c.ch.Q = Q →
          MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
      intro xi Q h hx hQ
      subst hx hQ
      exact h
    exact key _ _ l.mt.mt l.c.xi_eq l.c.Q_eq
  let nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := hmt, big := big, L := L, Sp := Sp, Au := Au, ss := ss,
      eq := rfl, pack := rfl }
  have hval : ValLL0 (withLoc L) (cfL L (cfOf x)) :=
    ⟨l.a.val.mu0, l.a.val.eta, l.a.val.chiPsi, l.a.val.del, l.a.val.del'⟩
  obtain ⟨Q, -, -, -, -, h5⟩ := _root_.GlobalTheory.NPin.exists_character_choice_of_nTrue_split hL _ _ _ _ nt hval
    (fun σ σ' h => x.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) l.a.elem.star l.a.elem.int l.a.elem.split
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
  exact ⟨Q, eq_of_heq h5⟩

theorem locComp_of_isRc_classMapD_cenLoc : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  intro hL hP
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l
  refine ⟨fun _ => ∅, fun Lc hB _ => ?_⟩
  obtain ⟨Pn, hM⟩ := _root_.GlobalTheory.SerThird.exists_character_choice_with_loc_of_built hL hP x l _ Lc hB
  exact _root_.UpperTheory.Lit.Dz.compatibleSystemLocalProperty_explicit hP.what₂ hP.green hP.zel hL (withLoc Lc) Pn _ (labTie_withLoc x Lc) (_root_.GlobalTheory.SerThird.tame_coupled_with_loc x l Lc)
    (hM ▸ _root_.GlobalTheory.SerThird.cenLoc_third_alt x l Lc)
end GlobalTheory.SerThird
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.ser_loc_eventually_of_built : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  first | exact @_root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UpperRamificationJointConditionThirdJump

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.JointConditionThird
theorem upper_ramification_joint_condition_third_jump_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalDatumCompatibility D' := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  refine GlobalTheory.DesignBC.jointCond_of_definite _ fun j h1 h2 => ?_
  have h := (w.st x.o.Z).B.toPre.V_posDef j h1 h2
  intro τ
  exact Or.inl (h τ)
end GlobalTheory.HeightCounting.Up.JointConditionThird
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UpperRamificationThirdJumpHolds

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up


theorem upper_ramification_third_jump_holds_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  intro hL hP
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  let T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { l.a.A.wdT with }
  let A' : _root_.GlobalTheory.HeightCounting.AUSideAlt (withLoc L) := { l.a.A.au with }
  have cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (withLoc L) T' := { l.a.cg with }
  have au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (withLoc L) T' A' := fun j h1 h2 π s σ h => l.a.au j h1 h2 π s σ h
  exact _root_.UpperTheory.BaseChangeIdentities.Conclusion1_alt_alt_alt hP.bc hP.what₂.bern hP.gen hP.std hL (withLoc L) T' A' cg au
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.third_member_upper_ramification' : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt | exact _root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemInputsAtThirdPlace

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PtInputsX
theorem inputs_at_third_place_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility →
    AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
    _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedInputs hL D') := by
  intro hL hP hX
  have h := (((_root_.GlobalTheory.T.compatible_system_third_place_linked_data hL hP hX).and (_root_.GlobalTheory.HeightCounting.Up.JointConditionThird.upper_ramification_joint_condition_third_jump_alt hL hP)).and
    (_root_.GlobalTheory.T.third_member_upper_ramification' hL hP)).and ((_root_.GlobalTheory.T.adm8_and_lamUsed_of_geometric_galois_compat hP hX).and (_root_.GlobalTheory.T.ser_loc_eventually_of_built hL hP))
  refine h.trans (StepW.of_all fun K B f T w _ _ hh P x l => ?_)
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h45, h6⟩ := hh
  have h4 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.NRows.LamUsed D' :=
    ⟨fun _ => ∅, fun _ _ _ => (h45 P x).2⟩
  have h5 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SumRepresentations.adm8 D' :=
    ⟨fun _ => ∅, fun _ _ _ => (h45 P x).1⟩
  have e := fun (P₁ P₂ : D7 → Prop) => _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt _ _ _ l.a.A l.mt.M l.c.ch l.c.tp.tup P₁ P₂
  have a := (e _ _).1 (h1 P x l) ((e _ _).1 (h2 P x l) ((e _ _).1 (h3 P x l) ((e _ _).1 h4
    ((e _ _).1 h5 (h6 P x l)))))
  refine (e _ _).2.1 (fun D' hD' hO => ?_) a
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hD'
  obtain ⟨T⟩ := t1 hO
  exact ⟨⟨T, ⟨hO, t2 hO, t3 hO, t4 hO, t5 hO, t6 hO,
    _root_.GlobalTheory.T.galoisRep_descends_at_real_places hP.decay hP.howe hX D' T.P.cf T.P.C T.P.tp T.X⟩⟩⟩
end GlobalTheory.PtInputsX
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eventually_nonempty_inputs_of_level_c :
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
      _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt →
      _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility →
      AllSt fun _ _ _ _ _ _ x =>
        ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
          _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData
            l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
              SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedInputs hL D') :=
  _root_.GlobalTheory.PtInputsX.inputs_at_third_place_alt
end
end
end
end
