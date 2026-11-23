module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.JointConditionOfConstituentConditionSplit
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualCharpolyEq

section

@[expose] public section



section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
end Formalism.MainNotions.N
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
theorem residual_charpoly_eq_alt_alt (hC : GlobalTheory.TwSys.Cheb) (D : D7) (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep)
    (x π : D.nd.X i) (ρx ρ0 : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (hx : ∃ e, IsDecomp (t := D.R.t) (rep x) ρx (D.nd.chi i) e)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0)
    (h0 : ∃ e, IsDecomp (t := D.R.t) r0 ρ0 (D.nd.chi i) e) (g : GE D.nd) :
    ((mat ρx g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
      ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly := by
  classical
  have hG3 := (_root_.UpperTheory.GalS.g3' ((h32 i).2.2 rep hr).2.2.1).2 x π g
  obtain ⟨ex, hex⟩ := hx
  obtain ⟨e0, he0⟩ := h0
  have dx := charpoly_of_decomp D i rep (fun _ => ρx) x ⟨ex, hex⟩ g
  have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
  have hc := charpoly_eq_of_isHeckeGalois hC D i rep hr π r0 hr0 g
  set res := IsLocalRing.residue (D.nd.O i)
  set P : (D.nd.O i)[X] := ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))
  have hP : (P.map res) ≠ 0 := by
    apply Polynomial.Monic.ne_zero
    apply Polynomial.Monic.map
    exact Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C _
  have e1 : ((mat ρx g).map res).charpoly * P.map res = ((mat ρ0 g).map res).charpoly * P.map res := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, ← Polynomial.map_mul, ← Polynomial.map_mul]
    have ex' : (rO D.nd i rep x g).charpoly = (mat ρx g).charpoly * P := dx
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly * P := d0
    rw [← ex', ← e0', ← hc, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
    exact hG3
  exact mul_right_cancel₀ hP e1
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfLive

section

@[expose] public section



section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
end Formalism.MainNotions.N
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
theorem setting_of_live_alt_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
      GoodR D.nd i rep ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i) := by
  intro hC D h32 hS i hZ hL
  classical
  obtain ⟨rep, hr⟩ := (h32 i).1.2
  have hG1 := ((h32 i).2.2 rep hr).1
  have hG3 := _root_.UpperTheory.GalS.g3' ((h32 i).2.2 rep hr).2.2.1
  have hJ := UpperTheory.GalS.jointCondition_of_constituentCondition_split D i rep hr (hG3.1 (Or.inr hL)) (hS i)
  let ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) := fun x =>
    if hx : x ∈ D.nd.Z i then Classical.choose (hZ x hx (rep x) (hr x)) else 1
  have hρ : ∀ x ∈ D.nd.Z i, ∃ e, IsDecomp (t := D.R.t) (rep x) (ρ x) (D.nd.chi i) e := by
    intro x hx
    have := Classical.choose_spec (hZ x hx (rep x) (hr x))
    simp only [ρ, dif_pos hx]
    exact this
  obtain ⟨π, hπ, r0, ρ0, hr0, h0, habs⟩ := hL
  refine ⟨rep, ρ, hr, D.nd.T_local i, D.nd.T_sep i, fun x => ?_, fun h d => ?_,
    hJ, hG3.2, hρ, fun x hx => ?_⟩
  · have hss := (hr x).2.1
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W fun g v hv => hW g v hv
    exact ⟨W', fun g v hv => h1 g v hv, h2⟩
  · obtain ⟨f, hf⟩ := hG1 h d
    have : (fun x => (mat (rep x) h).charpolyRev.coeff d) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [this]
    exact f.2
  · have hpos := pos_of_absIrrSub _ habs
    haveI : Nonempty (Fin D.R.r) := ⟨⟨0, hpos⟩⟩
    refine absIrrSub_of_span_eq_top hpos _ ?_
    refine span_eq_top_of_trace_eq _ (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0) (fun g => ?_)
      (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
    rw [mat_mapRep, mat_mapRep, Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
      _root_.GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.residual_charpoly_eq_alt_alt hC D h32 i rep hr x π (ρ x) ρ0 (hρ x hx) r0 hr0 h0 g]
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OChoose

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
  GlobalTheory.EtaJoin GlobalTheory.CoefDuty
namespace GlobalTheory.OChoose
theorem oChoose_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ S : Finset ℂ, Chosen D.nd D.naut i ↑S := by
  intro hC D hP hO i hZ hL
  classical
  obtain ⟨rep, ρ, hG, hS⟩ := _root_.GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.setting_of_live_alt_alt hC D hP hO i hZ hL
  obtain ⟨g0, hg0⟩ := exists_wild_inertia_cyclotomic_generator D i
  have hcont : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.RepCont D.nd i rep := fun x => (hG x).1
  have ha := (GlobalTheory.ConsExists.consExist D.nd i rep ρ (D.nd.O i) (D.nd.T i) rep ρ (D.nd.chi i) hcont
    (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.isEnlargement_self D.nd i rep ρ) hS).1
  have hch : ∀ π : D.nd.Z i, ∃ q : (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) ×
      (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) ×
      (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)),
      GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice D.R.t (D.nd.T i) rep ρ (D.nd.chi i) π g0 0 q.1 q.2.1 q.2.2 := fun π => by
    obtain ⟨eB, e1, X0, h⟩ := ha π π.2 g0 hg0.1 0
    exact ⟨(eB, e1, X0), h⟩
  choose q hq using hch
  refine ⟨Finset.univ.biUnion fun π : D.nd.Z i => Finset.univ.biUnion fun x : D.nd.X i =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol ((q π).1 x) ((q π).2.2 x)).map (iotaO D.nd D.naut i)).roots.toFinset,
    rep, ρ, hG, hS, fun π hπ => ?_⟩
  refine ⟨g0, 0, (q ⟨π, hπ⟩).1, (q ⟨π, hπ⟩).2.1, (q ⟨π, hπ⟩).2.2, hg0, hq ⟨π, hπ⟩, fun x => ?_⟩
  obtain ⟨hm, hd⟩ := blockPol_iota D i hS (hq ⟨π, hπ⟩) x
  obtain ⟨α, hα, he⟩ := exists_fin_roots hm hd
  refine ⟨α, fun c => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨π, hπ⟩, Finset.mem_univ _,
    Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Multiset.mem_toFinset.2 (hα c)⟩⟩), he⟩
end GlobalTheory.OChoose
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OChooseStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_finset_chosen_of_cheb_oSplit : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, ZDecomp D.nd i → Live D.nd i → ∃ S : Finset ℂ, Chosen D.nd D.naut i ↑S := by
  first | exact @_root_.GlobalTheory.OChoose.oChoose_alt | exact _root_.GlobalTheory.OChoose.oChoose_alt | (intros; apply _root_.GlobalTheory.OChoose.oChoose_alt <;> assumption)
end
end
end
