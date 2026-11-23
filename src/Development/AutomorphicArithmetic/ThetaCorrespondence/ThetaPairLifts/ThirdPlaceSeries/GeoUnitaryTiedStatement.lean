module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
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
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarily
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupActionStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteUnitaryAction

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open scoped InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

def IsUnitaryRep {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H) : Prop :=
  ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

def pairAt (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

def classSumAt (f f' : S.Forms) : ℂ :=
  ∑ c, ((S.wt c : ℂ))⁻¹ * pairAt S σ ((f : S.Cl → S.V) c) ((f' : S.Cl → S.V) c)

def IsUnitaryAt {G : Type} [Group G] (r : Representation K G S.Forms) : Prop :=
  ∀ (g : G) (f f' : S.Forms), classSumAt S σ (r g f) (r g f') = classSumAt S σ f f'

end ClassSum

section Statement

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}

structure DefiniteUnitary (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop where

  what₂ : ∀ (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtildeCSD t) σ (A.leftGroupActionRight t)

  lifts : ∀ (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtCSD i t) σ (A.leftGroupActionLift i t)

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure ActsUnitarily (R : RealDat D A Ks) : Prop where

  what₂ : IsUnitaryRep R.gE

  formsW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsUnitaryRep (R.gW i σ)

  definite : DefiniteUnitary A

end Statement

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupActionStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_goodRows_finiteGroup_action : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HE → R.models_gE → R.models_ν0 → ∀ g x, ‖R.gE g x‖ = ‖x‖ := by
  first | exact @GlobalTheory.norm_gE_rows | exact GlobalTheory.norm_gE_rows | (intros; apply GlobalTheory.norm_gE_rows <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ActsUnitarilyOfClauses

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction
open scoped ComplexOrder

namespace GlobalTheory.UnitaryActionTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem actsUnitarily_of_clauses (R : RealDat D A Ks) (hE : R.models_HE) (gE : R.models_gE) (h0 : R.models_ν0)
    (hW : R.models_HW) (gW : R.models_gW) (hν : R.models_νW) (ht : R.fam_tie) (hX : R.models_cX) (hV : R.models_cV) :
    ActsUnitarily R :=
  have h := GlobalTheory.FiniteGroupUnitary.definiteUnitary R ht hX hV
  ⟨GlobalTheory.FiniteGroupUnitary.isUnitaryRep_of_norm _ (GlobalTheory.T.norm_goodRows_finiteGroup_action R hE gE h0),
    fun i σ => GlobalTheory.FiniteGroupUnitary.isUnitaryRep_of_norm _ (GlobalTheory.T.norm_liftForms_finiteGroup_action R hW gW hν i σ),
    fun t σ => h.1 t σ, fun i t σ => h.2 i t σ⟩

theorem geometric_unitary (R : RealDat D A Ks) (hU : R.LUnif) (hW : R.models_HW) (gW : R.models_gW) (h : ActsUnitarily R)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (x y : Fin (R.nW i) → D.what₂.LL) :
    inner ℂ ((R.FW i).j σ ((R.FW i).ρ g x)) ((R.FW i).j σ ((R.FW i).ρ g y)) = inner ℂ ((R.FW i).j σ x) ((R.FW i).j σ y) := by
  have e : ∀ z, (R.FW i).j σ ((R.FW i).ρ g z) =
      σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i σ g ((R.FW i).j σ z) := fun z =>
    (hW i σ).1 (by rw [(hU i σ).2.2, map_smul, gW])
  have n : ‖σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G)
      (by rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one, map_one])
      Fintype.card_ne_zero
  rw [e, e, inner_smul_left, inner_smul_right, h.formsW, ← mul_assoc, Complex.conj_mul', n]
  simp

end GlobalTheory.UnitaryActionTest
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoUnitaryTied

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem geoUnitary_tied_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hp _ i σ g x y
  have hm := p.charW.base.models
  exact GlobalTheory.UnitaryActionTest.geometric_unitary p.R.toRealDat hp.prim.unif hm.HW hm.gW
    (GlobalTheory.UnitaryActionTest.actsUnitarily_of_clauses p.R.toRealDat hm.HE hm.gE hm.ν0 hm.HW hm.gW hm.νW
      p.charW.base.fam.tie hm.cX hm.cV) i _ g x y
end GlobalTheory.CovTop
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoUnitaryTiedStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.row_inner_product_invariant_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  first | exact @_root_.GlobalTheory.CovTop.geoUnitary_tied_alt | exact _root_.GlobalTheory.CovTop.geoUnitary_tied_alt | (intros; apply _root_.GlobalTheory.CovTop.geoUnitary_tied_alt <;> assumption)
end
end
end
