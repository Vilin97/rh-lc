module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqTie
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayerStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqThF

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Kernel1

variable {D : D7} {S T : HSp D}

end Kernel1

section CoefV

variable {D : D7} {V : HSp D} (c : CoefA V)

theorem ext_g0Act (hc : c.Is) {Q : Subgroup (Bridge.Gf V)} (ch : Q →* ℂˣ) (q : Q) (κ : GA D V) (hκ : κ ∈ GfC V)
    (hκq : (finHom V).rangeRestrict κ = q) (F : Bridge.Gf V → c.W) (h : GA D V) :
    c.ext (Bridge.g0Act ch q F) h = (((ch q)⁻¹ : ℂˣ) : ℂ) • c.ext F (h * κ) := by
  have e : c.ext (Bridge.g0Act ch q F) h =
      c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q)) := rfl
  have e2 : c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q)) =
      (((ch q)⁻¹ : ℂˣ) : ℂ) • c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q)) := LinearMap.map_smul _ _ _
  have e6 : c.ext F (h * κ) = c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q)) := hκq ▸ coefExt_mul c hc F h κ hκ
  exact e.trans (e2.trans (congrArg _ e6.symm))

end CoefV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem mem_Q_of_liftV (i : Fin D.R.m) (t : T) (g : G) {κ0 : GA D (Vc D i)}
    (hκ0 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ0) :
    (finHom (Vc D i)).rangeRestrict κ0 ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
  show Formalism.UG.bc (swapAE D) (finHom (Vc D i) κ0) ∈ lev D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))
  rw [← finE_eq]
  exact ⟨hκ0.2.1, Subgroup.mem_top _⟩

theorem red_of_liftV (hred : R.grp_red_L) (i : Fin D.R.m) (t : T) (g : G) {κ0 : GA D (Vc D i)}
    (hκ0 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ0) :
    (R.B.L i t).act_tie.red (⟨_, mem_Q_of_liftV R i t g hκ0⟩ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) = g := by
  apply R.eG.injective
  rw [hred i t ⟨_, mem_Q_of_liftV R i t g hκ0⟩]
  exact hκ0.2.2

theorem jV_act (hM : R.IsModels) (i : Fin D.R.m) (t : T) (g : G) (x : A.fam.amb.FL i t)
    (q0 : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hred0 : (R.B.L i t).act_tie.red q0 = g) :
    (R.HV i t).e (R.jV i t (A.fam.amb.opL i t (Sum.inr g) x)) =
      Bridge.g0Act (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q0 ((R.HV i t).e (R.jV i t x)) := by
  have hext := (R.B.L i t).act_tie.act_eq g q0 hred0 x
  exact (hM.jV i t _).trans (hext.trans
    (congrArg (Bridge.g0Act (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q0) (hM.jV i t x).symm))

theorem extV_apply (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (h : GA D (Vc D i)) :
    R.extV i t y h = (R.cV i).ext ((R.HV i t).e y) h := rfl

end Formalism.IndefR.Eqv.Act

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActionReadAtMember

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenLocAt

section Gen

open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)

theorem liftForm_lvlAct (hok : A3.fam3.Ok3 1) (k : Fin D.R.m) (s : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) :
    (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s (lvlAct F k s a x) : A3.A.fam.amb.FL k s) =
      ∑ g : G, a.coeff g • A3.A.fam.amb.opL k s (Sum.inr g) (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hok.ok2.conj _ ((hok.ok2.lifts k s).hpos _) _ (hok.ok2.lifts k s).act _ _ a ha x


variable (R) in
theorem jV_sum (k : Fin D.R.m) (s : T) (c : G → D.what₂.LL) (v : G → A3.A.fam.amb.FL k s) :
    R.jV k s (∑ g, c g • v g) = ∑ g, D.what₂.embLL (c g) • R.jV k s (v g) :=
  (map_sum (R.jV k s) (fun g => c g • v g) Finset.univ).trans
    (Finset.sum_congr rfl fun g _ => (R.jV k s).map_smulₛₗ (c g) (v g))


variable (R) in
theorem extV_sum (k : Fin D.R.m) (s : T) (c : G → ℂ) (w : G → (R.HV k s).H) (y : GA D (Vc D k)) :
    R.extV k s (∑ g, c g • w g) y = ∑ g, c g • R.extV k s (w g) y := by
  have e := map_sum (R.extV k s) (fun g => c g • w g) Finset.univ
  refine (congrFun e y).trans ((Finset.sum_apply y Finset.univ _).trans (Finset.sum_congr rfl fun g _ => ?_))
  exact congrFun ((R.extV k s).map_smul (c g) (w g)) y

theorem extV_act {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks) (hM : R.IsModels) (hred : R.grp_red_L)
    (k : Fin D.R.m) (s : T) (g : G) {κ : GA D (Vc D k)} (hκ : IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) κ)
    (v : A.fam.amb.FL k s) (y : GA D (Vc D k)) :
    R.extV k s (R.jV k s (A.fam.amb.opL k s (Sum.inr g) v)) y =
      (levChi (Vc D k) (R.βV k) (flagL (R.datVt k s)) κ)⁻¹ • R.extV k s (R.jV k s v) (y * κ) := by
  have e1 := Formalism.IndefR.Eqv.Act.jV_act R hM k s g v _ (Formalism.IndefR.Eqv.Act.red_of_liftV R hred k s g hκ)
  have e2 := Formalism.IndefR.Eqv.Act.ext_g0Act (R.cV k) (hM.cV k) (levEnv (Vc D k) (R.βV k) (R.datVt k s)).ch
    ⟨_, Formalism.IndefR.Eqv.Act.mem_Q_of_liftV R k s g hκ⟩ κ hκ.1 rfl ((R.HV k s).e (R.jV k s v)) y
  have e3 := congrArg (fun f => (R.cV k).ext f y) e1
  have hch : ((((levEnv (Vc D k) (R.βV k) (R.datVt k s)).ch ⟨_, Formalism.IndefR.Eqv.Act.mem_Q_of_liftV R k s g hκ⟩)⁻¹ : ℂˣ) : ℂ) =
      (levChi (Vc D k) (R.βV k) (flagL (R.datVt k s)) κ)⁻¹ := Units.val_inv_eq_inv_val _
  refine (Formalism.IndefR.Eqv.Act.extV_apply R k s _ y).trans (e3.trans (e2.trans ?_))
  exact congrArg₂ (fun (c : ℂ) (w : (R.cV k).W) => c • w) hch (Formalism.IndefR.Eqv.Act.extV_apply R k s _ (y * κ)).symm

theorem actRead_of (hM : R.toRealDat.IsModels) (hred : R.toRealDat.grp_red_L) (hok : A3.fam3.Ok3 1) : ActRead Y := by
  intro s h k a ha κ hκ x y
  have hr : ∀ x', adForm Y (Y.tup s) h k (ratForm Y k s x') =
      R.extV k s (R.jV k s (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x')) := fun x' => Y.mtRead k s h x'
  have e1 : R.jV k s (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s (lvlAct F k s a x)) =
      ∑ g : G, D.what₂.embLL (a.coeff g) •
        R.jV k s (A3.A.fam.amb.opL k s (Sum.inr g) (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x)) :=
    (congrArg (R.jV k s) (liftForm_lvlAct hok k s a ha x)).trans (jV_sum R k s _ _)
  refine (congrFun (hr _) y).trans ((congrFun (congrArg (R.extV k s) e1) y).trans
    ((extV_sum R k s _ _ y).trans (Finset.sum_congr rfl fun g _ => ?_)))
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) (extV_act R.toRealDat hM hred k s g (hκ g) _ y)).trans ?_
  exact (smul_smul _ _ _).trans (congrArg _ (congrFun (hr x) (y * κ g)).symm)

end Gen

end GlobalTheory.CenLocAt

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActReadAt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.CenLocAt
section Gen
open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Lev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)
end Gen
theorem actRead_at_mem_of_recT : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ =>
    actRead_of t.r.Y t.r.z.pins.char.base.models t.r.z.pins.char.base.grp.red_L t.r.intersectionNumber_baseChange.ok
end GlobalTheory.CenLocAt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActReadAtStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.actRead_at_member_of_recT : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y := by
  first | exact @_root_.GlobalTheory.CenLocAt.actRead_at_mem_of_recT | exact _root_.GlobalTheory.CenLocAt.actRead_at_mem_of_recT | (intros; apply _root_.GlobalTheory.CenLocAt.actRead_at_mem_of_recT <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMember

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenRatAt

theorem transfer {K G Pl0 V : Type} [Field K] [NumberField K] [StarRing K] [Group G] [Fintype G]
    (B B' : Formalism.L2.DIV.BlockDat K G Pl0) (hB : B = B') (ℓ : Formalism.L2.DIV.Lvl K G) (Q : V → V → Prop)
    (e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) → V) (e' : (Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) → V)
    (h : GlobalTheory.Mem.Top.Bl.SameOn e e') (a : MonoidAlgebra K G)
    (H : ∀ x, Q (e x) (e ((B.S.lvlOp B.r ℓ.P ℓ.ψ a).mulVec x))) (x' : Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) :
    Q (e' x') (e' ((B'.S.lvlOp B'.r ℓ.P ℓ.ψ a).mulVec x')) := by
  subst hB
  have he : e = e' := funext fun x => h.2 x x fun i i' hi => congrArg x (Fin.ext hi)
  subst he
  exact H x'

theorem famR_L_eq (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U U' : Set I.ι)
    (Xg : Finset (R3.Gc X.B px → X.B.LL)) (tr tr' : R3.TrI X.B px) (k : Fin X.toD7.R.m) (s : R3.TupU I U) (s' : R3.TupU I U')
    (h : s.1 = s'.1) : (R3.famR X I hX U Xg tr).A.fam.L k s = (R3.famR X I hX U' Xg tr').A.fam.L k s' := by
  obtain ⟨τ, hτ⟩ := s
  obtain ⟨τ', hτ'⟩ := s'
  cases h
  rfl

section Main

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}



theorem cenRat_of (t : RowsT K w Z Wt p0) (r : RXs t) : GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  intro s k z a ha x
  have h5 : (tAll w.I (t.r.Y.tup s)).1 = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have h3 := (r.all.cen (t.r.Y.tup s) z a ha).2.2 k
  exact transfer _ _ (famR_L_eq (w.st Z) w.I t.hX _ _ _ _ _ k _ _ h5) _
    (fun u v => (w.st Z).toD7.ntypes.cenMt (t.r.Y.tup s) ((k : ℕ) + 1) z ((w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) u) =
      (w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) v)
    (r.all.eMt k (t.r.Y.tup s)) (t.r.Y.eMt k s) (r.eMt_use k s) a h3 x

end Main

end GlobalTheory.CenRatAt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenRatAt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.CenRatAt
section Main
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}
end Main
theorem cenRat_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ hR _ => hR.elim fun r => cenRat_of t r
end GlobalTheory.CenRatAt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenRatAtStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.cenRat_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  first | exact @_root_.GlobalTheory.CenRatAt.cenRat_at_alt | exact _root_.GlobalTheory.CenRatAt.cenRat_at_alt | (intros; apply _root_.GlobalTheory.CenRatAt.cenRat_at_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAd

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenLocAt
theorem exists_ad_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ c => Nonempty (MtAd t.r.Y c.a.all.gal.mt) :=
  GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE _ _ => hE.elim fun e => ⟨_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.ad e⟩

theorem cenLoc_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := fun hL =>
  _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.cenRat_at_members hL) (_root_.GlobalTheory.T.actRead_at_member_of_recT hL)) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members hL) (_root_.GlobalTheory.CenLocAt.exists_ad_alt hL)))
    fun _ _ _ _ _ _ _ _ t _ _ _ h => h.2.2.elim fun ad => cenLoc_of t.r.Y t.r.z.cG _ ad h.1.1 h.1.2 (h.2.1 ad)
end GlobalTheory.CenLocAt
end
end
end
