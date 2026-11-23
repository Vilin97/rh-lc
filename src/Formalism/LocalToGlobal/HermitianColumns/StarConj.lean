module

public import Formalism.LocalToGlobal.HermitianColumns.CompletionIntegersIff
public import Formalism.LocalToGlobal.HermitianColumns.ClsNonempty
public import Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter
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
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- Source module: Formalism.LocalToGlobal.HermitianColumns.ColsHerm

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GTied (D : D7) (H : HermTied D) : Type :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    GLevTie (H.lev0 u) (D.gat u w hg)

structure FullTied (D : D7) extends AllTied D where
  levelZeroCompatibility : Lev0Tied D base.toHermCols atT
  g : GTied D base
  ad : AdTied D base.toHermCols atT
  cof : CofTied D base.toHermCols atT
  piG : PiGConst D base.toHermCols atT levelZeroCompatibility
  stabMap : StabMapTied D base.toHermCols atT
  fvI : FvStepTied D base.toHermCols atT
  relDet : RelativeDeterminantCompatible D base
  std : StdTied D
  vpos : PositiveVolumeCompatible D
  baseL : BaseTied D base.toHermCols atT

structure ColsHerm (D : D7) where
  base : HermCols D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  levelZeroCompatibility : Lev0Tied D base atT
  ad : AdTied D base atT
  cof : CofTied D base atT
  piG : PiGConst D base atT levelZeroCompatibility
  stabMap : StabMapTied D base atT
  fvI : FvStepTied D base atT
  std : StdTied D
  baseL : BaseTied D base atT

def FullTied.cols {D : D7} (X : FullTied D) : ColsHerm D where
  base := X.base.toHermCols
  atT := X.atT
  levelZeroCompatibility := X.levelZeroCompatibility
  ad := X.ad
  cof := X.cof
  piG := X.piG
  stabMap := X.stabMap
  fvI := X.fvI
  std := X.std
  baseL := X.baseL

end Formalism.L2.Herm

end
end
end

-- Source module: Formalism.LocalToGlobal.HermitianColumns.StarConj

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_conj {D : D7} (x : D.host.E) : star x = D.host.conj x := bridge_star_holds D.R D.host x

def toErrX {D : D7} (X : FullTied D) : ErrX D where
  piG := (X.levelZeroCompatibility D.u₀).piG
  piG_K := (X.levelZeroCompatibility D.u₀).piG_K
  piG_norm := fun i => by rw [← star_conj]; exact (X.levelZeroCompatibility D.u₀).piG_norm i
  piT := fun u => (X.atT u).piU
  piT_K := fun u => (X.atT u).piU_K
  piT_norm := fun u => (X.atT u).piU_norm
  piT_cong := fun u => (X.atT u).piU_cong
  vPl := fun u v => (X.base.vT u v).1
  vPl_inj := fun u a b h => (X.base.vT u).injective (Subtype.ext h)
  norm_mem_place_ideal := fun u v => (X.base.vT u v).2

def GroupCompatibleAtPlaces (D : D7) (H : HermTied D) (G : GTied D H) (Gt : GatTies D) : Prop :=
  ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
    x ∈ ((G u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w
        (tauLL D (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap D.host.F D.host.E (x : D.host.F)))

def GIwTied {D : D7} (H : HermTied D) (G : GTied D H) {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Formalism.MainNotions.G.Fills (D.gat u w hg)}
    {Lv : Formalism.MainNotions.G.Levels Fl} {Ch : Formalism.MainNotions.G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w hg Ch) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (x : D.host.E),
    (G u w hg).eQ v _ rfl (Kp.iw 0 v x) =
      ((G u w hg).spl _ ((G u w hg).pl v).2
        (inclE (F := D.host.F) (((G u w hg).pl v).1.adicCompletion D.host.F) x)).1

def GIwPos {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Formalism.MainNotions.G.Fills (D.gat u w hg)}
    {Lv : Formalism.MainNotions.G.Levels Fl} {Ch : Formalism.MainNotions.G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w hg Ch) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) (Kp.iw 0 v x)) =
      c.embW u w hg (tauLL D (Gt.gat_pos u w hg ⟨v, s⟩) (if s.val % 2 = 1 then D.host.conj x else x))

structure JoinTied {D : D7} (X : FullTied D) (lev : LevelData D) (eX : ErrX D) (Gt : GatTies D) : Prop where
  lev_eq : lev = X.base.lev0
  errX_eq : eX = toErrX X
  gpl : GroupCompatibleAtPlaces D X.base X.g Gt

structure ExtraTied {D : D7} (X : FullTied D) {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    (ex : Extra D L hT Gi Gl K Y cX) : Prop where
  join : JoinTied X ex.lev ex.errX hT
  iw : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    GIwTied X.base X.g u w h (ex.ker u w h)
  iw_pos : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    GIwPos u w h (ex.ker u w h)

end Formalism.L2.Herm

end
end
end
