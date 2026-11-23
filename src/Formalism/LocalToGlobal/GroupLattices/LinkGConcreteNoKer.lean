module

public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleFamilyNoKernel
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
public import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat
public import Formalism.SharpRestriction.GrowthBounds.JointsLit
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
public import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite

-- Source module: Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescOfValRat

section

@[expose] public section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions

variable {D : D7} (c : LatCmp D)

theorem yvRat (h : ValRat c) : Formalism.MainNotions.G.Joints.Lit.YvRat c :=
  fun u w hg v => yvRat_of_valRat c h u w hg v

theorem npDesc_of_valRat {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (hv : c.VramDef Y) (h : ValRat c) : c.NPDesc X Y K :=
  Formalism.MainNotions.G.Joints.Lit.NPDesc_of c hT X Y K hv (yvRat c h)

end Formalism.L2.G.Cmp
end
end

-- Source module: Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescFOfValRatF

section

@[expose] public section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

def ValRatF {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => ∀ hx : Fm.x1 < x, ValRat (Fm.ex x hx i).cmp

theorem npDescF_of_valRatF {eps : ℝ} (Fm : FamP eps) (h : ValRatF Fm) : NPDescF Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx i hx1 => ?_⟩
  refine npDesc_of_valRat _ (Fm.gatT x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK ?_ (hx0 x hx i hx1)
  exact (Fm.ex x hx1 i).lat.vram

theorem CmpTied.valRat {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D}
    {c : LatCmp D} (K : CmpTied D X T Gt c) : ValRat c := by
  intro u w hg x i L hL
  exact ⟨_, ((K.tie u w hg).val_cmp x i L hL).symm⟩

end Formalism.L2.G.Cmp
end
end

-- Source module: Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer

section

@[expose] public section

noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdSubF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : Ev Fm fun x i => Joints.StdSubAt (Fm.D x i) := by
  obtain ⟨x0, h0⟩ := h.and (Ev.x1 Fm)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨ht, hx1⟩ := h0 x hx i
  obtain ⟨G⟩ := ht hx1
  exact stdSubAt_of_ring _ G.ring

theorem gatEF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i) := by
  obtain ⟨x0, h0⟩ := h.and (Ev.x1 Fm)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨ht, hx1⟩ := h0 x hx i
  obtain ⟨G⟩ := ht hx1
  exact gatE_of_gatIs _ G.herm.lev0
    (fun u => Triv.trivStabU (G.herm.lev0 u) (Fm.D x i).host.g_prime (Fm.D x i).host.g_ne) G.gat

theorem npDescF_of_tied {eps : ℝ} (Fm : FamP eps) (h : GroupCompatibilityFamily Fm) : NPDescF Fm := by
  refine Cmp.npDescF_of_valRatF Fm ?_
  obtain ⟨x0, h0⟩ := h
  exact ⟨x0, fun x hx i hx1 => by
    obtain ⟨G⟩ := h0 x hx i hx1
    exact Cmp.CmpTied.valRat G.cmp⟩

theorem linkG_concrete_noKer (𝒞 : FamClass) (h : Loc)
    (hT : Closed 𝒞 fun Fm _ => GroupCompatibilityFamily Fm) (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  link_of_local_closed 𝒞 h (hT.imp fun Fm _ _ ht => gatEF_of_tied Fm ht) (hT.imp fun Fm _ _ ht => stdSubF_of_tied Fm ht)
    h2 (hT.imp fun Fm _ _ ht => npDescF_of_tied Fm ht)

theorem linkG_concrete5 (𝒞 : FamClass) (hT : Closed 𝒞 fun Fm _ => GroupCompatibilityFamily Fm) (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  linkG_concrete_noKer 𝒞 loc_proved hT h2

end Formalism.L2.G
end
end
end
