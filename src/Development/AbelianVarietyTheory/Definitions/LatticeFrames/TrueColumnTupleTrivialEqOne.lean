module

public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.HermitianForms.TiedBr
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Formalism.LocalToGlobal.KernelLattices.KerMemPin
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

-- Source module: Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions

variable (D : D7) (u : D.what₂.Word)

abbrev Pt : HLat D.what₂.LL := (D.fm u).ptLat

def IsPsi (Ψ : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V) : Prop :=
  ∀ x : (D.div.Nu u).V, (D.fm u).ptEmb (Ψ x) = PsiC (D.mem u).C (D.mem u).A (D.mem u).P (D.eMu u (D.jN u x))

def PsiRat : Prop := ∃ Ψ, IsPsi D u Ψ


open Classical in
def Psi : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V := if h : PsiRat D u then h.choose else 0

theorem isPsi_Psi (h : PsiRat D u) : IsPsi D u (Psi D u) := by
  unfold Psi; rw [dite_eq_left h]; exact h.choose_spec

def htPsi : ℝ := Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X (Pt D u).b (Pt D u).X (Psi D u)

def HtPsiLe (h : ℝ) : Prop := PsiRat D u ∧ (Psi D u ≠ 0 → htPsi D u ≤ h)

def PsiInt (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Prop :=
  PsiRat D u ∧ ∀ x ∈ N, Psi D u x ∈ (Pt D u).L

variable (Am : AmbForm D (RowSide.sharp D))

def IsPer (e : (Pt D u).V ≃ₗ[D.what₂.LL] (MtDual D Am).V) : Prop :=
  ∀ (x : (Pt D u).V) (z : (Mt D Am).V),
    D.what₂.embLL ((show Module.Dual D.what₂.LL (Mt D Am).V from e x) z) =
      (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm (Am.jAmb D.what₂.mu0 z))

theorem IsPer.isPhi_comp {e} (he : IsPer D u Am e) {Ψ} (h : IsPsi D u Ψ) : IsPhi D Am u (e.toLinearMap ∘ₗ Ψ) := fun x z => by
  refine (he (Ψ x) z).trans ?_
  rw [h x]
  exact (PhiC_apply _ _ _ _ _).trans (D.perCol_base_eq_PtilCol u _ _).symm

def AmbMetric : Prop :=
  ∃ e, IsPer D u Am e ∧ ∀ (v : InfinitePlace D.what₂.LL) (x : (Pt D u).V),
    Formalism.HermitianLatticesTheory.normAt (MtDual D Am).b (MtDual D Am).X v (e x) = Formalism.HermitianLatticesTheory.normAt (Pt D u).b (Pt D u).X v x

def AmbLattice : Prop :=
  ∃ e, IsPer D u Am e ∧ (∀ x, e x ∈ (MtDual D Am).L → x ∈ (Pt D u).L) ∧
    ∀ x ∈ (Pt D u).L, ((D.mem u).C.DGam : D.what₂.LL) • e x ∈ (MtDual D Am).L

end GlobalTheory.Core.Rk

end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Cls

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 NumberField IsDedekindDomain Matrix Formalism.UG

def LowerTie {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Forms.FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (Forms.bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      Forms.fnOf _ (Forms.shiftOf (Forms.lamT u D.R.m)) (Forms.mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c = Forms.fnOf _ (Forms.shiftOf (Forms.sgT u)) 1 (Ker.brTen D u P)

def RootsG (D : D7) : Prop :=
  ∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

structure SelC (ex : Extra D L hT Gi Gl K Y cX) : Type 1 where

  host : Host.HostTied D

  real : Theta.RealTied D

  cols : Forms.ColsTiedSym D

  full : Forms.ColsFullS cols

  extra : Forms.ColsExtraTiedS full ex

  cf : Host.CharFrame D

  tp : Host.TupTied D cf ex.nch

  chrVal : Host.ValLL0 D cf

  chrDt : Host.DtTied D cf

  roots : RootsG D

  tw : Forms.SymmetricTwistedColumnsAtPrimes tp cols ex.tw

  emt : Rows.EMtTied D cols tw

  g : G.GroupCompatibilityAll D hT ex.cmp

  herm_eq : g.herm = full.1.to0

  forms_eq : g.forms = fun u => (cols.forms u).to0

  beOn : ∀ u, Ker.BeOnTie D u

  lower : ∀ u, LowerTie (cols.forms u)

  ambMetric : ∀ u, Rk.AmbMetric D u ex.amb

  ambLattice : ∀ u, Rk.AmbLattice D u ex.amb

structure SelB (ex : Extra D L hT Gi Gl K Y cX) : Type 1 extends SelC ex where

  ker : Ker.KerEntTied ex

  crd : ∀ (u : D.what₂.Word) i, i ≤ D.R.m → GL (Fin (D.R.N i)) D.host.E

  crd_gram : ∀ u i (hi : i ≤ D.R.m),
    cT (Forms.sigD D : D.host.E →+* D.host.E) (crd u i hi).1 * (crd u i hi).1 = Forms.gramN D i hi

  crd_lat : ∀ u i (hi : i ≤ D.R.m) (x : Fin (D.R.N i) → D.host.E),
    x ∈ Forms.selfDualLatticeCoords D i hi ↔ ∀ a, ((crd u i hi).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

  ker_sharp : ∀ μ, (ker.cst μ).sharp = true

  ker_frm : ∀ u μ i (hi : i ≤ D.R.m) (y : (D.chTw u μ).Y i) (τ : D.what₂.Tau),
    (ker.O u μ).frm i y τ = Forms.atInf (Forms.embT D) (crd u i hi).1 τ * (Forms.twYS tw.ch cols.forms u μ i hi y).1 τ

  aaUnit : ker.AAUnit

  unfAll : ker.UnfAll

  adapted : ker.Adapted

  top : ker.TopPinned

  chTie : ker.ChTie

  memSide : ker.MemSideU

  mtTw : ker.MtTwTie

  om : Formalism.L2.GlobalTheoryTheory.OmegaCompatible D ker.δ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {ex : Extra D L hT Gi Gl K Y cX}

end GlobalTheory.Core.Cls

end
end
end
