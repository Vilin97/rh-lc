module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapPropertiesOfSymmetricForms
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfSelfDual
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClsCrdEqGlob
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
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
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.BrStmt

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField Formalism.UG

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ChiFinM (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U,
    (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)

def SelfDualP (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E))

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.SelfDualPHolds

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

theorem gramP_det_unit (D : D7) : IsUnit (gramP D).det := by
  let _ := D.host.cmStar
  unfold gramP
  rw [Matrix.det_reindex_self]
  exact Formalism.L2.G.gram_det_unit D.sp.cm D.sp.X'

theorem isLat_dlP (D : D7) (M : Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)) (hM : Comp.IsLat M) :
    Comp.IsLat (Comp.dl (sigD D) (gramP D) M) := by
  have hL : Submodule.IsLattice D.host.E M := Submodule.IsLattice.of_fg _ (Module.Finite.iff_fg.1 hM.1)
  have hFull : Submodule.IsFullLattice D.host.E M := { hL with span_eq_top := hM.2 }
  obtain ⟨d, hd, hle⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramP D) (gramP_det_unit D) M hFull
  exact ⟨Module.Finite.iff_fg.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hd hle),
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramP D) M hL⟩

variable {D : D7} {u : D.what₂.Word}

theorem levelLattice_dual_eq_self (K : ClsPTied (D := D) u) : Comp.dl (sigD D) (gramP D) K.lev.Lb = K.lev.Lb := by
  have hS : dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) K.lev.Lb = (K.lev.Lb : Set _) := by
    ext y
    constructor
    · intro hy
      have h := K.lev.Lb_dual y hy
      simpa using h
    · intro hy
      exact K.lev.Lb_int y hy
  unfold Comp.dl
  rw [hS, Submodule.span_eq]

theorem classLattice_eq_globalLattice (K : ClsPTied (D := D) u) (c : (D.fm u).clsP) :
    K.lat c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
  ext x
  constructor
  · intro hx
    exact (K.y_lat c _).1 (latS_of_mem _ x hx)
  · intro hx
    exact latLocGlob _ _ _ (K.lat c) (K.lat_fin c) x ((K.y_lat c _).2 hx)

theorem selfDualP_of_formsTiedSym {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf) :
    SelfDualP Tf := by
  intro c
  have hLb : Comp.IsLat Tf.clsP.lev.Lb := ⟨Tf.clsP.lev.Lb_fin, Tf.clsP.lev.Lb_span⟩
  have h1 : Comp.dl (sigD D) (gramP D) (Tf.clsP.lat c) = Tf.clsP.lat c := by
    rw [classLattice_eq_globalLattice, ← Comp.glob_dl (sigD D) (gramP D) (isLat_dlP D) hLb _ (Tf.clsP.y c).2, levelLattice_dual_eq_self]
  rw [← Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_span_dualSet]
  exact congrArg (fun M : Submodule _ _ => (M : Set (Fin (D.R.N D.R.m - 1) → D.host.E))) h1

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricClausesOfFormsNorm

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain



theorem fvStab_holds {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : FormsTiedSym D u Ch chOf) : FvStab Tf := by
  intro c γ hγ v x hx
  have hF := Tf.fv D.R.m le_rfl (Or.inr rfl)
  have hγ' := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI_range _ γ).1 hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ'
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 =
      ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 * κ *
        ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1⁻¹ := by
    rw [← hκe]; rfl
  have hκv := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U_eq κ).1 hκ |>.2 (Tf.atT.eV v).1
  rw [(Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.UlocAlt (Tf.atT.eV v).1 (Tf.atT.eV v).2] at hκv
  obtain ⟨_, hfix⟩ := (Subgroup.mem_inf.mp hκv).2
  have hzx := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) x.1 x.2
  have hzg := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) _ hx
  have key := conj_stepA (Tf.atT.eV v).1 _ κ γ.1 hbc x.1
  exact (hF v ((D.fm u).til c) ⟨_, hx⟩ hzg).trans ((congrArg _ ((congrArg _ (Subtype.ext key)).trans (hfix ⟨_, hzx⟩))).trans
    (hF v ((D.fm u).til c) x hzx).symm)

theorem class_injective_holds : ClassMapInjective :=
  class_injective_of_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf)

theorem stabiliser_bijective_holds : StabiliserMapBijective :=
  stabiliser_bijective_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf) (fun _ _ _ _ Tf => fvStab_holds Tf)

end Formalism.L2.GlobalTheoryTheory.Br
end
end
end
