module

public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFDOf
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeB
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBCFrameR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPf
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.AdelicContinuousOfUniform

section

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

theorem bcSp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : Gx (spMap ψ ≫ x) ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom ≫ spMap ψ)
    (pullback.snd (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom)
    (by rw [Category.assoc]; exact pullback.condition)

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [Over.snd_left, Over.snd_left]
  exact pullback.lift_snd _ _ _

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Over.fst_left, Over.fst_left]
  exact pullback.lift_fst _ _ _

theorem bcOver {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (h : x ≫ Xo.s = sOf c S) : (spMap ψ.toRingHom ≫ x) ≫ Xo.s = sOf c T := by
  rw [Category.assoc, h]
  unfold sOf
  rw [bcSp]
  congr 1
  ext a
  simp



end BC

section Loc

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Loc

end Formalism.L2.Pj
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RdIndepOf

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem rdIndep_of_wt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hAT : AllTest Xo c)
    (hU : IsUnf (U σ)) (hA : BCEx Xo c σ) (hF : WtField Xo c) : RdIndep Xo c U σ := by
  intro a k _ n b hb hli
  have hT : ∀ kk x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un kk x) := by
    intro kk x
    letI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    exact hAT (CAt σ) ((U σ).un kk x)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ kk (x : ((U σ).X kk).dom), ∑ i, g i * toC (evR Xo c (b i) ((U σ).un kk x)) = 0 := by
    intro kk x
    have h := congrFun (congrFun hg kk) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [← rdU_apply_dom (U σ) _ kk x]
  have hall := rel_of_frames (U σ) hU.2.2.1 hT hF b hb g hrel
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hc := indep_of_complex (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hW
    (fun p φ y => hA p y φ) b (fun i => (hb i).1) hli g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TanAddPf

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem tanAdd_holds (Xo : Moduli Dw l) : TanAddSt Xo := by
  intro S _ x w hw a b u₁ u₂ h₁ h₂
  have e₁ : u₁ = smT x a (ovT (t := Xo.univ.t) hw) := Over.OverMorphism.ext h₁
  have e₂ : u₂ = smT x b (ovT (t := Xo.univ.t) hw) := Over.OverMorphism.ext h₂
  rw [e₁, e₂, ← smT_add x _ (smT_zero_ovT hw)]
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrameLaws

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

variable (c : Coeff l)

def frBC (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {S K : Type} [CommRing S] [Algebra c.F S] [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K)
    (y : FrPt Xo c S) : FrPt Xo c K where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := Formalism.L2.Pj.bcOver ψ y.x_over
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis τ w hw he := bcLieAll c ψ y τ w hw he
  s := secCP (cpS ψ.toRingHom y.x) y.s
  gen := genBC_frame y.x hS hT ψ.toRingHom y.s y.gen

theorem frMap_frBC (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {S K : Type} [CommRing S] [Algebra c.F S] [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K)
    (y : FrPt Xo c S) : FrMap ψ y (frBC c hS hT ψ y) :=
  ⟨rfl, fun _ _ => rfl, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm ψ.toRingHom y.x, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_snd _ _,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_fst _ _, fun _ _ => rfl⟩

theorem bcEx_laws (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (σ : c.F →+* ℂ) : BCEx Xo c σ := by
  intro p y ψ
  let _ : Field (CAt σ) := inferInstanceAs (Field ℂ)
  exact ⟨frBC c hS hT ψ y, frMap_frBC c hS hT ψ y⟩

theorem wtField_laws (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) :
    WtField Xo c :=
  wtField_of_bcR hW (tanAdd_holds Xo) (bcGenR hS hT c) (bcLieR c)

theorem rdIndep_laws (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hAT : AllTest Xo c)
    (hU : IsUnf (U σ)) : RdIndep Xo c U σ :=
  rdIndep_of_wt U σ hW hAT hU (bcEx_laws c hS hT σ) (wtField_laws c hS hT hW)

end ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.L2.Pj

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end
