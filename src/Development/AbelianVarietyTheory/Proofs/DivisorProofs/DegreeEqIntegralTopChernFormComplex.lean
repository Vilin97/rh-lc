module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegralStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionOfGeneratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPowStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMultilinear

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.SelfInterPoly

theorem exists_polynomial_multilinear {A : Type*} {ι : Type} [AddCommGroup A] [Fintype ι]
    (f : (ι → A) →ₘₗ[ℤ] ℤ) (a b : A) :
    ∃ P : Polynomial ℝ, ∀ m : ℕ, (f (fun _ => a + m • b) : ℝ) = P.eval (m : ℝ) := by
  classical
  refine ⟨∑ S : Finset ι, Polynomial.C (f (S.piecewise (fun _ => b) (fun _ => a)) : ℝ) *
    Polynomial.X ^ S.card, fun m => ?_⟩
  have e : (fun _ : ι => a + m • b) = (fun _ : ι => (m : ℤ) • b) + (fun _ : ι => a) := by
    funext i
    simp [add_comm]
  rw [e, f.map_add_univ, Polynomial.eval_finsetSum, Int.cast_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have e₂ : S.piecewise (fun _ : ι => (m : ℤ) • b) (fun _ : ι => a) =
      S.piecewise (fun i => (fun _ : ι => (m : ℤ)) i • S.piecewise (fun _ => b) (fun _ => a) i)
        (S.piecewise (fun _ => b) (fun _ => a)) := by
    funext i
    by_cases h : i ∈ S <;> simp [h]
  rw [e₂, f.map_piecewise_smul]
  simp [mul_comm]

theorem exists_polynomial_topSelf : ∀ (Y : Var ℂ) (L H : LB Y.X), L.IsLB → H.IsLB → ∃ P : Polynomial ℝ, P.eval 0 = (topSelfIntersection ℂ L Y.dim : ℝ) ∧ ∀ m : ℕ, (topSelfIntersection ℂ (CechPic.tens L (lbPow H m)) Y.dim : ℝ) = P.eval (m : ℝ) := by
  intro Y L H hL hH
  have hv := diffVanish_chiPic_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver
    (d := Y.dim) (by rw [QCoh.suppDim_structureModule, Y.topologicalKrullDim_eq])
  have key : ∀ (M : LB Y.X) (hM : M.IsLB), topSelfIntersection ℂ M Y.dim = hv.form fun _ => cls M hM :=
    fun M hM => (interNum_eq_multiDiff ℂ _ fun _ => hM).trans (hv.form_apply _ 0).symm
  obtain ⟨P, hP⟩ := exists_polynomial_multilinear hv.form (cls L hL) (cls H hH)
  refine ⟨P, ?_, fun m => ?_⟩
  · have h0 := hP 0
    rw [zero_nsmul, add_zero, Nat.cast_zero] at h0
    rw [key L hL, h0]
  · rw [key _ (isLB_tens hL (isLB_lbPow hH m)), cls_tens hL (isLB_lbPow hH m), cls_lbPow hH, hP]

end GlobalTheory.SelfInterPoly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleByO1

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjVar

theorem exists_veryAmpleBy_O1 : ∀ Y : Var ℂ, ∃ s : Fin (Y.N + 1) → ((ProjSpace.O1 ℂ Y.N).pull Y.ι).Sec, GlobalTheory.AbLaw.VeryAmpleBy Y.str ((ProjSpace.O1 ℂ Y.N).pull Y.ι) s :=
  fun Y => ⟨_, ProjSpace.veryAmpleBy_secPull_coord Y.ι⟩

end GlobalTheory.ProjVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGenerated

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjVar

theorem exists_generating_secs_tens_lbPow_O1 : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (n : ℕ) (u : Fin n → (CechPic.tens L (lbPow ((ProjSpace.O1 ℂ Y.N).pull Y.ι) m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro Y L hL
  obtain ⟨s, hs⟩ := exists_veryAmpleBy_O1 Y
  have hH : ((ProjSpace.O1 ℂ Y.N).pull Y.ι).IsLB := pull_isLB (ProjSpace.O1_isLB ℂ Y.N) _
  generalize (ProjSpace.O1 ℂ Y.N).pull Y.ι = H at s hs hH
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated ℂ Y.X Y.str H _ s hH hs L hL
  refine ⟨t₀.toNat, fun m hm => ?_⟩
  obtain ⟨n, u, hu⟩ := ht m (by omega)
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens L (lbPow H m)).IsLB := isLB_tens hL hP
  have e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) =
      cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)
  have e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨_, v, hv⟩

end GlobalTheory.ProjVar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGeneratedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.twist_ample_globally_generated : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (n : ℕ) (u : Fin n → (CechPic.tens L (lbPow ((ProjSpace.O1 ℂ Y.N).pull Y.ι) m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 | exact GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 | (intros; apply GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundle

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option autoImplicit false

namespace GlobalTheory.MassDegree

theorem chernInt_eq_topSelf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ
  let ψ : Weight Y.str (RingHom.id ℂ) ((ProjSpace.O1 ℂ Y.N).pull Y.ι) :=
    ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).φ (RingHom.id ℂ)).pull Y.ι Y.ι_str
  have hψ : ψ.IsCInf := ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).cInf (RingHom.id ℂ)).pull Y.ι Y.ι_str
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.T.exists_polynomial_chernIntegral_tens_pow Y L _ φ ψ hφ hψ
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.SelfInterPoly.exists_polynomial_topSelf Y L _ φ.isLB ψ.isLB
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.twist_ample_globally_generated Y L φ.isLB
  have key : ∀ m : ℕ, m₀ ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨n, u, hu⟩ := hm₀ m hm
    rw [← hP m, ← hQ m]
    exact GlobalTheory.T.chernMass_eq_selfIntersection_of_generated Y _ (φ.tens (ψ.pow m)) (hφ.tens (hψ.zpow m)) n u hu
  have hPQ : P = Q := by
    refine Polynomial.eq_of_infinite_eval_eq P Q ?_
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite m₀).image Nat.cast_injective.injOn)
    rintro _ ⟨m, hm, rfl⟩
    exact key m hm
  rw [← hP0, ← hQ0, hPQ]

end GlobalTheory.MassDegree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernMass_eq_selfIntersection_lineBundle : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  first | exact @GlobalTheory.MassDegree.chernInt_eq_topSelf | exact GlobalTheory.MassDegree.chernInt_eq_topSelf | (intros; apply GlobalTheory.MassDegree.chernInt_eq_topSelf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresented

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernDegree

theorem inter_const_eq_topSelf_of_presents :
    ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim :=
  fun _ _ _ _ hL h => Var.inter_eq_of_toPic_eq (fun _ => hL) fun _ => h.toPic_eq

end GlobalTheory.ChernDegree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresentedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.intersection_divisor_eq_selfIntersection_presented : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim := by
  first | exact @GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents | exact GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents | (intros; apply GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqIntegralTopChernFormComplex

section

@[expose] public section

namespace GlobalTheory.ChernDegree

theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex := fun Y Δ L r hr φ hφ =>
  ⟨(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).1, by
    rw [GlobalTheory.T.chernMass_eq_selfIntersection_lineBundle Y L φ hφ, GlobalTheory.T.intersection_divisor_eq_selfIntersection_presented Y Δ L r φ.isLB hr]⟩

end GlobalTheory.ChernDegree
end
end
