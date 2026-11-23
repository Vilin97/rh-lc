module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormChernIntegrableOfPrincipalisationStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyReciprocityAtComplexEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralEqSumEmbeddingsStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubschemeStatement
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalyticStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedArchIntegralEqSumClosureIntegrals

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem logSec_restr_secPull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} (N : HermLB p) (t : N.B.Sec)
    (i : Y ⟶ X) (σ : k →+* ℂ) :
    (MLine.ofHerm (N.restr i) σ).logSec (Cartier.secPull t i) =
      fun y => (MLine.ofHerm N σ).logSec t (ptMap i rfl σ y) :=
  funext fun y => congrArg (fun a => Real.log a / 2) ((N.φ σ).nsq_pull_secPull i rfl t y)

theorem resArch_eq_finsum_cycInt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  intro hP k _ X _ _ p e hX L N t z hz htz
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  have hgen : genericPoint (clo z) ∈ nonzeroLocus (Cartier.secPull t (cloι z)) := by
    rw [Cartier.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]; exact htz
  have hd : topologicalKrullDim (clo z) = (e + 1 : ℕ) :=
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k X p hamb (e + 1) hX.dim_eq).2 z (genericPoint (clo z)) hz).1
  have hamb' : IsAmb (cloι z ≫ p) := hamb.sub (cloι z)
  have hc (σ : k →+* ℂ) := (GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme k X (clo z) p (cloι z ≫ p) σ hX.isProjOver (cloι z) rfl e
    (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t)).2
  simp only [cloι_genericPoint] at hc
  refine (dif_pos hgen).trans ?_
  rcases isArithVar_or_isEmpty hamb' hd with hv | hE
  · refine (GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings hP k (clo z) (cloι z ≫ p) e hv (fun a => (L a).restr (cloι z)) (N.restr (cloι z))
      (Cartier.secPull t (cloι z)) hgen).trans (finsum_congr fun σ => ?_)
    rw [hc σ, logSec_restr_secPull]
    rfl
  · refine (mixArch_eq_zero_of_isEmpty hE _ _ _).trans (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm
    rw [hc σ]
    haveI := hE σ
    simp only [Mix.int, MeasureTheory.integral_of_isEmpty, sub_zero]

end GlobalTheory.MixHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedArchIntegralEqSumClosureIntegralsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.restrictedArchIntegral_eq_sum_closureIntegrals : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  first | exact @GlobalTheory.MixHt.resArch_eq_finsum_cycInt | exact GlobalTheory.MixHt.resArch_eq_finsum_cycInt | (intros; apply GlobalTheory.MixHt.resArch_eq_finsum_cycInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormReciprocityOfPrincipalisation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem archRecip_of_principalisation (hP : GlobalTheory.Published.Principalisation) : ArchRecip := by
  intro k _ Y _ _ q e hq M N L s t hs ht hcov
  have : IsNoetherian Y := hq.isNoetherian
  have : Finite (k →+* ℂ) := hq.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hcons (A : HermLB q) (σ : k →+* ℂ) :
      (fun i => MLine.ofHerm ((Fin.cons A L : Fin (e + 1) → HermLB q) i) σ) =
        Fin.cons (MLine.ofHerm A σ) (fun i => MLine.ofHerm (L i) σ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, ((divOfSec A.isLB a ha).mult z : ℝ) *
          cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm B σ).logSec b) z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [GlobalTheory.T.restrictedArchIntegral_eq_sum_closureIntegrals hP k Y q e hq L B b z hz ((hab z hz).resolve_left hza), finsum_eq_sum_of_fintype,
        Finset.mul_sum]
  have fin (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
    D.finite_support_mult.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h
      simp [h] at hz
  have hside (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) :
      mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) A (isRatSec_ratOfSec a ha) +
          ∑ᶠ z, ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, side (MLine.ofHerm B σ) (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm A σ).logSec a)
          ((MLine.ofHerm B σ).logSec b) (divOfSec (MLine.ofHerm A σ).φ.isLB a ha) := by
    rw [GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings hP k Y q (e + 1) hq, finsum_eq_sum_of_fintype, finsum_congr (key A B a b ha hab),
      finsum_sum_comm _ _ (fun σ _ => fin _ _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [side, ← hcons]
    rfl
  rw [hside M N s t hs hcov, hside N M t s ht fun z hz => (hcov z hz).symm]
  exact Finset.sum_congr rfl fun σ _ => GlobalTheory.T.arith_variety_reciprocity_at_complex_embedding hP k Y q e hq σ (fun i => MLine.ofHerm (L i) σ)
    (MLine.ofHerm M σ) (MLine.ofHerm N σ) s hs t ht hcov

end GlobalTheory.MixHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormReciprocityOfPrincipalisationStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.archLogNormReciprocity_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchRecip := by
  first | exact @GlobalTheory.MixHt.archRecip_of_principalisation | exact GlobalTheory.MixHt.archRecip_of_principalisation | (intros; apply GlobalTheory.MixHt.archRecip_of_principalisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem GlobalTheory.MixHt.arCalc_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArCalc := fun h =>
  (GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic (GlobalTheory.T.archLogNormChernIntegrable_of_principalisation h) (GlobalTheory.T.archLogNormReciprocity_of_principalisation h)).1
end
end
