module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasSym
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjectionAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CommOfZalg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HasDerivAtConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LiftCv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvAlg
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevMulChi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevOfMulChi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocLimMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ChiGrow

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.chiGrow :
    UpperTheory.V.Cj.H.ChiGrow := by
  intro E _ _ _ a χ s _ φ hφ g
  obtain ⟨A, p, hA⟩ := hφ g
  obtain ⟨B, q, hB⟩ := chiDet_growth (a := a) χ⁻¹
  have hback : mulChi a χ⁻¹ (mulChi a χ φ) = φ := by
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  refine ⟨‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * B), p + q, fun y => ?_⟩
  have e : φ.1 (g * infGL E a y) = ((chiDet a χ⁻¹ g : ℂˣ) : ℂ) *
      ((mulChi a χ φ).1 (g * infGL E a y) * ((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)) := by
    conv_lhs => rw [← hback, mulChi_apply, map_mul, Units.val_mul]
    ring
  have hprod := mul_le_mul (hA y) (hB y) (norm_nonneg _) ((norm_nonneg _).trans (hA y))
  calc ‖φ.1 (g * infGL E a y)‖
      = ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (‖(mulChi a χ φ).1 (g * infGL E a y)‖ *
          ‖((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)‖) := by rw [e, norm_mul, norm_mul]
    _ ≤ ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * GlobalTheory.CuspRep.height y ^ p * (B * GlobalTheory.CuspRep.height y ^ q)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := by rw [pow_add]; ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpComm

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opComm :
    UpperTheory.V.Cj.H.OpComm := by
  intro E _ _ _ a ha μ _ _ T hT T' hL
  obtain ⟨c1, c2, c3, -⟩ := clFacts E a μ
  have gf := gardFacts E a ha μ
  refine ⟨fun φ h => (hL φ h).1, fun X φ hφ => ?_, fun g φ hφ => ?_⟩
  · induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨ψ, F, hψ, hφ⟩ := h
      have h1 := liftCv E a ha μ T hT T' hL ψ φ F hψ hφ
      have h2 := cvLie E a μ ψ _ hψ _ h1 X
      have h3 := cvLie E a μ ψ φ hψ F hφ X
      have h4 := liftCv E a ha μ T hT T' hL _ _ F (((testOps E a ψ).2 hψ).1 X) h3
      exact Subtype.ext (h2.trans h4.symm)
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul s x _ hx => simp only [map_smul, hx]
  · have m1 : rt E a g (T' φ) ∈ gard μ := (gf _ (hL φ hφ).1).2.2.2.2 g
    have m0 : rt E a g φ ∈ gard μ := (gf _ hφ).2.2.2.2 g
    have m2 : T' (rt E a g φ) ∈ gard μ := (hL _ m0).1
    have m3 : (1 : ℂ) • rt E a g (T' φ) + (-1 : ℂ) • T' (rt E a g φ) ∈ gard μ :=
      add_mem (Submodule.smul_mem _ _ m1) (Submodule.smul_mem _ _ m2)
    have e := (c1 _ _ 1 (-1) (gf _ m1).2.1 (gf _ m2).2.1).2
    rw [c3 _ g (gf _ (hL φ hφ).1).2.1, (hL φ hφ).2, (hL _ m0).2, c3 _ g (gf _ hφ).2.1, hT,
      ← add_smul, add_neg_cancel, zero_smul] at e
    have z := c2 _ (gf _ m3).1 (gf _ m3).2.1 e
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at z
    exact z
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLim

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opLim :
    UpperTheory.V.Cj.H.OpLim := by
  intro E _ _ _ a ha μ _ _ T P hT hP hlim T' P' hT' hP' φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, hF⟩ := h
    intro C hC
    have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
    obtain ⟨-, hlin, -, hb⟩ := cvAlg (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1
    obtain ⟨B, hB⟩ := hb C hC
    have h1 : ∀ k, (T' k φ).1 = cv ψ.1 (T k F) := fun k =>
      liftCv E a ha μ (T k) (hT k) (T' k) (hT' k) ψ φ F hψ hF
    have h2 : (P' φ).1 = cv ψ.1 (P F) := liftCv E a ha μ P hP P' hP' ψ φ F hψ hF
    have h3 : Tendsto (fun k => B * ‖P F - T k F‖) atTop (𝓝 0) := by
      have h4 : Tendsto (fun k => P F - T k F) atTop (𝓝 (P F - P F)) := tendsto_const_nhds.sub (hlim F)
      have h5 := h4.norm.const_mul B
      simpa using h5
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [h3.eventually (gt_mem_nhds hε)] with k hk x hx
    rw [h1, h2, dist_eq_norm]
    have h6 := congrFun (hlin (P F) (T k F) 1 (-1)) x
    have h7 : (1 : ℂ) • P F + (-1 : ℂ) • T k F = P F - T k F := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [h7] at h6
    have h8 : cv ψ.1 (P F) x - cv ψ.1 (T k F) x = cv ψ.1 (P F - T k F) x := by
      rw [h6]; simp [sub_eq_add_neg]
    rw [h8]
    exact (hB _ x hx).trans_lt hk
  | zero =>
    intro C _
    simp only [map_zero]
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun k x _ => by simpa using hε
  | add φ ψ _ _ h1 h2 =>
    intro C hC
    simp only [map_add (f := _)]
    exact (h1 C hC).add (h2 C hC)
  | smul c φ _ h =>
    intro C hC
    simp only [map_smul]
    exact (uniformContinuous_const_smul c).comp_tendstoUniformlyOn (h C hC)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.FnProj0

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.fnProj0 :
    UpperTheory.V.Cj.H.FnProj0 := by
  intro E _ _ _ a ha μ _ _ n e he c
  obtain ⟨P, Q, S, hP, hQ, hS, hres, hker, hlim⟩ := casimir_resolvent_projection E a ha μ n e he c
  obtain ⟨P', hP'⟩ := opLift E a ha μ P hP
  choose Q' hQ' using fun k => opLift E a ha μ (Q k) (hQ k)
  choose S' hS' using fun k => opLift E a ha μ (S k) (hS k)
  have hG := gardFacts E a ha μ
  obtain ⟨c1, c2, -, -⟩ := clFacts E a μ
  obtain ⟨-, -, hA⟩ := casOp E a n e he 0 c
  obtain ⟨hA1, hA2⟩ := hA (gard μ) fun X φ h => (hG φ h).2.2.2.1 X
  have hinj : ∀ φ ∈ gard μ, cl μ φ = 0 → φ = 0 := fun φ h h0 => c2 φ (hG φ h).1 (hG φ h).2.1 h0
  have hsub : ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (φ - ψ) = cl μ φ - cl μ ψ := by
    intro φ hφ ψ hψ
    have h := (c1 φ ψ 1 (-1) (hG φ hφ).2.1 (hG ψ hψ).2.1).2
    simpa only [one_smul, neg_smul, sub_eq_add_neg] using h
  have oS := fun k => opComm E a ha μ (S k) (hS k) (S' k) (hS' k)
  refine ⟨P', Q', S', opComm E a ha μ P hP P' hP', fun k => opComm E a ha μ (Q k) (hQ k) (Q' k) (hQ' k), oS,
    fun k φ hφ => ?_, fun φ hφ => ?_, opLim E a ha μ Q P hQ hP hlim Q' P' hQ' hP'⟩
  · rw [hA2 (S' k) (oS k) φ hφ]
    have h1 := hQ' k φ hφ
    have h2 := hS' k _ (hA1 φ hφ)
    have h3 := (gard μ).sub_mem hφ h1.1
    refine sub_eq_zero.1 (hinj _ ((gard μ).sub_mem h3 h2.1) ?_)
    rw [hsub _ h3 _ h2.1, hsub _ hφ _ h1.1, h1.2, h2.2, hres k φ hφ, sub_self]
  · have h1 := hP' φ hφ
    have h2 := hA1 _ h1.1
    refine hinj _ h2 (inner_self_eq_zero (𝕜 := ℂ).1 ?_)
    rw [casSym E a ha μ n e c _ h1.1 _ h2, h1.2]
    exact hker _ _ h2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.FnProj

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.fnProj :
    UpperTheory.V.Cj.H.FnProj := by
  intro E _ _ _ a ha r n e he c
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure (GA E a)).IsHaarMeasure
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Lit.Bor.twEx E a ha r
  obtain ⟨P, Q, S, h⟩ := fnProj0 E a ha μ n e he c
  obtain ⟨P', Q', S', h'⟩ := twRes E a r χ hχ (gard μ) n e c P Q S h
  refine ⟨_, P', Q', S', ⟨fun X φ hφ => (twSq E a ha μ r χ hχ φ hφ).1 X, fun φ hφ => ?_,
    fun φ hφ => (twSq E a ha μ r χ hχ φ hφ).2, fun φ h1 h2 h3 h4 => twCpt E a ha μ r χ hχ φ h1 h2 h3 h4⟩, h'⟩
  obtain ⟨s, hs⟩ := hχ.1
  exact chiGrow E a χ s hs φ (gardFacts E a ha μ _ hφ).2.2.1
end
end
