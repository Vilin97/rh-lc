module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.DatDatum
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KillComp
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Langlands
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearDat
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RhoLe
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.KillCore

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.FunKill

section

@[expose] public section

open NumberField

theorem UpperTheory.ConvolutionTheory.BW.funKill :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.FunKill E := by
  intro E _ _ _ S n ρ C hC
  obtain ⟨B, hB⟩ := far E n C hC
  obtain ⟨D₀, hfin, hD₀⟩ := nearDat E S n ρ B
  refine ⟨{d ∈ D₀ | 2 ≤ d.len}, hfin.subset (Set.sep_subset _ _), fun d hd => hd.2, ?_⟩
  intro φ w F G hφ hSφ hw hK hSw hF hD hG hsum
  refine (langlands E S n ρ w hw hK hSw).2 ?_
  intro k d hd hlen
  refine killComp E S n C φ w F G hC hφ hSφ hw hF hG hsum k d ?_
  by_cases hfar : ∃ τ i, B < ‖d.lam τ i‖
  · exact Or.inr fun ψ hψ hSψ => hB S d ψ hψ hSψ hfar
  · push_neg at hfar
    obtain ⟨d', hd', hl, hk⟩ := hD₀ d hd hfar
    exact Or.inl (hk F hF (hD d' ⟨hd', hl ▸ hlen⟩))
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Imports

section

@[expose] public section

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.BW PositivityTheory.Rg.Tf.Core

theorem UpperTheory.ConvolutionTheory.kill :
    UpperTheory.ConvolutionTheory.Kill := by
  intro K _ _ _ n hn μ _ 𝔞 η hη
  obtain ⟨ρ, Cb, hCb, hcore⟩ := killCore hn 𝔞 η hη
  obtain ⟨D, hD, hlen, hk⟩ := funKill K 𝔞.S n ρ Cb hCb
  choose b hb1 hb2 using fun d : D => datDatum K 𝔞.S n d.1 (hlen d.1 d.2)
  refine ⟨D, hD.fintype, b, hb1, fun ev hev χ hχ hχ0 _ F G hF hFb hG => ?_⟩
  refine hcore ev hev 0 (1 - Pc μ) (fun R _ => by rw [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]) ?_
    (ContinuousLinearMap.zero_comp _) χ hχ hχ0 F G hF hG fun y φ w _ hw hφ hs hkw hsw hsum =>
      hk φ w F G hφ hs hw.umg hkw hsw hF.2 (fun d hd => hb2 ⟨d, hd⟩ F hF.2 (hFb ⟨d, hd⟩)) hG hsum
  exact (Submodule.isIdempotentElem_starProjection _).mul_one_sub_self
end
end
