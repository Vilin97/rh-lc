module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MulIntegerMemBaseLattice
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PullIopOf
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.ReductionOf
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.OneEntryMem
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.LineOfSpans
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.CharacterFactorUnitaryAction
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.NormOne
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeightShare

section

@[expose] public section

theorem UpperTheory.Reformulated.B.HeightShare.star_sqrt_neg :
    ∀ {D : Formalism.BasicNotions.D7} (x : D.host.E) (n : ℕ),
    (0 : ℕ) < n →
      x ^ (2 : ℕ) = -(↑n : D.host.E) →
        Star.star x =
          -x := by
  intro D x n hn hx
  haveI := D.host.isCMField_hostE
  have hc : D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x
  have h2 : star x ^ 2 = x ^ 2 := by rw [← star_pow, hx, star_neg, star_natCast]
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left fun h => ?_
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 (h ▸ hc).symm
  have h3 : (r : ℂ) ^ 2 = -(n : ℂ) := by rw [← hr, ← map_pow, hx, map_neg, map_natCast]
  have h4 : r ^ 2 = -(n : ℝ) := by exact_mod_cast h3
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith [sq_nonneg r]
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPOf

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_of (B : Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hL : B.LatAll)
    (h0 : ∀ N N', Even N → Even N' → B.ThZeroMem N N')
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hJ1 : J1 B) (hJ2 : J2 B) : B.EqP χ :=
  reduction_of (detMul D) (detSmul D) (norm_one_unit_ideal D) (smulSD D) χ hχ hL h0 hSq hTL hTR (pullIop_of hL) hJ1 hJ2

theorem eqP (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hJ1 : J1 B) (hJ2 : J2 B) : B.EqP χ :=
  eqP_of B χ hχ (B.latAll hcc hδ hδ0) (fun N N' _ _ => B.thZeroMem hS N N') hSq hTL hTR hJ1 hJ2

end Formalism.L2.PairingIndexBounds.Eq
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantOfTrianglesData

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem first_constant_of_triangles_data (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hG : GaussRow B)
    (hLat : ∀ N N', Even N → Even N' → Lat0IsLat B N N') (hSp : ∀ N N', Even N → Even N' → B.ThZeroSpans N N') : J1 B := by
  intro N N' γ hN hN'
  obtain ⟨γ₁, γ₂, rfl, h1, h2⟩ := split_host D γ
  exact J1at_mul hL hTL hN hN' (B.thZeroMem hS N N') γ₁ γ₂
    (J1at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₁ h1)
    (J1at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₂ h2)

theorem second_constant_of_triangles_data (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hG : GaussRow B)
    (hLat : ∀ N N', Even N → Even N' → Lat0IsLat B N N') (hSp : ∀ N N', Even N → Even N' → B.ThZeroSpans N N') : J2 B := by
  intro N N' γ' hN hN'
  obtain ⟨γ₁, γ₂, rfl, h1, h2⟩ := split_host D γ'
  have h := J2at_mul hL hTR hN hN' (B.thZeroMem hS N N') γ₁ γ₂
    (J2at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₁ h1)
    (J2at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₂ h2)
  have hself : ∀ M : Submodule (𝓞 D.host.E) (Fin N' → D.host.E), B.thMoved N N' (StandardLatticesGL3.stdL D N) M =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) M)
        (B.thZero N N') := by
    intro M
    show TaylorLogMetric.Iop D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
    rw [iopSelf D B.tor N N' _ _ (mem_ThSp_of' _ _ _ _ (B.thZeroMem hS N N'))]
  rw [hself]
  exact h

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantOfGaussSum

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem first_constant_of_gauss_sum (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hG : GaussRow B) : J1 B :=
  first_constant_of_triangles_data hS hL hTL hG (fun N N' _ _ => lat0IsLat hS N N') (fun N N' _ _ => thZeroSpans hS N N')

theorem second_constant_of_gauss_sum (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hG : GaussRow B) : J2 B :=
  second_constant_of_triangles_data hS hL hTR hG (fun N N' _ _ => lat0IsLat hS N N') (fun N N' _ _ => thZeroSpans hS N N')

theorem first_constant_of_pullback (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hNeg : NegOneNorm D) : J1 B :=
  first_constant_of_gauss_sum hS hL hTL (gaussRow_of B hS hL hNeg)

theorem second_constant_of_pullback (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hNeg : NegOneNorm D) : J2 B :=
  second_constant_of_gauss_sum hS hL hTR (gaussRow_of B hS hL hNeg)

theorem eqP_of_neg (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hNeg : NegOneNorm D) : B.EqP χ :=
  eqP B hcc hδ hδ0 hS χ hχ hSq hTL hTR (first_constant_of_pullback hS (B.latAll hcc hδ hδ0) hTL hNeg) (second_constant_of_pullback hS (B.latAll hcc hδ hδ0) hTR hNeg)

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantHolds

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem star_sqrt_neg (x : D.host.E) (n : ℕ) (hn : 0 < n) (hx : x ^ 2 = -(n : D.host.E)) : star x = -x :=
  _root_.UpperTheory.Reformulated.B.HeightShare.star_sqrt_neg x n hn hx

theorem isIntegral_sqrt (x : D.host.E) (n : ℕ) (hx : x ^ 2 = -(n : D.host.E)) : IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (n : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [hx]

theorem isIntegral_int (k : ℤ) : IsIntegral ℤ (k : D.host.E) := by
  have := isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := k)
  simpa using this

theorem negOneNorm (D : D7) : NegOneNorm D := by
  intro m hm
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have hqd : D.host.q ≠ D.host.d := by omega
  obtain ⟨α, β, γ, δ, s, h⟩ := Neg.rep_int D.host.q D.host.d hq hd hq8 hqd m hm
  have ha : (D.host.sqq : D.host.E) ^ 2 = -(D.host.q : D.host.E) :=
    D.host.sqq_sq
  have hb : (D.host.sqd : D.host.E) ^ 2 = -(D.host.d : D.host.E) :=
    D.host.sqd_sq
  obtain ⟨a, haa⟩ : ∃ a : D.host.E, a = D.host.sqq := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b : D.host.E, b = D.host.sqd := ⟨_, rfl⟩
  rw [← haa] at ha
  rw [← hbb] at hb
  have hsa := star_sqrt_neg a _ hq.pos ha
  have hsb := star_sqrt_neg b _ hd.pos hb
  have hint : IsIntegral ℤ (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) :=
    ((isIntegral_int α).add ((isIntegral_int β).mul (isIntegral_sqrt a _ ha))).mul
      ((isIntegral_int γ).add ((isIntegral_int δ).mul (isIntegral_sqrt b _ hb)))
  refine ⟨⟨_, hint⟩, ⟨_, isIntegral_int s⟩, ?_, ?_⟩
  · show star (s : D.host.E) = (s : D.host.E)
    exact star_intCast s
  · show star (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) * (((α : D.host.E) + β * a) * ((γ : D.host.E) + δ * b)) =
      -1 + (m : D.host.E) * (s : D.host.E)
    have hZ : ((α : D.host.E) ^ 2 + D.host.q * (β : D.host.E) ^ 2) * ((γ : D.host.E) ^ 2 + D.host.d * (δ : D.host.E) ^ 2) =
        -1 + (m : D.host.E) * (s : D.host.E) := by exact_mod_cast congrArg (Int.cast : ℤ → D.host.E) h
    rw [star_mul', star_add, star_add, star_mul', star_mul', star_intCast, star_intCast, star_intCast, star_intCast,
      hsa, hsb]
    linear_combination hZ + (-(β : D.host.E) ^ 2 * ((γ : D.host.E) ^ 2 - (δ : D.host.E) ^ 2 * b ^ 2)) * ha +
      (-((α : D.host.E) ^ 2 + D.host.q * (β : D.host.E) ^ 2) * (δ : D.host.E) ^ 2) * hb

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem eqP_of_paths (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) : B.EqP χ :=
  eqP_of_neg B hcc hδ hδ0 hS χ hχ hSq hTL hTR (negOneNorm D)

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end
