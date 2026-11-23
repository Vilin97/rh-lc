module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
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
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NotRootUnity

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory IsDedekindDomain
  NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsUnifIdele (P : HeightOneSpectrum (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  ∃ (e f : AE D) (ϖ : 𝓞 D.host.E), IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧
    (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)

def IsUnramAt (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ e f : AE D, IsPrimeIdem P e f ∧ ∀ x : (AE D)ˣ, (x : AE D) = e * (x : AE D) + (1 - e) →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1


open Classical in
def chiAt (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) : ℂ :=
  if h : IsUnramAt χ P ∧ ∃ x, IsUnifIdele P x then ((χ h.2.choose : Circle) : ℂ) else 0

def normP (P : HeightOneSpectrum (𝓞 D.host.E)) : ℕ := Ideal.absNorm P.asIdeal

def lfac (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) (s : ℂ) : ℂ :=
  (1 - chiAt χ P * (normP P : ℂ) ^ (-s))⁻¹

end Formalism.IndefR.Mi

end
end
end

-- Source module: Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PartialLFunctionCharacter

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult IsDedekindDomain NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

variable {D : D7}

def TrivialOnF (χ : (AE D)ˣ →* Circle) : Prop := ∀ a : (AF D.host.F)ˣ, χ (idF D a) = 1

def lPartial (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) (s : ℂ) : ℂ :=
  ∏' P : {P : HeightOneSpectrum (𝓞 D.host.E) // OffS D S P}, Mi.lfac χ P.1 s

def IsPartialL (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re →
    HasProd (fun P : {P : HeightOneSpectrum (𝓞 D.host.E) // OffS D S P} => Mi.lfac χ P.1 s) (Λ s)

def IsFiniteL (χ : (AE D)ˣ →* Circle) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re →
    HasProd (fun P : HeightOneSpectrum (𝓞 D.host.E) => Mi.lfac χ P s) (Λ s)

def PosUpTo (t : ℕ) (Λ : ℂ → ℂ) : Prop := ∀ n : ℕ, 1 ≤ n → n ≤ t → (Λ n).im = 0 ∧ 0 < (Λ n).re

def HeckeRatioPos (D : D7) : Prop :=
  ∀ μ μ' : (AE D)ˣ →* Circle, IsHeckeChar D μ → IsHeckeChar D μ' → TrivialOnF μ → TrivialOnF μ' →
    (∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D μ τ (-e) ∧ HasInfExp D μ' τ (-e') ∧ e ≠ e') →
    ∀ t : ℕ,
      (∃ Λ : ℂ → ℂ, IsFiniteL (μ * μ'⁻¹) Λ ∧ PosUpTo t Λ) ∧
      ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∃ Λ : ℂ → ℂ, IsPartialL S (μ * μ'⁻¹) Λ ∧ PosUpTo t Λ

theorem IsPartialL.eq_lPartial {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {χ : (AE D)ˣ →* Circle} {Λ : ℂ → ℂ}
    (h : IsPartialL S χ Λ) {s : ℂ} (hs : 1 < s.re) : Λ s = lPartial S χ s := (h.2 s hs).tprod_eq.symm

theorem eq_of_eqOn_re {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  refine AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2) (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) ?_
  have : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  exact Filter.mem_of_superset this h

theorem IsPartialL.unique {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {χ : (AE D)ˣ →* Circle} {Λ Λ' : ℂ → ℂ}
    (h : IsPartialL S χ Λ) (h' : IsPartialL S χ Λ') : Λ = Λ' :=
  eq_of_eqOn_re h.1 h'.1 fun _ hs => (h.eq_lPartial hs).trans (h'.eq_lPartial hs).symm

end GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

end
end
end
