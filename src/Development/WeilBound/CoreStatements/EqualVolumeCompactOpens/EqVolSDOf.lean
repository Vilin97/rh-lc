module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.IsIsotropicHermitianSetting
public import Mathlib.NumberTheory.NumberField.CMField
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

-- Source module: Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SameUpToScalars

section

@[expose] public section

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev ccH (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E := (IsCMField.complexConj E).toRingHom

end defs

def LevelFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)), IsLat Λ → IsUnit J.det →
    (Neat c 𝔞 → ∀ γ ∈ levelGrp c.toRingHom J Λ 𝔞,
      (∃ s : E, (γ : Matrix (Fin N) (Fin N) E) = s • (1 : Matrix (Fin N) (Fin N) E)) → γ = 1) ∧
    ∀ (J₀ : Matrix (Fin N) (Fin N) E) (a : GL (Fin N) E) (Λ₀ : Submodule (𝓞 E) (Fin N → E)),
      (a : Matrix (Fin N) (Fin N) E)ᵀ * J₀ * (a : Matrix (Fin N) (Fin N) E).map c.toRingHom = J →
      (∀ x, x ∈ Λ ↔ (a : Matrix (Fin N) (Fin N) E) *ᵥ x ∈ Λ₀) →
      conjBy a (levelGrp c.toRingHom J Λ 𝔞) = levelGrp c.toRingHom J₀ Λ₀ 𝔞

end PositivityTheory.EqVol
end
end
end

-- Source module: Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.EqVolSDOf

section

@[expose] public section

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SDHerm (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y)

def SDTrace (ξ : E) (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, EFf ξ G x y = k) ∧ ∀ φ : L →+ ℤ, ∃ x ∈ L, ∀ y : L, (φ y : ℚ) = EFf ξ G x y

end defs

def DualTransport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E) (a : GL (Fin r) E)
    (L' : Submodule (𝓞 E) (Fin r → E)),
    (a : Matrix (Fin r) (Fin r) E)ᵀ * G * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = G' → IsLat L' →
    ∃ aL' : Submodule (𝓞 E) (Fin r → E), IsLat aL' ∧ (∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ aL') ∧
      (SDHerm G' L' → SDHerm G aL') ∧ ∀ ξ, SDTrace ξ G' L' → SDTrace ξ G aL'

def LocalToAdelic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (L L' : Submodule (𝓞 E) (Fin r → E)), IsLat L → IsLat L' →
    (∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (GlobalTheory.SelfDualGenus.LocAlg v),
      (∀ v, GlobalTheory.SelfDualGenus.IsLocalIsometry v G L' G L (γ v)) ∧ {v | γ v ≠ 1}.Finite) →
    AdGenus (IsCMField.complexConj E) G L L'

end PositivityTheory.EqVol
end
end
end
