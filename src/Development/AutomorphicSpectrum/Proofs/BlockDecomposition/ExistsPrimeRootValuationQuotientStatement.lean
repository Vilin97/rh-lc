module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparability

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableQuotientOfValuation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValQuot

theorem valuation_comparable_quotient : ∀ {S : Type} [CommRing S] (π : S), Val π → Val0 (S := S ⧸ Ideal.span {π}) := by
  intro S _ π hV f' g'
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g'
  have hpi : ∀ x : S, ∃ N : ℕ, π ^ N ∈ Ideal.span {x, π} := fun x =>
    ⟨1, Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩⟩
  obtain ⟨e₁, he1, h1f, h1π⟩ := hV f π (hpi f)
  obtain ⟨e₂, he2, h2g, h2π⟩ := hV g π (hpi g)
  obtain ⟨a1, ha1⟩ := Ideal.mem_span_singleton'.mp h1f
  obtain ⟨b1, hb1⟩ := Ideal.mem_span_singleton'.mp h1π
  obtain ⟨a2, ha2⟩ := Ideal.mem_span_singleton'.mp h2g
  have he1' : e₁ * e₁ = e₁ := he1
  have he2' : e₂ * e₂ = e₂ := he2
  obtain ⟨u, hu⟩ : ∃ u : S, u = (1 - e₁) * (1 - e₂) := ⟨_, rfl⟩
  have hu2 : u * u = u := by subst hu; linear_combination (1 - e₂) ^ 2 * he1' + (1 - e₁) * he2'
  have he1u : e₁ * u = 0 := by subst hu; linear_combination (-(1 - e₂)) * he1'
  have huπ : u * π = (1 - e₂) * b1 * f := by subst hu; linear_combination (-(1 - e₂)) * hb1
  obtain ⟨e₃, he3, h3, h3'⟩ := hV (u * f + (1 - u)) (u * g + (1 - u))
    ⟨1, Ideal.mem_span_pair.mpr ⟨(1 - e₂) * b1 * u + π * (1 - u), 0, by
      linear_combination ((1 - e₂) * b1 * f - (1 - e₂) * b1 - π * f + 2 * π) * hu2 - u * huπ⟩⟩
  have he3' : e₃ * e₃ = e₃ := he3
  obtain ⟨c3, hc3⟩ := Ideal.mem_span_singleton'.mp h3
  obtain ⟨d3, hd3⟩ := Ideal.mem_span_singleton'.mp h3'
  refine ⟨Ideal.Quotient.mk _ (e₁ + u * e₃), ?_, ?_, ?_⟩
  · show Ideal.Quotient.mk _ (e₁ + u * e₃) * Ideal.Quotient.mk _ (e₁ + u * e₃) =
      Ideal.Quotient.mk _ (e₁ + u * e₃)
    rw [← map_mul]
    exact congrArg (Ideal.Quotient.mk _)
      (by linear_combination he1' + 2 * e₃ * he1u + e₃ ^ 2 * hu2 + u * he3')
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (c3 * u), ?_⟩
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨-a1, by linear_combination -ha1 - u * hc3 + (c3 * g - c3 - e₃ * f + e₃) * hu2⟩
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (d3 * u), ?_⟩
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), ← map_sub, ← map_mul, ← map_mul, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-((1 - e₁) * a2), by
      linear_combination -(1 - e₁) * ha2 - g * hu - u * hd3 + (d3 * f - d3 - (1 - e₃) * g + (1 - e₃)) * hu2⟩

end GlobalTheory.CompanionTheory.ValQuot
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeRootValuationQuotient

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem untilt_mod_varpi_sq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest →
    ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧
      R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := by
  intro l _ A hA
  obtain ⟨t, ht⟩ := A.frob_bijective.2 A.pi
  have ht' : t ^ l = A.pi := ht
  have hpow : A.sharp t ^ l = (l : A.U) := by
    rw [← map_pow, ht', A.sharp_pi]
  refine ⟨A.sharp t, hpow, ?_⟩
  have hle : Ideal.span {(l : A.U) ^ 1} ≤ Ideal.span {A.sharp t ^ 2} := by
    rw [pow_one, ← hpow]
    exact Ideal.span_singleton_le_span_singleton.2
      (pow_dvd_pow _ (Fact.out : l.Prime).two_le)
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  let g : A.A →+* A.U ⧸ Ideal.span {A.sharp t ^ 2} :=
    (Ideal.Quotient.factor hle).comp A.aToU1
  have hg : Function.Surjective g :=
    (Ideal.Quotient.factor_surjective hle).comp hsurj
  have hπ : ∀ a ∈ Ideal.span {A.pi}, g a = 0 := fun a ha => by
    rw [← hker] at ha
    change Ideal.Quotient.factor hle (A.aToU1 a) = 0
    rw [RingHom.mem_ker.1 ha, map_zero]
  let g' : A.A ⧸ Ideal.span {A.pi} →+* A.U ⧸ Ideal.span {A.sharp t ^ 2} :=
    Ideal.Quotient.lift _ g hπ
  have hg' : Function.Surjective g' := Ideal.Quotient.lift_surjective_of_surjective _ hπ hg
  exact ⟨(GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective g' hg').2
      (GlobalTheory.CompanionTheory.ValQuot.valuation_comparable_quotient A.pi hA.2),
    (GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective g hg).1 hA.1⟩

end GlobalTheory.CompanionTheory.Untilt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeRootValuationQuotientStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.exists_prime_root_valuation_quotient : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧ R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq | exact GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq | (intros; apply GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq <;> assumption)
end
end
