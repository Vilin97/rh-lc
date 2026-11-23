module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianOverSubfield
public import Formalism.ConjugateSelfDual.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCoreLeFixingSubgroupNormalClosure

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.NormalClosureSolv

open Pointwise

variable {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω]

theorem algebraMap_mem_smul_iff (γ : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (c : F) :
    algebraMap F Ω c ∈ γ • A ↔ algebraMap F Ω c ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.commutes]

theorem isPlaceOver_smul' [NumberField F] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (γ : Ω ≃ₐ[F] Ω) : IsPlaceOver (γ • A) v := by
  intro x
  rw [← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, algebraMap_mem_smul_iff,
    algebraMap_mem_smul_iff, map_inv₀]

end GlobalTheory.NormalClosureSolv
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemRealOfSq

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh55.mem_real_of_sq :
    ∀ {Y : Type} [inst : Field Y] {δ : Y}
    {q : ℕ}, (0 : ℕ) < q → δ ^ (2 : ℕ) = (↑q : Y) → δ ∈ NumberField.maximalRealSubfield Y := by
  intro Y _ δ q hq h
  rw [NumberField.mem_maximalRealSubfield_iff]
  intro φ
  have h1 : (φ δ) ^ 2 = (q : ℂ) := by rw [← map_pow, h, map_natCast]
  have h2 : (φ δ) ^ 2 = ((Real.sqrt q : ℝ) : ℂ) ^ 2 := by
    rw [h1, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
  · rw [h3, Complex.star_def, Complex.conj_ofReal]
  · rw [h3, star_neg, Complex.star_def, Complex.conj_ofReal]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Double

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem over_under {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
  rw [IsScalarTower.algebraMap_apply F K Ω]
  exact h (algebraMap (𝓞 F) (𝓞 K) x)

private theorem smul_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (g' : G K' Ω) (hg : ∀ x, g x = g' x) : g • A = g' • A := by
  apply SetLike.coe_injective
  rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
  ext x
  simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]

private theorem mem_real_of_sq {Y : Type} [Field Y] {δ : Y} {q : ℕ} (hq : 0 < q) (hδ : δ ^ 2 = (q : Y)) :
    δ ∈ maximalRealSubfield Y :=
  _root_.UpperTheory.Reformulated.B.Qh55.mem_real_of_sq hq hδ

private theorem algebraMap_mem_real {E Y : Type} [Field E] [Field Y] [Algebra E Y] {x : E}
    (hx : x ∈ maximalRealSubfield E) : algebraMap E Y x ∈ maximalRealSubfield Y :=
  (mem_maximalRealSubfield_iff _).2 fun φ => (mem_maximalRealSubfield_iff x).1 hx (φ.comp (algebraMap E Y))

private theorem apart_of_moves {E Y Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Y] [NumberField Y] [IsCMField Y]
    [Field Ω] [Algebra E Y] [Algebra E Ω] [Algebra Y Ω] [IsScalarTower E Y Ω] [IsAlgClosure Y Ω] {δ : Y} {q : ℕ} (hq : 0 < q)
    (hδ : δ ^ 2 = (q : Y)) (A : ValuationSubring Ω) (σ : G E Ω) (hσ : σ (algebraMap Y Ω δ) = -algebraMap Y Ω δ)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield E) A, g (algebraMap Y Ω δ) = algebraMap Y Ω δ)
    {w₁ w₂ : HeightOneSpectrum (𝓞 Y)} (hw₁ : IsPlaceOver A w₁) (hw₂ : IsPlaceOver (σ • A) w₂) : GlobalTheory.Cong.Apart w₁ w₂ := by
  intro hv
  haveI : IsAlgClosure (maximalRealSubfield Y) Ω :=
    ⟨IsAlgClosure.isAlgClosed Y, Algebra.IsAlgebraic.trans _ Y Ω⟩
  have h1 := over_under (F := maximalRealSubfield Y) hw₁
  have h2 := over_under (F := maximalRealSubfield Y) hw₂
  rw [← hv] at h2
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver h1 h2
  have hδr : δ ∈ maximalRealSubfield Y := mem_real_of_sq hq hδ
  have hρδ : ρ (algebraMap Y Ω δ) = algebraMap Y Ω δ := ρ.commutes (⟨δ, hδr⟩ : maximalRealSubfield Y)
  have hρF : ∀ x : maximalRealSubfield E, ρ.toRingEquiv (algebraMap (maximalRealSubfield E) Ω x) =
      algebraMap (maximalRealSubfield E) Ω x := fun x => by
    have h := ρ.commutes (⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ : maximalRealSubfield Y)
    have e : algebraMap (maximalRealSubfield Y) Ω ⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ =
        algebraMap (maximalRealSubfield E) Ω x := by
      change algebraMap Y Ω (algebraMap E Y x) = algebraMap E Ω x
      exact (IsScalarTower.algebraMap_apply E Y Ω _).symm
    rw [e] at h
    exact h
  let ρ' : G (maximalRealSubfield E) Ω := AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρF
  let σ' : G (maximalRealSubfield E) Ω := σ.restrictScalars _
  have hg : ρ'⁻¹ * σ' ∈ Dec (F := maximalRealSubfield E) A := mem_Dec.2 (by
    rw [mul_smul, inv_smul_eq_iff, smul_congr A σ' σ (fun _ => rfl), ← hρ, smul_congr A ρ' ρ (fun _ => rfl)])
  have h3 := hfix _ hg
  have h4 : σ' (algebraMap Y Ω δ) = ρ' (algebraMap Y Ω δ) := by
    have := congrArg ρ' h3
    rwa [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply ρ', mul_inv_cancel, AlgEquiv.one_apply] at this
  have h5 : -algebraMap Y Ω δ = algebraMap Y Ω δ := by
    have a : σ' (algebraMap Y Ω δ) = σ (algebraMap Y Ω δ) := rfl
    have b : ρ' (algebraMap Y Ω δ) = ρ (algebraMap Y Ω δ) := rfl
    rw [a, b, hσ, hρδ] at h4
    exact h4
  haveI : CharZero Y := algebraRat.charZero Y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  have h6 : algebraMap Y Ω δ = 0 := self_eq_neg.1 h5.symm
  have h7 : δ = 0 := (map_eq_zero _).1 h6
  rw [h7] at hδ
  have : (q : Y) = 0 := by simpa using hδ.symm
  exact hq.ne' (by exact_mod_cast this)

theorem double : Double := by
  intro E Ω _ _ _ _ _ _ T Q h0 t ht
  obtain ⟨⟨δ, ⟨⟨q, hq, hδ⟩, _, s, hs, hsδ⟩, hfix⟩, _, _⟩ := h0
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω t
  let σ : G E Ω := AlgEquiv.ofRingEquiv (f := s) (fun x => hs (algebraMap E Ω) x)
  have hA' : IsPlaceOver (σ • A) t := GlobalTheory.NormalClosureSolv.isPlaceOver_smul' hA σ
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA'
  exact ⟨w₁, w₂, eq_of_isPlaceOver (over_under hw₁) hA, eq_of_isPlaceOver (over_under hw₂) hA',
    apart_of_moves hq hδ A σ hsδ (hfix t ht A hA) hw₁ hw₂⟩

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end
end
