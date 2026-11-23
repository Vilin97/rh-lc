module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomSpannedByClassSums
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleDualAlgebraicityFiniteData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassExistsFiniteReps
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTwistedClassSumsAlgebraic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ClassSumKernelIsAlgebraic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormBottom

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RowEx.BotField

theorem field_of_gens {T Hh κ : Type} [Finite T] (v : T → Hh → κ → ℂ) (good : Set Hh)
    (hab : ∃ (H : Finset Hh) (K : Finset κ) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧ (∀ h ∈ H, h ∈ good) ∧
      ∀ t, ∀ h ∈ good, ∀ k, ∃ c : Hh → κ → ℂ, (∀ a b, c a b ∈ M₀) ∧ v t h k = ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * v t h' k')
    (hc : ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, IsAlgebraic ℚ (v t h k / Ω)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, v t h k / Ω ∈ M := by
  obtain ⟨H, K, M₀, hM₀, hH, hv⟩ := hab
  obtain ⟨Ω, hΩ, halg⟩ := hc
  let S : Set ℂ := Set.range fun x : T × H × K => v x.1 x.2.1 x.2.2 / Ω
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  have hS : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro _ ⟨⟨t, h, k⟩, rfl⟩
    exact (halg t h (hH h h.2) k).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := IntermediateField.finiteDimensional_adjoin hS
  refine ⟨M₀ ⊔ IntermediateField.adjoin ℚ S, inferInstance, Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨c, hc, e⟩ := hv t h hh k
  rw [e, Finset.sum_div]
  refine sum_mem fun h' hh' => ?_
  rw [Finset.sum_div]
  refine sum_mem fun k' hk' => ?_
  rw [mul_div_assoc]
  refine mul_mem ((le_sup_left : M₀ ≤ _) (hc h' k')) ((le_sup_right : IntermediateField.adjoin ℚ S ≤ _) ?_)
  exact IntermediateField.subset_adjoin ℚ S ⟨⟨t, ⟨h', hh'⟩, ⟨k', hk'⟩⟩, rfl⟩

theorem sumsIn_mono {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {A A' WW : HSp D}
    {X : Tri T A A' WW} {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SumsIn W σ X)
    (hσ : Set.range σ ⊆ Set.range σ') : SumsIn W σ' X := by
  obtain ⟨Ω, Ω', h0, h0', H⟩ := h
  exact ⟨Ω, Ω', h0, h0', fun t g hg => ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end GlobalTheory.RowEx.BotField

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomSpannedByTwistedClassSums

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology
noncomputable section
namespace GlobalTheory.BotSpanSnd
open Formalism.L2.Fam.ThC (fixSig)
section General
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
end General
section Bottom
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
  {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
end Bottom
section Real
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
  {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
end Real
theorem twistedClassSums_span_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A'.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A'.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  classical
  obtain ⟨K, hK⟩ := vanish_off_finite hX
  obtain ⟨J, hJ, hl⟩ := level_right hX
  obtain ⟨H, hH, hc⟩ := _root_.GlobalTheory.BotClassFin.bottomClass_exists_finite_reps hP hI hL hX J hJ
  refine ⟨H, K, conjField D, finiteDimensional_conjField, hH, ?_⟩
  intro t h hh k
  obtain ⟨γ, hγ, r, hrI, h₀, hh₀, κ, hκJ, hκf, rfl⟩ := hc h hh
  have hx : h₀ * κ ∈ GfC WW := mul_mem (hH h₀ hh₀) hκf
  have hγr : γ * r ∈ GfC WW := by
    have e : γ * r = (γ * r * h₀ * κ) * (h₀ * κ)⁻¹ := by group
    rw [e]; exact mul_mem hh (inv_mem hx)
  obtain ⟨c, hcM, hcE⟩ := real_right hX t hγ hrI hγr (h₀ * κ) k
  have e1 : X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) (γ * r * h₀ * κ) =
      ∑ k' ∈ c.support, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ := by
    have e0 : γ * r * h₀ * κ = γ * ((h₀ * κ) * r) := by
      rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC WW hrI hx]; simp only [mul_assoc]
    rw [e0, rat_left hX t _ hγ, hcE]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [hl t κ hκJ hκf]
  refine ⟨fun h' k' => if h' = h₀ then c.coeff k' else 0, fun a b => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hcM b
    · exact zero_mem _
  rw [e1, Finset.sum_eq_single_of_mem h₀ hh₀ (fun b _ hb => by simp [hb])]
  simp only [if_true]
  calc ∑ k' ∈ c.support, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀
      = ∑ k' ∈ c.support ∪ K, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        Finset.sum_subset Finset.subset_union_left fun k' _ hk' => by
          rw [MvPolynomial.notMem_support_iff.1 hk', zero_mul]
    _ = ∑ k' ∈ K, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        (Finset.sum_subset Finset.subset_union_right fun k' _ hk' => by
          rw [hK t h₀ k' hk', mul_zero]).symm
end GlobalTheory.BotSpanSnd
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_spanned_by_twistedClassSums : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A'.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A'.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  first | exact @_root_.GlobalTheory.BotSpanSnd.twistedClassSums_span_bottom | exact _root_.GlobalTheory.BotSpanSnd.twistedClassSums_span_bottom | (intros; apply _root_.GlobalTheory.BotSpanSnd.twistedClassSums_span_bottom <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFieldIsNumberField

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.RowEx.BotField
theorem sums_mem_bottomField (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {T : Type} [Finite T] {L : LevCh D T}
    {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (hL : L.Is μ₀) (hX : IsBottomTri W i j X) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ SumsIn W (algebraMap M ℂ) X := by
  obtain ⟨M₁, h₁, Ω, hΩ, e₁⟩ := field_of_gens (fun t h k => X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (_root_.GlobalTheory.T.bottom_spanned_by_classSums hP hI hL hX) (_root_.GlobalTheory.T.bottom_classSums_algebraic hP hI hL hX)
  obtain ⟨M₂, h₂, Ω', hΩ', e₂⟩ := field_of_gens (fun t h k => X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (_root_.GlobalTheory.T.bottom_spanned_by_twistedClassSums hP hI hL hX) (_root_.GlobalTheory.T.bottom_twistedClassSums_algebraic hP hI hL hX)
  refine ⟨M₁ ⊔ M₂, inferInstance, Ω, Ω', hΩ, hΩ', fun t h hh => ⟨fun k _ => ?_, fun k _ => ?_⟩⟩
  · exact ⟨⟨_, (le_sup_left : M₁ ≤ _) (e₁ t h hh k)⟩, rfl⟩
  · exact ⟨⟨_, (le_sup_right : M₂ ≤ _) (e₂ t h hh k)⟩, rfl⟩
end GlobalTheory.RowEx.BotField
theorem GlobalTheory.RowEx.bottomField_isNumberField : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → NFBot := by
  intro hP hI
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => by
    haveI : Finite T := hS.fin
    have hL : R.toLevCh.Is A.μ0 := hS.core.lev
    have hex : ∀ ij : Fin D.R.m × Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
        ∃ (A₁ A₂ WW : HSp D) (X : Tri T A₁ A₂ WW), IsBottomTri ch.W ij.1 ij.2 X ∧ SumsIn ch.W (algebraMap M ℂ) X := by
      intro ij
      obtain ⟨A₁, A₂, WW, X, hX⟩ := exists_bottomTri hL ch.G ch.W ij.1 ij.2
      obtain ⟨M, hM, hs⟩ := _root_.GlobalTheory.RowEx.BotField.sums_mem_bottomField hP hI hL hX
      exact ⟨M, hM, A₁, A₂, WW, X, hX, hs⟩
    choose M hM hB using hex
    haveI := hM
    refine ⟨⨆ ij, M ij, IntermediateField.finiteDimensional_iSup_of_finite, fun i j => ?_⟩
    obtain ⟨A₁, A₂, WW, X, hX, hs⟩ := hB (i, j)
    refine ⟨A₁, A₂, WW, X, hX, GlobalTheory.RowEx.BotField.sumsIn_mono hs ?_⟩
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨z, (le_iSup M (i, j) : M (i, j) ≤ _) z.2⟩, rfl⟩
  ⟩⟩
end
end
end
end
