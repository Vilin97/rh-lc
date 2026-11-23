module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparisonStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.de_rham_representation_tensor_comparison : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  first | exact @GlobalTheory.Per.ExactMult.exact_hodge_add | exact GlobalTheory.Per.ExactMult.exact_hodge_add | (intros; apply GlobalTheory.Per.ExactMult.exact_hodge_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLattices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.Per.SESJumps

theorem isJumpV_iff_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  intro l _ P AI hT K LL T₀ T₁ T₂ ι π hS _ h₁ _ τ a
  obtain ⟨hi, hs, -, hex, -⟩ := hS
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hex x).symm
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h₁).1
  exact ((GlobalTheory.T.de_rham_representation_tensor_comparison l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f ι.equiv π.equiv
    hi hs hrk hDR).2.2 τ a).2.2

end GlobalTheory.Per.SESJumps
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLatticesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

theorem _root_.GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  first | exact @GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | exact GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | (intros; apply GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat <;> assumption)
end
end
