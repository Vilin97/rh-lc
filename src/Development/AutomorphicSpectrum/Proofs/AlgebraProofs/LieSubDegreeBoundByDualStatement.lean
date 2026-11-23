module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv
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
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LinearIndependentMapVec
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeBotAndMaxExistsStatement
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DotDualSubDegreeAnnihilator

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_dotDual_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W :=
  PositivityTheory.HtPt.Ch.subdeg_orth

end GlobalTheory.CompanionTheory.Ar.Crv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DotDualSubDegreeAnnihilatorStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.dot_dual_sub_degree_annihilator : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactSubDegreeBound

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes

theorem subDeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) :=
  @PositivityTheory.HtPt.Ch.subdeg_ses

end GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactSubDegreeBoundStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.short_exact_sub_degree_bound : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes.subDeg_ses | exact GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes.subDeg_ses | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes.subDeg_ses <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeMonoInjectiveHom

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_le_map_of_injective : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) :=
  PositivityTheory.HtPt.Ch.deg_inj

end GlobalTheory.CompanionTheory.Ar.Crv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeMonoInjectiveHomStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.sub_degree_mono_injective_hom : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LieSubDegreeBoundByDual

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.FrobEst

def dotOrth {K : Type} [Field K] {d : ℕ} (X : Submodule K (Fin d → K)) :
    Submodule K (Fin d → K) where
  carrier := {u | ∀ φ ∈ X, u ⬝ᵥ φ = 0}
  add_mem' := fun {a b} ha hb φ hφ => by rw [add_dotProduct, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' := fun φ _ => zero_dotProduct φ
  smul_mem' := fun c u hu φ hφ => by rw [smul_dotProduct, hu φ hφ, smul_zero]

theorem frob_estimate : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (O : Type) [CommRing O] [StarRing O] (d : ℕ) (D : ConjData C p O d), 2 < p →
    0 ≤ deg C (dotDual C D.lie) ∧
      ∀ W : Submodule K (Fin d → K),
        ((p : ℤ) - 2) * subDeg C D.lie W ≤ deg C (dotDual C D.lie) := by
  intro K _ C p _ _ O _ _ d D hp
  obtain ⟨h0, W₀, hW₀⟩ := GlobalTheory.T.sub_degree_bot_and_max_exists K C (Fin d → K) D.lie D.lie_bun
  have hp2 : (0 : ℤ) < (p : ℤ) - 2 := by
    have : (2 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    linarith
  have hf := GlobalTheory.CompanionTheory.Ar.Crv.SubFrob.subDeg_frob K C p d D.lie W₀ D.lie_bun
  have h1 := GlobalTheory.T.sub_degree_mono_injective_hom K C (Fin d → K) ((Fin d → K) × (Fin d → K))
    (frobLat C p D.lie) D.H D.α (frobSub p W₀)
    (GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat K C p d D.lie D.lie_bun).1 D.H_bun D.conj.1
    (fun i x hx => (D.conj.2.2.2.1 i x).1 hx)
  have h2 := GlobalTheory.T.short_exact_sub_degree_bound K C (Fin d → K) ((Fin d → K) × (Fin d → K)) (Fin d → K)
    (dotDual C D.lie) D.H D.lie (LinearMap.inr K (Fin d → K) (Fin d → K))
    (LinearMap.fst K (Fin d → K) (Fin d → K)) (Submodule.map D.α (frobSub p W₀)) D.H_bun D.hodge
  have h3 := GlobalTheory.T.dot_dual_sub_degree_annihilator K C d D.lie
    (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))))
    (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))) D.lie_bun (fun u => Iff.rfl)
  have h4 := hW₀ (Submodule.map (LinearMap.fst K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀)))
  have h5 := hW₀ (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀))))
  have hr : ((p : ℤ) - 2) * subDeg C D.lie W₀ = (p : ℤ) * subDeg C D.lie W₀ - 2 * subDeg C D.lie W₀ := by
    ring
  have key : ((p : ℤ) - 2) * subDeg C D.lie W₀ ≤ deg C (dotDual C D.lie) := by
    linarith
  have hμ : 0 ≤ subDeg C D.lie W₀ := by
    have := hW₀ ⊥
    linarith
  refine ⟨?_, fun W => ?_⟩
  · have := mul_nonneg hp2.le hμ
    linarith
  · have := mul_le_mul_of_nonneg_left (hW₀ W) hp2.le
    linarith

end GlobalTheory.CompanionTheory.Ar.Crv.FrobEst
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LieSubDegreeBoundByDualStatement

section

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.lie_sub_degree_bound_by_dual : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O : Type) [CommRing O] [StarRing O] (d : ℕ) (D : ConjData C p O d), 2 < p → 0 ≤ deg C (dotDual C D.lie) ∧ ∀ W : Submodule K (Fin d → K), ((p : ℤ) - 2) * subDeg C D.lie W ≤ deg C (dotDual C D.lie) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.FrobEst.frob_estimate | exact GlobalTheory.CompanionTheory.Ar.Crv.FrobEst.frob_estimate | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.FrobEst.frob_estimate <;> assumption)
end
end
