module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Etale.StandardEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleFibreStandardEtaleSpreads
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComapIncludeRightFieldStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleFibreStandardEtaleSpreadsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.preirreducible_fibre_standardEtale_spreads : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (a : A) (I : Finset A), algebraMap A Ω a ≠ 0 ∧ (∀ c ∈ I, algebraMap A Ω c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], algebraMap A k a ≠ 0 → (∀ c ∈ I, algebraMap A k c = 0) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) := by
  first | exact @GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads | exact GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads | (intros; apply GlobalTheory.preirreducibleSpace_fibre_standardEtale_spreads <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleTensorLocalizationAway

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preirreducibleSpace_primeSpectrum_tensor_localizationAway
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k]
    [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  intro hX
  letI : Algebra (k ⊗[A] B) (k ⊗[A] Localization.Away b) :=
    (Algebra.TensorProduct.map (AlgHom.id A k)
      (IsScalarTower.toAlgHom A B (Localization.Away b))).toAlgebra
  haveI : IsScalarTower k (k ⊗[A] B) (k ⊗[A] Localization.Away b) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right A k (Submonoid.powers b)
    (Localization.Away b) (by ext; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at hl
  haveI : IsLocalization.Away
      (Algebra.TensorProduct.includeRight (R := A) (A := k) b) (k ⊗[A] Localization.Away b) := hl
  exact (PrimeSpectrum.localization_away_isOpenEmbedding (k ⊗[A] Localization.Away b)
    (Algebra.TensorProduct.includeRight (R := A) (A := k) b)).preirreducibleSpace

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleTensorLocalizationAwayStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.preirreducible_tensor_localization_away : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  first | exact @GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | exact GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | (intros; apply GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_basicOpen_fibres_preirreducible :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B →
    ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) →
    PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) →
    ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧
      (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧
      ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) →
        IsPreirreducible {r : PrimeSpectrum B |
          r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  intro A B _ _ _ hsm q Ω _ _ _ hq hΩ
  obtain ⟨b, hbq, n, _, hST, hSE⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := q.asIdeal)
  have hΩb := GlobalTheory.T.preirreducible_tensor_localization_away A B b Ω hΩ
  obtain ⟨a, I, haΩ, hIΩ, hall⟩ := GlobalTheory.T.preirreducible_fibre_standardEtale_spreads A (Localization.Away b) n hSE Ω hΩb
  have memq : ∀ x : A, algebraMap A B x ∈ q.asIdeal ↔ algebraMap A Ω x = 0 := by
    intro x
    have := congrArg (x ∈ ·) hq
    simpa [Ideal.mem_comap, RingHom.mem_ker] using this
  refine ⟨b, a, I, hbq, fun h => haΩ ((memq a).1 h), fun c hc => (memq c).2 (hIΩ c hc), ?_⟩
  intro t hat hIt
  let k := AlgebraicClosure t.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap A k) = t.asIdeal := by
    rw [IsScalarTower.algebraMap_eq A t.asIdeal.ResidueField k, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap t.asIdeal.ResidueField k).injective,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  have hmem : ∀ x : A, algebraMap A k x = 0 ↔ x ∈ t.asIdeal := by
    intro x; rw [← RingHom.mem_ker, hker]
  have hk := hall k (fun h => hat ((hmem a).1 h)) (fun c hc => (hmem c).2 (hIt c hc))
  have himg := (PreirreducibleSpace.isPreirreducible_univ (X := PrimeSpectrum (k ⊗[A] Localization.Away b))).image
    (PrimeSpectrum.comap ((Algebra.TensorProduct.includeRight :
      Localization.Away b →ₐ[A] k ⊗[A] Localization.Away b).toRingHom.comp
        (algebraMap B (Localization.Away b))))
    (PrimeSpectrum.continuous_comap _).continuousOn
  convert himg using 1
  rw [Set.image_univ, PrimeSpectrum.comap_comp, Set.range_comp,
    GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker, hker]
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hr, hbr⟩
    have : r ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]; exact hbr
    obtain ⟨r', rfl⟩ := this
    refine ⟨r', ?_, rfl⟩
    rw [← hr, IsScalarTower.algebraMap_eq A B (Localization.Away b), ← Ideal.comap_comap]
    rfl
  · rintro ⟨r', hr', rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hr', IsScalarTower.algebraMap_eq A B (Localization.Away b), ← Ideal.comap_comap]
      rfl
    · have : PrimeSpectrum.comap (algebraMap B (Localization.Away b)) r' ∈
          Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := ⟨r', rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at this
      exact this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmoothStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B → ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) → PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧ (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → IsPreirreducible {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  first | exact @GlobalTheory.exists_basicOpen_fibres_preirreducible | exact GlobalTheory.exists_basicOpen_fibres_preirreducible | (intros; apply GlobalTheory.exists_basicOpen_fibres_preirreducible <;> assumption)
end
end
