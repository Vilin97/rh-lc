module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyActMemLatVIff

section

@[expose] public section

open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatFix

section Gen

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]

theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (x y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis R b).repr x i *
        (Algebra.TensorProduct.basis R b).repr y j * algebraMap F R (b.repr (b i * b j) k) := by
  classical
  set B := Algebra.TensorProduct.basis R b with hB
  conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y]

  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
  Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hB, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]
  simp

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem eventually_integral (c : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := by
  exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) c).2

theorem eventually_mul_closed {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ x y : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x * y) k ∈
        v.adicCompletionIntegers F := by
  classical
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ i j k : Fin d,
      algebraMap F (Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    exact fun i j k => eventually_integral _
  filter_upwards [h] with v hv x y hx hy k
  rw [repr_mul]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (hv i j k)

end Adelic

end GlobalTheory.CompanionTheory.SW.LatFix
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePreservedCofinitelyByUnit

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat

theorem eventually_cV_mul_mem_latV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (y : (AF F ⊗[F] E)ˣ), ∀ᶠ v in cofinite, ∀ Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E, (fun a i => cV v (y : AF F ⊗[F] E) * Y a i) ∈ latV b v ↔ Y ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b y
  have e1 := GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b
    (projFin (fun _ _ : Fin 1 => (y : AF F ⊗[F] E)))
  have e2 := GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b
    (projFin (fun _ _ : Fin 1 => ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)))
  filter_upwards [e1, e2, GlobalTheory.CompanionTheory.SW.LatFix.eventually_mul_closed b] with v h1 h2 h3 Y
  have c1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (cV v (y : AF F ⊗[F] E)) k ∈ v.adicCompletionIntegers F := fun k => h1 0 0 k
  have c2 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (cV v ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) k ∈ v.adicCompletionIntegers F :=
    fun k => h2 0 0 k
  have hone : cV v ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * cV v (y : AF F ⊗[F] E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  constructor
  · intro hY a i k
    have h := h3 _ _ c2 (hY a i) k
    rwa [← mul_assoc, hone, one_mul] at h
  · intro hY a i k
    exact h3 _ _ c1 (hY a i) k

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePreservedCofinitelyByUnitStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem _root_.GlobalTheory.T.lattice_preserved_cofinitely_by_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (y : (AF F ⊗[F] E)ˣ), ∀ᶠ v in cofinite, ∀ Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E, (fun a i => cV v (y : AF F ⊗[F] E) * Y a i) ∈ latV b v ↔ Y ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat.eventually_cV_mul_mem_latV_iff | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat.eventually_cV_mul_mem_latV_iff | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat.eventually_cV_mul_mem_latV_iff <;> assumption)
end
end
