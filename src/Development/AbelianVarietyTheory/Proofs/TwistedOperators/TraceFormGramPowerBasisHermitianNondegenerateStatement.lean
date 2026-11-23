module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarStarOfInvol

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem star'_star'_of_invol {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {n : ℕ} (P : PPol σ n) (l : Fld P) : star' P (star' P l) = l := by
  have h : ((star' P : Fld P →+* Fld P).comp (star' P : Fld P →+* Fld P)) = RingHom.id (Fld P) := by
    refine AdjoinRoot.ringHom_ext (p := P.1) ?_ ?_
    · ext e
      change star' P (star' P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e
      rw [star'_algebraMap, star'_algebraMap, hσ]
    · change star' P (star' P (alpha P)) = alpha P
      rw [star'_alpha, map_inv₀, star'_alpha, inv_inv]
  exact RingHom.congr_fun h l

theorem trace_star'_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (l : Fld P), Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  intro F E _ _ _ σ hσ n P l
  let e₁ : E ≃+* E := RingEquiv.ofRingHom (σ : E →+* E) (σ : E →+* E) (RingHom.ext hσ) (RingHom.ext hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofRingHom (star' P : Fld P →+* Fld P) (star' P : Fld P →+* Fld P)
    (RingHom.ext (star'_star'_of_invol hσ P)) (RingHom.ext (star'_star'_of_invol hσ P))
  have he : RingHom.comp (algebraMap E (Fld P)) (e₁ : E →+* E) = RingHom.comp (e₂ : Fld P →+* Fld P) (algebraMap E (Fld P)) := by
    ext e
    exact (star'_algebraMap P e).symm
  have h := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he l
  change _ = σ (Algebra.trace E (Fld P) (star' P l)) at h
  rw [h, hσ]

end GlobalTheory.TrEll
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceFormGramPowerBasisHermitianNondegenerate

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

theorem gramOne_herm_nd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), IsHermND σ (GlobalTheory.TrUnitLat.gramOne P) := by
  intro F E _ _ _ _ _ σ hcm r P
  have hσ : ∀ e, σ (σ e) = e := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have hs := star'_star'_of_invol hσ P
  have htr := trace_star'_eq F E σ hσ r P
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [gramOne, Matrix.of_apply]
    rw [← htr, map_mul, hs, mul_comm]
  · intro hdet
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hw0
    set b := powB P
    set z : Fld P := ∑ j, w j • b j with hz
    have h1 : ∀ i, Algebra.trace E (Fld P) (z * star' P (b i)) = 0 := by
      intro i
      have := congr_fun hw i
      simp only [Matrix.mulVec, dotProduct, gramOne, Matrix.of_apply, Pi.zero_apply] at this

      rw [hz, Finset.sum_mul, map_sum]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
    have h2 : ∀ u : Fld P, Algebra.trace E (Fld P) (z * u) = 0 := by
      intro u
      have hu : u = ∑ i, σ (b.repr (star' P u) i) • star' P (b i) := by
        conv_lhs => rw [← hs u, ← b.sum_repr (star' P u)]

        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, star'_algebraMap]

      rw [hu, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mul_smul_comm, map_smul, h1, smul_zero]
    have hz0 : z = 0 := (traceForm_nondegenerate E (Fld P)).1 z fun u => by
      rw [Algebra.traceForm_apply]; exact h2 u
    funext j
    exact Fintype.linearIndependent_iff.1 b.linearIndependent w (by rw [← hz0]) j

end GlobalTheory.TrUnitLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceFormGramPowerBasisHermitianNondegenerateStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.traceFormGramPowerBasis_hermitian_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), IsHermND σ (GlobalTheory.TrUnitLat.gramOne P) := by
  first | exact @GlobalTheory.TrUnitLat.gramOne_herm_nd | exact GlobalTheory.TrUnitLat.gramOne_herm_nd | (intros; apply GlobalTheory.TrUnitLat.gramOne_herm_nd <;> assumption)
end
end
