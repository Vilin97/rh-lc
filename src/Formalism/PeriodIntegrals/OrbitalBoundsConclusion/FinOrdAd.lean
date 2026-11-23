module

public import Formalism.PeriodIntegrals.FinOrdAd
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DefPosDef
public import Formalism.PeriodIntegrals.PowBddInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Development
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TensCpctDen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitKron
public import Formalism.PeriodIntegrals.UnitKron

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.EvalIntMapEqZero

section

@[expose] public section

namespace PI.PowBddIntWork

open Matrix Polynomial

theorem eval₂_int_map_eq_zero {A B : Type*} [Ring A] [Ring B] (ψ : A →+* B) (p : ℤ[X]) (a : A)
    (h : p.eval₂ (algebraMap ℤ A) a = 0) : p.eval₂ (algebraMap ℤ B) (ψ a) = 0 := by
  have e : ψ.comp (algebraMap ℤ A) = algebraMap ℤ B := RingHom.ext_int _ _
  rw [← e, ← Polynomial.hom_eval₂, h, map_zero]

theorem stepB : StepB := by
  intro E _ k γ hγ i
  obtain ⟨p, hpm, hp⟩ := hγ
  let F := AlgebraicClosure E
  let γ' : Matrix (Fin k) (Fin k) F := γ.map (algebraMap E F)
  have hp' : p.eval₂ (algebraMap ℤ (Matrix (Fin k) (Fin k) F)) γ' = 0 :=
    eval₂_int_map_eq_zero (algebraMap E F).mapMatrix p γ hp

  have hroot : ∀ μ ∈ γ'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have hs : μ ∈ spectrum F γ' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic γ').ne_zero).1 hμ
    have h1 := spectrum.subset_polynomial_aeval γ' (p.map (algebraMap ℤ F)) ⟨μ, hs, rfl⟩
    have h2 : Polynomial.aeval γ' (p.map (algebraMap ℤ F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp']
    rw [h2] at h1
    refine ⟨p, hpm, ?_⟩
    have h3 : (p.map (algebraMap ℤ F)).eval μ = p.eval₂ (algebraMap ℤ F) μ := Polynomial.eval_map _ _
    rw [← h3]
    by_contra hne
    rw [spectrum.mem_iff, sub_zero] at h1
    exact h1 ((Ne.isUnit hne).map _)
  have hcp : γ'.charpoly = γ.charpoly.map (algebraMap E F) := Matrix.charpoly_map γ _
  have hinj : Function.Injective ((algebraMap E F).toIntAlgHom) := (algebraMap E F).injective
  rw [← isIntegral_algHom_iff _ hinj]
  show IsIntegral ℤ (algebraMap E F (γ.charpoly.coeff i))
  rw [← Polynomial.coeff_map, ← hcp]

  have hq : γ'.charpoly.Monic := Matrix.charpoly_monic _
  have hcard : Multiset.card γ'.charpoly.roots = γ'.charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)
  by_cases hi : i ≤ γ'.charpoly.natDegree
  · rw [Polynomial.coeff_eq_esymm_roots_of_card hcard hi, hq.leadingCoeff, one_mul]
    refine IsIntegral.mul (IsIntegral.pow (IsIntegral.neg isIntegral_one) _) ?_
    show _ ∈ integralClosure ℤ F
    unfold Multiset.esymm
    refine Subalgebra.multiset_sum_mem _ ?_
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hy
    refine Subalgebra.multiset_prod_mem _ ?_
    intro x hx
    exact hroot x (Multiset.mem_of_le (Multiset.mem_powersetCard.1 hs).1 hx)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact isIntegral_zero

end PI.PowBddIntWork
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Imports

section

@[expose] public section

namespace PI.PowBddIntWork

open Matrix NumberField

theorem stepA : StepA := by
  intro E _ _ k γ N hN hint
  classical
  let L : (Fin k → Fin k → 𝓞 E) →ₗ[ℤ] Matrix (Fin k) (Fin k) E :=
    { toFun := fun B => Matrix.of fun i j => ((N : E))⁻¹ * algebraMap (𝓞 E) E (B i j)
      map_add' := fun B C => by ext i j; simp [mul_add]
      map_smul' := fun c B => by
        ext i j
        first | (simp [zsmul_eq_mul]; ring) | simp [zsmul_eq_mul] }
  have hfg : (Submodule.map L ⊤).FG := Module.Finite.fg_top.map L
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ {γ}) ≤ Submodule.map L ⊤ := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
    refine ⟨fun i j => IsIntegralClosure.mk' (𝓞 E) ((N : E) * (γ ^ n) i j) (hint n i j), trivial, ?_⟩
    have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
    ext i j
    simp [L, IsIntegralClosure.algebraMap_mk', hN']
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  exact isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ {γ}) (isNoetherian_of_le hle) γ
    (Algebra.subset_adjoin (Set.mem_singleton γ))

end PI.PowBddIntWork
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PowBddInt

section

@[expose] public section

theorem power_bounded_integral : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicFiniteOrder.Assembly

section

@[expose] public section

noncomputable section

namespace PI

open NumberField IsDedekindDomain TensorProduct Matrix

theorem charpoly_int_of_powers_in_compact (hT : TensCpctDen) (hP : PowBddInt)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ)
    (γ : Matrix (Fin k) (Fin k) E) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ C : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F), IsCompact C →
    (∀ (n : ℕ) (i j : Fin k), inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) ((γ ^ n) i j) ∈ C) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i) := by
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro C hC hmem
  obtain ⟨N, hN, hNC⟩ := hT F E C hC
  exact hP E k γ N hN (fun n i j => hNC _ (hmem n i j))

theorem continuous_conj_entry (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (k : ℕ)
    (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (i j : Fin k) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) := by
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  let : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  have : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have : ContinuousAdd (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  have hmul : ∀ c d : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Continuous (fun z => c * z * d) := by
    intro c d
    have := IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F)
      ((LinearMap.mulRight (FiniteAdeleRing (𝓞 F) F) d).comp
        (LinearMap.mulLeft (FiniteAdeleRing (𝓞 F) F) c))
    exact this
  have he : ∀ a b : Fin k, Continuous (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      (u : Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hfun : (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) =
      fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => ∑ b, ∑ a, (y : Matrix (Fin k) (Fin k) _) i a *
        (u : Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b *
        ((y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin k) (Fin k) _) b j := by
    funext u
    simp only [Units.val_mul, Matrix.mul_apply, Finset.sum_mul]
  rw [hfun]
  exact continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun a _ => (hmul _ _).comp (he a b)

theorem finOrdAd_of (hU : UnitKron) (hP : PowBddInt) (hT : TensCpctDen) (hD : DefPosDef) : FinOrdAd := by
  intro F E _ _ _ _ _ hreal σ k J hH hDef U _hUle hUc y _hy γ hγ hbc
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, Units.ext (Matrix.ext fun i _ => Fin.elim0 i)⟩
  · obtain ⟨hc, hdef⟩ := hD F E hreal σ k J hk hH hDef
    obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.mp hbc
    have hint := charpoly_int_of_powers_in_compact hT hP F E k (γ : Matrix (Fin k) (Fin k) E)
      (⋃ (i : Fin k) (j : Fin k), (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
        ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) '' (U : Set _))
      (isCompact_iUnion fun i => isCompact_iUnion fun j => hUc.image (continuous_conj_entry F E k y i j))
      (by
        intro n i j
        have h1 : bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) (γ ^ n) = y * u ^ n * y⁻¹ := by
          rw [map_pow, ← hyu, ← map_pow]
          rfl
        refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, u ^ n, U.pow_mem hu n, ?_⟩⟩
        show ((y * u ^ n * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j = _
        rw [← h1, ← Units.val_pow_eq_pow_val]
        rfl)
    have hγ' : ((γ : Matrix (Fin k) (Fin k) E).map (σ : E →+* E))ᵀ * J * (γ : Matrix (Fin k) (Fin k) E) = J := hγ
    obtain ⟨n, hn, hpow⟩ := hU E (σ : E →+* E) hc k J γ hdef hγ' hint
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Units.ext (by rw [Units.val_pow_eq_pow_val, hpow]; simp)⟩

end PI
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdAd

section

@[expose] public section

theorem finite_order_adelic : PI.FinOrdAd :=
  PI.finOrdAd_of unit_kronecker power_bounded_integral tensor_compact_dense positive_definite_form
end
end
