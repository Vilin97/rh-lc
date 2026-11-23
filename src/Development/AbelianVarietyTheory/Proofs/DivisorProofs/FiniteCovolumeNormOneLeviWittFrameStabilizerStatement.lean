module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovolStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicLeviNormOneLastColumnProdEquivStatement
import GroundTheory.AutomorphicForms.QuotientMeasure

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicFrameDecompositionOfWittFrame

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.FrameExt

theorem idem_factor {K : Type} [Field K] {n : ℕ} (Q : Matrix (Fin n) (Fin n) K) (hQ : Q * Q = Q) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K), Z * C = Q ∧ C * Z = 1 := by
  let W := LinearMap.range Q.mulVecLin
  let b := Module.finBasis K W
  have key : ∀ w : W, Q.mulVecLin.rangeRestrict (w : Fin n → K) = w := by
    rintro ⟨w, v, rfl⟩
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hQ]
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict)
        = Q.mulVecLin := LinearMap.ext fun v => by simp
    rw [this, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict) ∘ₗ (W.subtype ∘ₗ b.equivFun.symm.toLinearMap)
        = LinearMap.id := LinearMap.ext fun c => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, key,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    rw [this, LinearMap.toMatrix'_id]

end GlobalTheory.FrameExt

theorem GlobalTheory.FrameExt.exists_fr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW
  have hσ : ∀ e, σ (σ e) = e := fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e
  have ccT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) E), cT (σ : E →+* E) (cT (σ : E →+* E) M) = M :=
    fun M => Matrix.ext fun i j => by simp [Formalism.UG.cT, hσ]
  have cT0 : ∀ {p q : ℕ}, cT (σ : E →+* E) (0 : Matrix (Fin p) (Fin q) E) = 0 :=
    Matrix.ext fun i j => by simp [Formalism.UG.cT]
  have hJJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hBX : cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx hcm hJ hW
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := by rw [hA]; exact hW.xx
  have hAY : A * Y = 1 := by rw [hA]; exact hW.xy
  have hBY : B * Y = 0 := by rw [hB]; exact hW.yy
  have hBX' : B * X = 1 := by rw [hB]; exact hBX
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAQ : A * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY]
    simp
  have hBQ : B * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX', hBY]
    simp
  have hQQ : Q * Q = Q := by
    calc Q * Q = (1 - X * B - Y * A) * Q := by rw [← hQ]
      _ = Q - X * (B * Q) - Y * (A * Q) := by
        rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Q := by rw [hBQ, hAQ]; simp
  obtain ⟨m, Z, C, hZC, hCZ⟩ := GlobalTheory.FrameExt.idem_factor Q hQQ
  have hQZ : Q * Z = Z := by rw [← hZC, Matrix.mul_assoc, hCZ, Matrix.mul_one]
  have hAZ : A * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hAQ, Matrix.zero_mul]
  have hBZ : B * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hBQ, Matrix.zero_mul]

  have hzc : cT (σ : E →+* E) Z * J * X = 0 := by
    have := congrArg (cT (σ : E →+* E)) hAZ
    rwa [hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  have hzd : cT (σ : E →+* E) Z * J * Y = 0 := by
    have := congrArg (cT (σ : E →+* E)) hBZ
    rwa [hB, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀, J₀ = cT (σ : E →+* E) Z * J * Z := ⟨_, rfl⟩
  have hJ₀h : cT (σ : E →+* E) J₀ = J₀ := by
    rw [hJ₀, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, Matrix.mul_assoc]
  have key : cT (σ : E →+* E) Z * J = J₀ * C := by
    calc cT (σ : E →+* E) Z * J = cT (σ : E →+* E) Z * J * (X * B + Y * A + Z * C) := by
          rw [hZC, hQ]; simp
      _ = cT (σ : E →+* E) Z * J * X * B + cT (σ : E →+* E) Z * J * Y * A + J₀ * C := by
          rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ₀]
      _ = J₀ * C := by rw [hzc, hzd]; simp
  have hJZ : J * Z = cT (σ : E →+* E) C * J₀ := by
    have := congrArg (cT (σ : E →+* E)) key
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, hJ₀h] at this
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have hZ : Z = J⁻¹ * (cT (σ : E →+* E) C * J₀) := by
    rw [← hJZ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul]
  have hdet₀ : J₀.det ≠ 0 := by
    refine Matrix.det_ne_zero_of_left_inverse (B := C * J⁻¹ * cT (σ : E →+* E) C) ?_
    rw [← hCZ, hZ]; simp only [Matrix.mul_assoc]
  have hJ₀u : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hdet₀
  refine ⟨m, Z, J₀, ⟨hcm, hJ, ⟨fun i j => ?_, hdet₀⟩, hW.xx, hW.yy, hW.xy, hBX, ?_, ?_, hzc, hzd, hJ₀.symm, ?_, ?_⟩⟩
  · have := congrFun (congrFun hJ₀h i) j
    simpa [Formalism.UG.cT] using this
  · rw [← hA]; exact hAZ
  · rw [← hB]; exact hBZ
  · rw [← hA, ← hB, key, ← Matrix.mul_assoc J₀⁻¹, Matrix.nonsing_inv_mul _ hJ₀u, Matrix.one_mul, hZC, hQ]
    abel
  · have htr : (1 : Matrix (Fin n) (Fin n) E).trace = (X * B).trace + (Y * A).trace + (Z * C).trace := by
      rw [← Matrix.trace_add, ← Matrix.trace_add, hZC, hQ]; congr 1; abel
    rw [Matrix.trace_mul_comm X B, hBX', Matrix.trace_mul_comm Y A, hAY, Matrix.trace_mul_comm Z C, hCZ] at htr
    simp only [Matrix.trace_one, Fintype.card_fin] at htr
    have h3 : ((m + 2 * (r + 1) : ℕ) : E) = ((n : ℕ) : E) := by push_cast at htr ⊢; rw [htr]; ring
    exact Nat.cast_injective h3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicFrameDecompositionOfWittFrameStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.exists_isotropicFrameDecomposition_of_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  first | exact @GlobalTheory.FrameExt.exists_fr | exact GlobalTheory.FrameExt.exists_fr | (intros; apply GlobalTheory.FrameExt.exists_fr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTop

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory

theorem isFundamentalDomain_stdDom_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂] (μ : Measure (G₁ × G₂)) :
    IsFundamentalDomain (Γ₁.prod Γ₂) (GlobalTheory.AutomorphicL2Unitary.stdDom Γ₁ ×ˢ GlobalTheory.AutomorphicL2Unitary.stdDom Γ₂) μ := by
  refine .mk' ((GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₁).prod (GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₂)).nullMeasurableSet ?_
  rintro ⟨a, b⟩
  obtain ⟨γ₁, h₁, u₁⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₁ a
  obtain ⟨γ₂, h₂, u₂⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₂ b
  refine ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨h₁, h₂⟩, ?_⟩
  rintro ⟨⟨c, d⟩, hcd⟩ ⟨hc, hd⟩
  have e₁ := u₁ ⟨c, (Subgroup.mem_prod.1 hcd).1⟩ hc
  have e₂ := u₂ ⟨d, (Subgroup.mem_prod.1 hcd).2⟩ hd
  ext <;> simp [← e₁, ← e₂]

theorem measure_fundamentalDomain_prod_lt_top : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ₁ Γ₂ _ _ h₁ h₂ μ hμ 𝓕 h𝓕
  have hd := GlobalTheory.isFundamentalDomain_stdDom_prod Γ₁ Γ₂ μ
  haveI : Countable (Γ₁.prod Γ₂) := by
    have : Function.Injective (fun γ : Γ₁.prod Γ₂ => ((⟨(γ : G₁ × G₂).1, (Subgroup.mem_prod.1 γ.2).1⟩ : Γ₁),
      (⟨(γ : G₁ × G₂).2, (Subgroup.mem_prod.1 γ.2).2⟩ : Γ₂))) := by
      rintro ⟨⟨a, b⟩, _⟩ ⟨⟨c, d⟩, _⟩ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      ext <;> simp [h.1, h.2]
    exact this.countable
  rw [h𝓕.measure_eq hd]
  have hp : (Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂) |>.IsHaarMeasure := inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂)),
    Measure.smul_apply, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
  have a₁ := h₁ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₁ Measure.haar)
  have a₂ := h₂ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₂ Measure.haar)
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top a₁.lt_top a₂.lt_top)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTopStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.measure_fundamentalDomain_prod_lt_infty : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  first | exact @GlobalTheory.measure_fundamentalDomain_prod_lt_top | exact GlobalTheory.measure_fundamentalDomain_prod_lt_top | (intros; apply GlobalTheory.measure_fundamentalDomain_prod_lt_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizer

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.ResidueEisenstein

theorem finCovol_leviOne_last : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW π DM hπ hDM
  obtain ⟨m, Z, J₀, hF⟩ := GlobalTheory.T.exists_isotropicFrameDecomposition_of_wittFrame F E σ n J r X Y hcm hJ hW
  letI : MeasurableSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  set A := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hA
  set G₁ := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker
  set ΓA := (ratPts σ J).subgroupOf A
  set ΓG := (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range.subgroupOf G₁
  obtain ⟨hlc, hsc, hdisc, hfinGL⟩ := GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume F E σ hcm (r + 1)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.standardParabolicLeviNormOne_lastColumn_prodEquiv F E σ n J r m X Y Z J₀ hF
  have hclA : IsClosed (A : Set (GAd σ J)) :=
    (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const).inter
      (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const)
  haveI : LocallyCompactSpace A := hclA.locallyCompactSpace
  haveI : LocallyCompactSpace (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) :=
    (GlobalTheory.StdPar.isClosed_levi _ hcm hJ hW).2.locallyCompactSpace
  haveI := hlc
  haveI := hsc
  haveI := hdisc
  haveI : DiscreteTopology ΓA := DiscreteTopology.of_continuous_injective
    (f := fun x : ΓA => (⟨(x.1 : GAd σ J), x.2⟩ : ratPts σ J))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun a b h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun y : ratPts σ J => (y : GAd σ J)) h)
  haveI : Countable (ΓA.prod ΓG) := by
    haveI : Countable ΓA := inferInstance
    haveI : Countable ΓG := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact Function.Injective.countable (f := fun x : ΓA.prod ΓG => ((⟨x.1.1, x.2.1⟩ : ΓA), (⟨x.1.2, x.2.2⟩ : ΓG)))
      (fun a b h => Subtype.ext (Prod.ext (congrArg (fun q => (q.1 : A)) h) (congrArg (fun q => (q.2 : G₁)) h)))
  refine GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv (A × G₁) _ φ (ΓA.prod ΓG) _ (fun g => ?_)
    (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.measure_fundamentalDomain_prod_lt_infty A G₁ ΓA ΓG
      (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns F E σ n J (r + 1) m X Y Z J₀ hF μ 𝓕 hμ h𝓕) (fun μ hμ 𝓕 h𝓕 => hfinGL μ 𝓕 hμ h𝓕)
      μ hμ 𝓕 h𝓕) π DM hπ hDM
  rw [Subgroup.mem_prod, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hφ g]

end GlobalTheory.ResidueEisenstein
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizerStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.finiteCovolume_normOneLevi_wittFrameStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.ResidueEisenstein.finCovol_leviOne_last | exact GlobalTheory.ResidueEisenstein.finCovol_leviOne_last | (intros; apply GlobalTheory.ResidueEisenstein.finCovol_leviOne_last <;> assumption)
end
end
