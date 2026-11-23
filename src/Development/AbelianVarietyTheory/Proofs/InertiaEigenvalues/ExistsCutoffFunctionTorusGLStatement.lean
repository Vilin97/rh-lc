module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.FieldTheory.Perfect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasureStatement
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocallyConstantCutoffClosedEmbedding
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitLeftMulMatrixOfCommuteCompanionStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyCompanionMatrixEtaleGeneratorSeparable

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem charpoly_companion_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F),
    A.IsGen τ p → (companion p).charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : CharZero F := hU.charZero
  set P := (companion p).charpoly with hP
  have hmon : P.Monic := Matrix.charpoly_monic _
  have hdeg : P.natDegree = r := by rw [hP, Matrix.charpoly_natDegree_eq_dim]; simp
  have hroot : Polynomial.aeval τ P = 0 := by
    apply Algebra.leftMulMatrix_injective (bas A hG)
    rw [map_zero, ← Polynomial.aeval_algHom_apply, leftMul_tau A hG]
    exact Matrix.aeval_self_charpoly _
  have hsmall : ∀ Q : Polynomial F, Q.natDegree < r → Polynomial.aeval τ Q = 0 → Q = 0 := by
    intro Q hQ h0
    rw [Polynomial.aeval_eq_sum_range' hQ] at h0
    rw [← Fin.sum_univ_eq_sum_range (fun i => Q.coeff i • τ ^ i) r] at h0
    have := Fintype.linearIndependent_iff.mp hG.1 (fun i => Q.coeff i) h0
    ext n
    by_cases hn : n < r
    · simpa using this ⟨n, hn⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  rw [PerfectField.separable_iff_squarefree]
  intro q hq
  obtain ⟨s, hs⟩ := hq
  by_contra hqu
  have hP0 : P ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hqdeg : 0 < q.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_ne_zero_of_nonunit hq0 hqu)
  have hQ0 : q * s ≠ 0 := mul_ne_zero hq0 hs0
  have hdegQ : (q * s).natDegree < r := by
    have : P.natDegree = q.natDegree + (q * s).natDegree := by
      rw [hs, mul_assoc, Polynomial.natDegree_mul hq0 hQ0]
    omega
  apply hQ0
  apply hsmall _ hdegQ
  have hnil : IsNilpotent (Polynomial.aeval τ (q * s)) := ⟨2, by
    rw [pow_two, ← map_mul]
    have : q * s * (q * s) = P * s := by rw [hs]; ring
    rw [this, map_mul, hroot, zero_mul]⟩
  exact hnil.eq_zero

end GlobalTheory.JR.LinDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyCompanionMatrixEtaleGeneratorSeparableStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.charpoly_companionMatrix_etaleGenerator_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → (companion p).charpoly.Separable := by
  first | exact @GlobalTheory.JR.LinDesc.charpoly_companion_separable | exact GlobalTheory.JR.LinDesc.charpoly_companion_separable | (intros; apply GlobalTheory.JR.LinDesc.charpoly_companion_separable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizerStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.conjugates_separable_matrix_compact_mod_centralizer : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ (A₀ : Matrix (Fin r) (Fin r) F), A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) F), IsCompact Z → ∃ C : Set (GL (Fin r) F), IsCompact C ∧ ∀ g : GL (Fin r) F, (g : Matrix (Fin r) (Fin r) F) * A₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ Z → ∃ c ∈ C, ∃ t : GL (Fin r) F, (t : Matrix (Fin r) (Fin r) F) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) F) ∧ g = c * t) ∧ ∀ (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ C : Set (Matrix.unitaryGroup (Fin r) E), IsCompact C ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * A₀ * star g.1 ∈ Z → ∃ c ∈ C, ∃ t : Matrix.unitaryGroup (Fin r) E, t.1 * A₀ = A₀ * t.1 ∧ g = c * t := by
  first | exact @GlobalTheory.OrbCpt.orbit_cpt | exact GlobalTheory.OrbCpt.orbit_cpt | (intros; apply GlobalTheory.OrbCpt.orbit_cpt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocallyConstantCutoffClosedEmbeddingStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_locallyConstant_cutoff_closedEmbedding : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  first | exact @GlobalTheory.CutOff.exists_cutoff | exact GlobalTheory.CutOff.exists_cutoff | (intros; apply GlobalTheory.CutOff.exists_cutoff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHom

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem tm_isClosedEmbedding : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin r → F) := (bas A hG).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : A.K ≃ₜ (Fin r → F) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  let g : (Fin r → F) →ₗ[F] Matrix (Fin r) (Fin r) F :=
    (Algebra.leftMulMatrix (bas A hG)).toLinearMap ∘ₗ e.symm.toLinearMap
  have hg : IsClosedEmbedding g := by
    refine LinearMap.isClosedEmbedding_of_injective ?_
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have h1 := Algebra.leftMulMatrix_injective (bas A hG) hxy
    exact e.symm.injective h1
  let f : A.K → Matrix (Fin r) (Fin r) F := fun x => Algebra.leftMulMatrix (bas A hG) x
  have hf : IsClosedEmbedding f := by
    have : f = g ∘ eh := by
      funext x; simp [f, g, eh, e]
    rw [this]; exact hg.comp eh.isClosedEmbedding
  haveI : T2Space A.K := eh.isEmbedding.t2Space
  have hfo : IsClosedEmbedding (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x))) :=
    MulOpposite.opHomeomorph.isClosedEmbedding.comp (hf.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hP : IsClosedEmbedding (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) :=
    hf.prodMap hfo
  have hK : IsClosedEmbedding (Units.embedProduct A.K) := Units.isClosedEmbedding_embedProduct
  have hM : IsClosedEmbedding (Units.embedProduct (Matrix (Fin r) (Fin r) F)) := Units.isClosedEmbedding_embedProduct
  have hcomp : (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG) =
      (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) ∘ Units.embedProduct A.K := by
    funext t
    simp only [Function.comp_apply, Units.embedProduct_apply, Prod.map_apply, MulOpposite.unop_op]
    refine Prod.ext ?_ ?_
    · exact tm_coe A hG t
    · simp only
      rw [tm_inv_coe]
  have hc : IsClosedEmbedding ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
    rw [hcomp]; exact hP.comp hK
  have hcont : Continuous (LinDesc.tm A hG) := by
    rw [hM.isInducing.continuous_iff]; exact hc.continuous
  refine ⟨⟨Topology.IsInducing.of_comp hcont hM.continuous hc.isInducing, ?_⟩, ?_⟩
  · intro x y hxy
    exact hc.injective (by simp [Function.comp_apply, hxy])
  · have : Set.range (LinDesc.tm A hG) = (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ⁻¹' Set.range ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
      ext x; constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨t, ht⟩; exact ⟨t, hM.injective ht⟩
    rw [this]; exact hc.isClosed_range.preimage hM.continuous

end GlobalTheory.JR.LinDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHomStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  first | exact @GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | exact GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | (intros; apply GlobalTheory.JR.LinDesc.tm_isClosedEmbedding <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCutoffFunctionTorusGL

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem gl_lc_td (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] [IsUltrametricDist F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ TotallyDisconnectedSpace (GL (Fin r) F) := by
  refine ⟨?_, ?_⟩
  · haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
      inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
    exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin r) (Fin r) F)).locallyCompactSpace
  · haveI : TotallyDisconnectedSpace (Matrix (Fin r) (Fin r) F) :=
      inferInstanceAs (TotallyDisconnectedSpace (Fin r → Fin r → F))
    exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem exists_cutoff_torus : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ α : GL (Fin r) F → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1 := by
  intro F E _ _ _ _ _ A r τ p hG lam μK hμ f' hf'
  haveI := (Unram.lcF (F := F) (E := E))
  haveI := (Unram.ultraF (F := F) (E := E))
  obtain ⟨hlc, htd⟩ := gl_lc_td F r
  obtain ⟨hB, hH, -⟩ := GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure F E A μK hμ
  have hZ : IsCompact (Prod.fst '' tsupport f') := hf'.2.isCompact.image continuous_fst
  obtain ⟨C, hC, hCg⟩ := (GlobalTheory.T.conjugates_separable_matrix_compact_mod_centralizer F E r).1 (companion p) (GlobalTheory.T.charpoly_companionMatrix_etaleGenerator_separable F E A r τ p hG) _ hZ
  obtain ⟨α, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_locallyConstant_cutoff_closedEmbedding (GL (Fin r) F) A.Kˣ (LinDesc.tm A hG)
    (GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom F E A r τ p hG) (LinDesc.unitsMeas A μK) C hC
  refine ⟨α, h1, h2, h3, ?_⟩
  rintro g ⟨v, w, hne⟩ s₀
  have hmem : (g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈
      Prod.fst '' tsupport f' := ⟨(_, v, w, lam), subset_tsupport _ (Function.mem_support.2 hne), rfl⟩
  obtain ⟨c, hc, t, ht, rfl⟩ := hCg g hmem
  obtain ⟨t₁, rfl⟩ := GlobalTheory.T.exists_unit_leftMulMatrix_of_commute_companion F E A r τ p hG t ht
  have := h4 c hc (t₁ * s₀)
  simpa [map_mul, mul_assoc] using this

end GlobalTheory.JR.LinDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCutoffFunctionTorusGLStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_cutoff_function_torus_GL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ α : GL (Fin r) F → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1 := by
  first | exact @GlobalTheory.JR.LinDesc.exists_cutoff_torus | exact GlobalTheory.JR.LinDesc.exists_cutoff_torus | (intros; apply GlobalTheory.JR.LinDesc.exists_cutoff_torus <;> assumption)
end
end
