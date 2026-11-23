module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinFub
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SquareIntegrableInnerProduct
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HcParamGapGeIndex
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidUniversal
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ExistsOrthogonalProjectionInner
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ClosedIrreducibleLowestTypeData

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem mem_closure_generated_of_mem {ε : Fin n → Bool} (W' : Submodule ℂ (smD ε (rreg ε))) {v : smD ε (rreg ε)}
    (hv : v ∈ W') : (v : L2 ε) ∈ closGen (smE ε (rreg ε)) W' := by
  apply Submodule.le_topologicalClosure
  refine ⟨v, ?_, rfl⟩
  exact (le_sInf fun _ hT => hT.1 : W' ≤ genSub (smE ε (rreg ε)) W') hv

theorem closure_generated_isClosed {ε : Fin n → Bool} (W' : Submodule ℂ (smD ε (rreg ε))) :
    IsClosed (closGen (smE ε (rreg ε)) W' : Set (L2 ε)) :=
  Submodule.isClosed_topologicalClosure _

theorem exists_integral_parameter (lam : Fin n → ℝ) (hlam : S7.IsHCParam lam) : ∃ μ : Fin n → ℤ, S7.IsMu lam μ := by
  choose m hm using hlam.2
  refine ⟨fun a => m a + (n : ℤ) - 1 - ((a : ℕ) : ℤ), fun a => ?_⟩
  have := hm a
  simp only [rho]
  push_cast
  linarith

theorem closed_irreducible_lowest_type_data (ε : Fin n → Bool) (lam' : Fin n → ℝ) (h : ℝ) (hstd : StdGap ε lam')
    (hlam : S7.IsHCParam lam') (hgl : GapAtLeast ε lam' h) (hq0 : 1 ≤ S7.q0 ε)
    (h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h) (W' : Submodule ℂ (smD ε (rreg ε)))
    (hirr : IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W')
    (hcas : ∀ v ∈ W', casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v)
    (hK : ∀ k' ∈ Kset ε, ∀ v ∈ W', ∃ v'' ∈ W', (v'' : L2 ε) = rreg ε k' (v : L2 ε)) :
    ∃ (T' : S7.KType ε (lowK ε lam')) (μ' : Fin n → ℤ), S7.IsMu lam' μ' ∧
      ∃ C : ℝ, 0 < C ∧ ∃ d : ℝ, 0 < d ∧
      (∀ v ∈ W', ∃ t : T'.V, ∀ g ∈ UJset ε,
        ⟪((v : smD ε (rreg ε)) : L2 ε), rreg ε g (v : L2 ε)⟫_ℂ = (C : ℂ) * ⟪t, S7.PsiM T' μ' g t⟫_ℂ) ∧
      (∀ g ∈ UJset ε, ∀ x ∈ closGen (smE ε (rreg ε)) W', rreg ε g x ∈ closGen (smE ε (rreg ε)) W') ∧
      ∀ a ∈ closGen (smE ε (rreg ε)) W', ∀ b ∈ closGen (smE ε (rreg ε)) W',
        ∀ a' ∈ closGen (smE ε (rreg ε)) W', ∀ b' ∈ closGen (smE ε (rreg ε)) W',
        Integrable (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
          star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) (Formalism.REAL.muG ε) ∧
        ∫ y, ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪b', b⟫_ℂ * ⟪a, a'⟫_ℂ / (d : ℂ) := by
  obtain ⟨T'⟩ := HW.kType_exists_of_dom ε (lowK ε lam') (HW.lowK_int_dom ε lam' hlam).1
    (HW.lowK_int_dom ε lam' hlam).2
  obtain ⟨μ', hμ⟩ := exists_integral_parameter lam' hlam
  have hP : IsPsiFor ε lam' T' (S7.PsiM T' μ') :=
    (S7.isPsiFor_psiM ε lam' h T' μ' hlam hμ hgl hq0 h8).1
  have hv₀ := HW.KType.w_ne_zero T'
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV2 := datumV_isKIrrHW hP hv₀
  have hc2 := datumV_casimir hP T'.w
  have hVK2 := datumV_kStable hP T'.w
  have hV20 := datumV_ne_bot hP hv₀
  have hW0 : W' ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hirr.2.2.2
    intro hb
    rw [hb] at hw
    exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ hD hirr hσ hD hV2
  have huniv := rigid_universal hσ hD hirr hcas hK hσ hD hV2 hc2 hVK2 hstd φ hφK hφI
  have hjw := datumEmbedding_highest_ne_zero hstd hP hv₀
  have hstab := closGen_stable hstd hσ hD hirr hcas hK
  obtain ⟨U0, hU0⟩ := data_unitary_equiv hstd hσ hD hirr hcas hK hW0 hσ hD hV2 hc2 hVK2 hV20
  let U : closGen (smE ε (rreg ε)) W' ≃ₗᵢ[ℂ] Hlam ε (S7.PsiM T' μ') T'.w := U0
  have hU : ∀ g ∈ UJset ε, ∀ x y : closGen (smE ε (rreg ε)) W', (x : L2 ε) = rreg ε g (y : L2 ε) →
      ((U x : Hlam ε (S7.PsiM T' μ') T'.w) : L2 ε) = rreg ε g ((U y : Hlam ε (S7.PsiM T' μ') T'.w) : L2 ε) :=
    hU0
  obtain ⟨d, hd0, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam' (sigLam ε (S7.PsiM T' μ') T'.w)
    (isDS_sigLam hstd hP hv₀)
  refine ⟨T', μ', hμ, ‖uniformisationL2 ε (S7.PsiM T' μ') T'.w T'.w‖ ^ 2, by positivity, d, hd0, ?_, hstab, ?_⟩
  · intro v hv
    have hmem : ((φ ⟨v, hv⟩ : datumV ε (S7.PsiM T' μ') T'.w) : smD ε (rreg ε)) ∈
        LinearMap.range (jSm hP T'.w) := by
      rw [← datumV_eq_range hP T'.w]; exact (φ ⟨v, hv⟩).2
    obtain ⟨t, ht⟩ := hmem
    have ht' : (((φ ⟨v, hv⟩ : datumV ε (S7.PsiM T' μ') T'.w) : smD ε (rreg ε)) : L2 ε) =
        uniformisationL2 ε (S7.PsiM T' μ') T'.w t := by rw [← ht]; rfl
    refine ⟨t, fun g hg => ?_⟩
    have e := huniv g hg ⟨v, hv⟩ ⟨v, hv⟩
    rw [ht'] at e
    rw [← formulaF hstd hP hv₀ hg t t]
    exact e.symm
  · intro a ha b hb a' ha' b' hb'
    have key : ∀ (x z : closGen (smE ε (rreg ε)) W') (y : Formalism.REAL.UJ ε),
        ⟪(x : L2 ε), rreg ε (Formalism.MainNotions.S.umat y) (z : L2 ε)⟫_ℂ =
          Formalism.MainNotions.S.coefOn (sigLam ε (S7.PsiM T' μ') T'.w) (U z) (U x) y := by
      intro x z y
      have hy : Formalism.MainNotions.S.umat y ∈ UJset ε := unitary_matrix_mem_set ε y
      let z' : closGen (smE ε (rreg ε)) W' := ⟨rreg ε (Formalism.MainNotions.S.umat y) z, hstab _ hy _ z.2⟩
      have e1 := hU _ hy z' z rfl
      show _ = ⟪U x, sigLam ε (S7.PsiM T' μ') T'.w (Formalism.MainNotions.S.umat y) (U z)⟫_ℂ
      rw [Submodule.coe_inner, sigLam_coe hstd hP hv₀ hy, ← e1, ← Submodule.coe_inner,
        LinearIsometryEquiv.inner_map_map, Submodule.coe_inner]
    have hfun : (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
          star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) =
        fun y => Formalism.MainNotions.S.coefOn (sigLam ε (S7.PsiM T' μ') T'.w) (U ⟨b, hb⟩) (U ⟨a, ha⟩) y *
          star (Formalism.MainNotions.S.coefOn (sigLam ε (S7.PsiM T' μ') T'.w) (U ⟨b', hb'⟩) (U ⟨a', ha'⟩) y) := by
      funext y
      rw [← key ⟨a, ha⟩ ⟨b, hb⟩ y, ← key ⟨a', ha'⟩ ⟨b', hb'⟩ y]
    rw [hfun]
    refine ⟨(hd _ _ _ _).1, ?_⟩
    rw [(hd _ _ _ _).2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map,
      Submodule.coe_inner, Submodule.coe_inner]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ReproducingFormulaClosedInvariant

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem convolution_integral_fubini {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (f : L2 ε)
    (hFc : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)))
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hγ : MemLp (fGam ε f) 2 (Formalism.REAL.muG ε)) {N : Set (Formalism.REAL.UJ ε)}
    (hNf : Formalism.REAL.muG ε N ≠ ∞) (x : Formalism.REAL.UJ ε) :
    ∫ z in N, fPhi ε F f (z * x) ∂(Formalism.REAL.muG ε) =
      ∫ y, (∫ z in N, F (Formalism.MainNotions.S.umat (z * y)) ∂(Formalism.REAL.muG ε)) * fGam ε f (y⁻¹ * x)
        ∂(Formalism.REAL.muG ε) := by
  set μ := Formalism.REAL.muG ε with hμ
  have e1 : (fun z => fPhi ε F f (z * x)) =
      fun z => ∫ y, F (Formalism.MainNotions.S.umat (z * y)) * fGam ε f (y⁻¹ * x) ∂μ := by
    funext z
    unfold fPhi
    rw [← integral_mul_left_eq_self (fun y => F (Formalism.MainNotions.S.umat y) * fGam ε f (y⁻¹ * (z * x))) z]
    congr 1
    funext y
    congr 2
    group
  rw [e1]
  set G2 : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε → ℂ :=
    fun z y => F (Formalism.MainNotions.S.umat (z * y)) * fGam ε f (y⁻¹ * x) with hG2
  have hcont : Continuous (Function.uncurry G2) := by
    show Continuous fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat (p.1 * p.2)) * fGam ε f (p.2⁻¹ * x)
    exact (hFc.comp continuous_mul).mul ((matrix_coefficient_continuous ε f).comp (continuous_snd.inv.mul continuous_const))
  have hB : MemLp (fun y => fGam ε f (y⁻¹ * x)) 2 μ :=
    hγ.comp_measurePreserving ((measurePreserving_mul_right ε x).comp (Measure.measurePreserving_inv μ))
  have hA : ∀ z, MemLp (fun y => F (Formalism.MainNotions.S.umat (z * y))) 2 μ :=
    fun z => hF2.comp_measurePreserving (measurePreserving_mul_left μ z)
  have hint : Integrable (Function.uncurry G2) ((μ.restrict N).prod μ) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun z => (hA z).integrable_mul hB, ?_⟩
    have : IsFiniteMeasure (μ.restrict N) := isFiniteMeasure_restrict.2 hNf
    refine Integrable.of_bound hcont.aestronglyMeasurable.norm.integral_prod_right'
      ((∫ y, ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ y, ‖fGam ε f (y⁻¹ * x)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hH := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun y => F (Formalism.MainNotions.S.umat (z * y))) (g := fun y => fGam ε f (y⁻¹ * x))
      (by rw [ENNReal.ofReal_ofNat]; exact hA z) (by rw [ENNReal.ofReal_ofNat]; exact hB)
    have ht : ∫ y, ‖F (Formalism.MainNotions.S.umat (z * y))‖ ^ (2 : ℝ) ∂μ = ∫ y, ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ) ∂μ :=
      integral_mul_left_eq_self (fun y => ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ)) z
    rw [ht] at hH
    refine le_of_eq_of_le ?_ hH
    simp only [Function.uncurry_apply_pair, hG2, norm_mul]
  rw [integral_integral_swap hint]
  congr 1
  funext y
  exact integral_mul_const _ _

theorem reproducing_formula_closed_invariant {K : Submodule ℂ (L2 ε)} {d : ℝ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hFc : ContinuousOn F (UJset ε))
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hKc : IsClosed (K : Set (L2 ε))) (hfK : toL2 ε F ∈ K)
    (hKs : ∀ g ∈ UJset ε, ∀ u ∈ K, rreg ε g u ∈ K)
    (hS : ∀ a ∈ K, ∀ b ∈ K, ∀ a' ∈ K, ∀ b' ∈ K,
      Integrable (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
        star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) (Formalism.REAL.muG ε) ∧
      ∫ y, ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ
        ∂(Formalism.REAL.muG ε) = ⟪b', b⟫_ℂ * ⟪a, a'⟫_ℂ / (d : ℂ)) :
    ∀ x ∈ UJset ε, ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪toL2 ε F, rreg ε ((Formalism.MainNotions.S.umat y)⁻¹ * x) (toL2 ε F)⟫_ℂ ∂(Formalism.REAL.muG ε) =
      ⟪toL2 ε F, toL2 ε F⟫_ℂ / (d : ℂ) * F x := by
  intro x hx
  obtain ⟨x, rfl⟩ := exists_unitary_preimage ε hx
  set f := toL2 ε F with hfdef
  set μ := Formalism.REAL.muG ε with hμ
  set c : ℂ := ⟪f, f⟫_ℂ / (d : ℂ) with hc
  have hL : ∫ y, F (Formalism.MainNotions.S.umat y) * ⟪f, rreg ε ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x) f⟫_ℂ ∂μ =
      fPhi ε F f x := by
    unfold fPhi fGam
    congr 1
    funext y
    rw [unitary_matrix_mul, unitary_matrix_inv_alt]
  rw [hL]
  have hFc' : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) :=
    hFc.comp_continuous (continuous_unitary_matrix ε) (fun g => unitary_matrix_mem_set ε g)
  have hγ : MemLp (fGam ε f) 2 μ := matrix_coefficient_memLp ε hS hfK hfK
  set D : Formalism.REAL.UJ ε → ℂ := fun w => fPhi ε F f w - c * F (Formalism.MainNotions.S.umat w) with hD
  have hDc : Continuous D := (convolution_coefficient_continuous hS hF2 hfK).sub (continuous_const.mul hFc')
  by_contra hne
  have hδ : D x ≠ 0 := fun h0 => hne (sub_eq_zero.1 h0)
  have hδp : 0 < ‖D x‖ := norm_pos_iff.2 hδ
  have hDz : Continuous fun z : Formalism.REAL.UJ ε => D (z * x) := hDc.comp (continuous_id.mul continuous_const)
  have hev : ∀ᶠ z in 𝓝 (1 : Formalism.REAL.UJ ε), ‖D (z * x) - D x‖ < ‖D x‖ / 2 := by
    have ht := hDz.tendsto 1
    simp only [one_mul] at ht
    have := (Metric.tendsto_nhds.1 ht) (‖D x‖ / 2) (by linarith)
    simpa [dist_eq_norm] using this
  obtain ⟨C₀, hC₀c, hC₀n⟩ := exists_compact_mem_nhds (1 : Formalism.REAL.UJ ε)
  set N := interior ({z | ‖D (z * x) - D x‖ < ‖D x‖ / 2} ∩ C₀) with hN
  have hNo : IsOpen N := isOpen_interior
  have h1N : (1 : Formalism.REAL.UJ ε) ∈ N := mem_interior_iff_mem_nhds.2 (Filter.inter_mem hev hC₀n)
  have hNC : N ⊆ C₀ := interior_subset.trans Set.inter_subset_right
  have hNP : ∀ z ∈ N, ‖D (z * x) - D x‖ < ‖D x‖ / 2 := fun z hz => (interior_subset hz).1
  have hNlt : μ N < ∞ := lt_of_le_of_lt (measure_mono hNC) hC₀c.measure_lt_top
  have hNf : μ N ≠ ∞ := hNlt.ne
  have hNpos : 0 < μ N := hNo.measure_pos μ ⟨1, h1N⟩
  have hNr : 0 < (μ N).toReal := ENNReal.toReal_pos hNpos.ne' hNf
  have hNm : MeasurableSet N := hNo.measurableSet
  have hIphi : IntegrableOn (fun z => fPhi ε F f (z * x)) N μ :=
    (((convolution_coefficient_continuous hS hF2 hfK).comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact
      hC₀c).mono_set hNC
  have hIF : IntegrableOn (fun z => F (Formalism.MainNotions.S.umat (z * x))) N μ :=
    ((hFc'.comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact hC₀c).mono_set hNC
  have hkey : ∫ z in N, fPhi ε F f (z * x) ∂μ = c * ∫ z in N, F (Formalism.MainNotions.S.umat (z * x)) ∂μ := by
    rw [convolution_integral_fubini f hFc' hF2 hγ hNf x]
    have e2 : (fun y => (∫ z in N, F (Formalism.MainNotions.S.umat (z * y)) ∂μ) * fGam ε f (y⁻¹ * x)) =
        fun y => ⟪(indicatorConstLp 2 hNm hNf (1 : ℂ) : L2 ε), rreg ε (Formalism.MainNotions.S.umat y) f⟫_ℂ *
          fGam ε f (y⁻¹ * x) := by
      funext y
      rw [inner_indicator_right_regular ε hF2 hNm hNf y]
      rfl
    rw [e2, schur_orthogonality_integral hKc hKs hS hfK, inner_indicator_right_regular ε hF2 hNm hNf x, hc]
    simp only [unitary_matrix_mul]
    ring
  have hzero : ∫ z in N, D (z * x) ∂μ = 0 := by
    simp only [hD]
    rw [integral_sub hIphi (hIF.const_mul c), integral_const_mul, hkey, sub_self]
  have hID : IntegrableOn (fun z => D (z * x)) N μ := hIphi.sub (hIF.const_mul c)
  have hIc : IntegrableOn (fun _ : Formalism.REAL.UJ ε => D x) N μ :=
    (continuous_const.continuousOn.integrableOn_compact hC₀c).mono_set hNC
  have hNr' : 0 < μ.real N := hNr
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun z => D (z * x) - D x) hNlt
    (fun z hz => (hNP z hz).le)
  rw [integral_sub hID hIc, hzero, setIntegral_const,
    zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg hNr'.le] at hbound
  nlinarith [mul_pos hNr' hδp]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinProj

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem finProj (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (Wf : Submodule ℂ (Mat k r → ℂ)) (W' : Submodule ℂ (smD ε (rreg ε)))
    (hWf : ∀ F ∈ Wf, ContinuousOn F (UJset ε) ∧ ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (hW' : ∀ v : smD ε (rreg ε), v ∈ W' ↔ ∃ F ∈ Wf, (v : L2 ε) = toL2 ε F)
    (hirr : IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W')
    (hcas : ∀ v ∈ W', casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v)
    (hK : ∀ k' ∈ Kset ε, ∀ v ∈ W', ∃ v'' ∈ W', (v'' : L2 ε) = rreg ε k' (v : L2 ε))
    (F : Mat k r → ℂ) (hF : F ∈ Wf) (hFW : ∃ v ∈ W', v ≠ 0 ∧ (v : L2 ε) = toL2 ε F) :
    ∃ (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ) (v₁ v₂ : T'.V), S7.IsMu lam' μ' ∧
      ∀ x ∈ UJset ε, F x = ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪v₂, S7.PsiM T' μ' ((Formalism.MainNotions.S.umat y)⁻¹ * x) v₁⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  obtain ⟨v, hvW, hv0, hvF⟩ := hFW
  obtain ⟨hq0, hNd⟩ := gapNeed k r ε h hp hq hgap
  have hstd : StdGap ε lam' := by
    refine ⟨hlam.1, h, hgl, ?_⟩
    have h1 := hgap.1
    have h2 := le_max_right (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2)
      (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith
  have h8 : 8 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < h := by
    have hmq : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ) := by
      delta S7.q0
      simp only [Nat.cast_min]
    unfold hNeed at hNd
    rw [hmq, max_lt_iff, max_lt_iff] at hNd
    obtain ⟨-, hB, -⟩ := hNd
    have hs := Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))
    have hnq : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    nlinarith
  obtain ⟨T', μ', hμ, C, hC, d, hd, hcoef, hstab, hS⟩ :=
    closed_irreducible_lowest_type_data ε lam' h hstd hlam hgl hq0 h8 W' hirr hcas hK
  obtain ⟨t, ht⟩ := hcoef v hvW
  rw [hvF] at ht
  have hf0 : toL2 ε F ≠ 0 := by
    intro h0; apply hv0; apply Subtype.ext; rw [hvF, h0]; rfl
  have hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
    by_contra hn; exact hf0 (toL2_eq_zero_of_not_memLp ε hn)
  have hfK : toL2 ε F ∈ closGen (smE ε (rreg ε)) W' := hvF ▸ mem_closure_generated_of_mem W' hvW
  have hrep := reproducing_formula_closed_invariant (hWf F hF).1 hF2 (closure_generated_isClosed W') hfK hstab hS
  have hff : ⟪toL2 ε F, toL2 ε F⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hf0
  have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  set κ : ℂ := (C : ℂ) * (d : ℂ) / ⟪toL2 ε F, toL2 ε F⟫_ℂ with hκ
  refine ⟨T', μ', κ • t, t, hμ, fun x hx => ?_⟩
  obtain ⟨x', rfl⟩ := exists_unitary_preimage ε hx
  have e : ∀ y : Formalism.REAL.UJ ε, F (Formalism.MainNotions.S.umat y) *
      ⟪t, S7.PsiM T' μ' ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x') (κ • t)⟫_ℂ =
      (κ / C) * (F (Formalism.MainNotions.S.umat y) *
        ⟪toL2 ε F, rreg ε ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x') (toL2 ε F)⟫_ℂ) := by
    intro y
    have hg : (Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x' ∈ UJset ε := by
      rw [← unitary_matrix_inv_alt, ← unitary_matrix_mul]; exact unitary_matrix_mem_set ε _
    rw [ht _ hg, map_smul, inner_smul_right]
    field_simp
  rw [integral_congr_ae (ae_of_all _ e), integral_const_mul, hrep _ hx, hκ]
  field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ToL2EqZeroOfEqZeroOnUJset

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem toL2_eq_zero_of_eq_zero_on_UJset {n : ℕ} (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ g ∈ UJset ε, F g = 0) : toL2 ε F = 0 := by
  have h0 : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = 0 :=
    funext fun g => hF _ (unitary_matrix_mem_set ε g)
  have hm : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
    rw [h0]
    exact MemLp.zero
  rw [toL2_eq_memLp_toLp ε hm]
  exact (hm.toLp_congr MemLp.zero (ae_of_all _ (congrFun h0))).trans (MemLp.toLp_zero _)

theorem finStep : FinStatement := by
  intro hIS k r ε u lam' h z c Vp _ _ _ π μW μN P hP hB hp hq hgap hlam hgl ξ Wf W' hWf hW' hirr hcas hK hinj
  obtain ⟨w, hwW, hw0, -⟩ := hirr.2.2.2
  obtain ⟨F, hF, hwF⟩ := (hW' w).1 hwW
  have hne : ∃ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := toL2_eq_zero_of_eq_zero_on_UJset ε F (hinj F hF hcon)
    exact hw0 (Subtype.ext (hwF.trans h0))
  obtain ⟨x, hx, hxne⟩ := hne
  obtain ⟨T', μ', v₁, v₂, hμ, hrep⟩ :=
    finProj k r ε lam' h hp hq hgap hlam hgl Wf W' hWf hW' hirr hcas hK F hF ⟨w, hwW, hw0, hwF⟩
  obtain ⟨hFc, C, hFb⟩ := hWf F hF
  obtain ⟨x₀, hx₀, hne0⟩ := finFub hIS k r ε u lam' h z c Vp π μW μN P hP hB hp hq hgap hlam hgl T' μ' hμ v₁ v₂ ξ F C
    hFc hFb hrep x hx hxne
  exact ⟨T', μ', P, z, c, Vp, inferInstance, inferInstance, inferInstance, π, μW, μN, hμ, hP, hB,
    v₁, v₂, ξ, x₀, x, hx₀, hx, hne0⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end
