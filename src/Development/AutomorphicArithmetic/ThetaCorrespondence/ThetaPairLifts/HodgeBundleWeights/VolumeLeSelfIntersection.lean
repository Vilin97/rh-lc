module

public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfKnownTheorem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystem
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOver
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfB
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.BigOperators.Field
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
import Mathlib.Tactic.Basify

-- Source module: CompanionTheory.AutomorphicTheory.KrullDimension.TopologicalKrullDimModel

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHt

namespace ModelDimension.ModelDim

theorem ringKrullDim_eq {A Ω : Type} [CommRing A] [Field Ω] [CharZero Ω] (φ : A →+* Ω)
    (hφ : Function.Injective φ) (hfr : ∀ x : Ω, ∃ a b : A, x = φ a / φ b) (hft : Algebra.FiniteType ℤ A) {d : ℕ}
    (hd : Algebra.trdeg ℤ Ω = d) : ringKrullDim A = (d + 1 : ℕ) := by
  have : IsDomain A := hφ.isDomain φ
  have : CharZero A := φ.charZero
  let _ : Algebra A Ω := φ.toAlgebra
  have : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : IsFractionRing A Ω := IsFractionRing.of_field _ _ hfr
  have : Algebra.IsAlgebraic A Ω := IsLocalization.isAlgebraic Ω (nonZeroDivisors A)
  have h1 := GroundTheory.Heights₂.Heights.IntDomainDim.proof A (algebraMap ℤ A).injective_int
  rw [h1, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top ℤ A Ω, hd, Cardinal.toENat_nat]
  norm_cast

theorem topologicalKrullDim_model {o Ω : Type} [CommRing o] [Field Ω] [CharZero Ω] [Algebra o Ω]
    (ho : Algebra.FiniteType ℤ o) (M : GlobalTheory.ZH.RatModel o Ω) {d : ℕ} (hd : Algebra.trdeg ℤ Ω = d) :
    topologicalKrullDim M.Z = (d + 1 : ℕ) := by
  have := M.lft
  have : LocallyOfFiniteType (spMap (Int.castRingHom o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ho)
  let t : M.Z ⟶ Sp ℤ := M.s ≫ spMap (Int.castRingHom o)
  have ht : LocallyOfFiniteType t := inferInstance
  have key (U : M.Z.Opens) (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) :
      topologicalKrullDim (U : Set M.Z) = (d + 1 : ℕ) := by
    have h1 : (t.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType t ht ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    have e : (t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom =
      algebraMap ℤ Γ(M.Z, U) := RingHom.ext_int _ _
    rw [← RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of ℤ)).inv, e,
      RingHom.finiteType_algebraMap] at h1
    refine ((GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(M.Z, U)))).trans ?_
    refine ringKrullDim_eq (M.res U hne) (M.res_injective U hne) (fun x => ?_) h1 hd
    obtain ⟨a, b, -, h⟩ := GlobalTheory.ZH.RatModel.exists_eq_div hU hne x
    exact ⟨a, b, by rw [M.res_apply, M.res_apply]; exact h⟩
  apply le_antisymm
  · refine GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact ⟨U, U.isOpen, hx, (key U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint M.Z) trivial
    rw [← key U hU ⟨_, hx⟩]
    exact topologicalKrullDim_subspace_le _ _

theorem trdeg_eq {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (hg : GlobalTheory.DegVal.GenRatios ev) {d : ℕ} (hd : 0 < imageDeg ev d) :
    Algebra.trdeg K Ω = d := by
  obtain ⟨N, b, f, hf⟩ := (imageDeg_pos_iff ev d).1 hd
  set y : Fin N → Ω := fun j => ev (b j) with hy
  have hy0 : y ≠ 0 := fun h => hg.1 (b.ext fun j => congrFun h j)
  have hgen : Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
    have hj' : y j ≠ 0 := hj
    set F := Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) with hF
    have h1 : ∀ v, ev v / y j ∈ F := fun v => by

      rw [← b.sum_repr v, map_sum, Finset.sum_div]
      refine sum_mem fun i _ => ?_
      rw [map_smul, Algebra.smul_def, mul_div_assoc]
      exact mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩))
    have h2 := congrArg IntermediateField.toSubfield hg.2
    rw [GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h2
    refine top_unique (h2 ▸ Subfield.closure_le.2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨v, w, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [← div_div_div_cancel_right₀ hj']
      exact div_mem (h1 v) (h1 w)
  have := isPrime_coneIdeal (K := K) y
  have hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = (d + 1 : ℕ) :=
    GlobalTheory.ConeDeg.ringKrullDim_of_isChowFormInt
      (fun g hg n => homogeneousComponent_mem_of_mem (isHomogeneous_coneIdeal y) hg n) hf
  obtain ⟨e, he1, he2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K (MvPolynomial (Fin N) K ⧸ coneIdeal K y)
  obtain rfl : e = d + 1 := by exact_mod_cast he1.symm.trans hdim
  let φ := Ideal.kerLiftAlg (coneMap K y)
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective _
  let A := φ.range
  let e := AlgEquiv.ofInjective φ hφ
  have hQA : Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = Algebra.trdeg K A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self φ (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := GlobalTheory.Adelic.ConeDim.isAlgebraic_of_closure_eq_top y hy0 hgen A hXy
  have : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top K A (Polynomial Ω), ← trdeg_add_eq K Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain, Nat.cast_add, Nat.cast_one] at he2
  exact (Cardinal.add_one_inj).1 he2

end ModelDimension.ModelDim
end
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfA

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField MeasureTheory GlobalTheory.ChowHt GlobalTheory.HeightUnique ReciprocityTheory.MultiplicativeHeights

namespace PositivityTheory.UnitarySelfGeneration.FrameHeightScaling

theorem linSubst_smul {B N δ : ℕ} (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) {f : MvPolynomial (Fin B × Fin N) ℂ}
    (hf : IsMultiHomogeneous (fun _ => δ) f) : linSubst (c • A) f = C (c ^ (B * δ)) * linSubst A f := by
  refine MvPolynomial.funext fun u => ?_
  rw [map_mul, eval_C, GlobalTheory.SphereMeanFrame.eval_linSubst, GlobalTheory.SphereMeanFrame.eval_linSubst, eval_eq', eval_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : ∑ p, s p = B * δ := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun b _ => hf s hs b]
    simp
  have h2 : ∀ p : Fin B × Fin N, ∑ k, (c • A) p.2 k * u (p.1, k) = c * ∑ k, A p.2 k * u (p.1, k) := fun p => by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  simp only [h2, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1]
  ring

theorem blockSphereMean_C {B n : ℕ} (hn : 0 < n) (z : ℂ) :
    blockSphereMean B n (C z) = Real.log ‖z‖ := by
  have hP : IsProbabilityMeasure (blockSphereProb B n) := by
    have : NeZero n := ⟨hn.ne'⟩
    have hne : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
      rw [Ne, Measure.measure_univ_eq_zero]
      exact Measure.toSphere_ne_zero _
    have : IsProbabilityMeasure (sphereProb n) := by
      unfold sphereProb
      exact ProbabilityTheory.cond_isProbabilityMeasure hne
    unfold blockSphereProb
    infer_instance
  unfold blockSphereMean
  simp

theorem formHeight_smul {F : Type} [Field F] [NumberField F] {B N n δ : ℕ} (hN : 0 < N)
    (w : Matrix (Fin N) (Fin n) F) {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0)
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous (fun _ => δ) f) (r : ℝ) :
    formHeight δ w (fun σ => ((Real.exp r : ℝ) : ℂ) • A σ) f = formHeight δ w A f + B * δ * r := by
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hc : ((Real.exp r : ℝ) : ℂ) ^ (B * δ) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.exp_pos r).ne')
  have hinf : ∀ σ : F →+* ℂ, blockSphereMean B N (linSubst (((Real.exp r : ℝ) : ℂ) • A σ) (MvPolynomial.map σ f)) =
      B * δ * r + blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) := by
    intro σ
    have hm := isMultiHomogeneous_map_ring _ f ha σ
    rw [linSubst_smul _ _ hm, sphere_mean_mul_multihomogeneous Closed.sphereLogIntegrable B N 0 _ _ _
      (by rwa [Ne, MvPolynomial.C_eq_zero])
      (linSubst_ne_zero ((A σ).mul_nonsing_inv (hA σ).isUnit) fun h =>
        hf (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero])))
      (isMultiHomogeneous_iff_block.2 (isWeightedHomogeneous_C _ _)) (linSubst_homog _ hm), blockSphereMean_C hN,
      norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos r).le, Real.log_pow, Real.log_exp]
    push_cast
    ring
  unfold formHeight
  simp only [hinf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul]
  field_simp
  ring

theorem frameNorm_smul {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {c : ℂ} (hc : c ≠ 0)
    (x : Fin N → ℂ) : frameNorm (c • A) x = ‖c⁻¹‖ * frameNorm A x := by
  have h : (c • A)⁻¹ = c⁻¹ • A⁻¹ := Matrix.inv_eq_left_inv (by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, Matrix.nonsing_inv_mul _ hA.isUnit])
  simp only [frameNorm, h, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem conjCompat_smul {F : Type} [Field F] {N : ℕ} {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ σ, (A σ).det ≠ 0) (h : ConjCompat A) {c : ℂ} (hc : c ≠ 0) : ConjCompat fun σ => c • A σ := fun σ x => by
  rw [frameNorm_smul (hA _) hc, frameNorm_smul (hA _) hc, h σ x]

theorem sum_smul {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (v : Fin m → ℂ) :
    ∑ a, ‖∑ k, (c • M) k a * v k‖ ^ 2 = ‖c‖ ^ 2 * ∑ a, ‖∑ k, M k a * v k‖ ^ 2 := by
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, norm_mul, mul_pow]

theorem archSize_smul_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    GlobalTheory.Adelic.archSize (c • A) x ^ 2 = ‖c‖ ^ 2 * GlobalTheory.Adelic.archSize A x ^ 2 := by
  rw [GlobalTheory.Adelic.archSize, GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), sum_smul]

end PositivityTheory.UnitarySelfGeneration.FrameHeightScaling
end
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelModel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model

theorem exists_comb {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N m : ℕ} (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) (v : V) :
    ∃ c : Fin m → K, ev v = ∑ k, algebraMap K Ω (c k) * ev (∑ j, g j k • b j) := by
  have hmem : (⇑(b.repr v) : Fin N → K) ∈ Submodule.span K (Set.range g.col) := by
    rw [hg]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨c, ?_⟩
  have hv : v = ∑ k, c k • ∑ j, g j k • b j := by
    conv_lhs => rw [← b.sum_repr v]
    rw [← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    rfl
  rw [hv]

  simp only [map_sum, map_smul, Algebra.smul_def]

theorem closure_eq_top {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {m : ℕ} (t : Fin m → Ω)
    (ht : ∀ v, ∃ c : Fin m → K, ev v = ∑ k, algebraMap K Ω (c k) * t k) (i : Fin m) (hi : t i ≠ 0)
    (hr : IntermediateField.adjoin K {a : Ω | ∃ v w, a = ev v / ev w} = ⊤) :
    Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ := by
  set F := Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) with hF
  have hK : ∀ x : K, algebraMap K Ω x ∈ F := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    rw [map_div₀]
    have e : ∀ y : 𝓞 K, algebraMap K Ω (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) Ω y :=
      fun y => (IsScalarTower.algebraMap_apply (𝓞 K) K Ω y).symm
    rw [e, e]
    exact div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))
  have key : ∀ u, ev u / t i ∈ F := by
    intro u
    obtain ⟨c, hc⟩ := ht u
    rw [hc, Finset.sum_div]
    refine sum_mem fun k _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (hK (c k)) (Subfield.subset_closure (Or.inr ⟨i, k, rfl⟩))
  have hS : {a : Ω | ∃ v w, a = ev v / ev w} ⊆ (F.toIntermediateField hK : Set Ω) := by
    rintro _ ⟨v, w, rfl⟩
    show ev v / ev w ∈ F
    rw [← div_div_div_cancel_right₀ hi (ev v) (ev w)]
    exact div_mem (key v) (key w)
  have hle := (IntermediateField.adjoin_le_iff).2 hS
  rw [hr] at hle
  exact eq_top_iff.2 fun x _ => hle (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K Ω))

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeLeSelfIntersection

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open PositivityTheory.UnitarySelfGeneration.FrameHeightScaling
theorem PositivityTheory.UnitarySelfGeneration.volume_le_self_intersection : PositivityTheory.UnitarySelfGeneration.ChowFormHeight → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (t : ℝ), IsFrame Nm L b g A → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev d → ∀ (M : GlobalTheory.ZH.RatModel (𝓞 K) Ω), M.HasDiv (fun k => ev (∑ j, g j k • b j)) → GlobalTheory.IsArithVar M.s d → ∀ (H : ReciprocityTheory.ChartRestriction.G.Semi.LB M.Z) (hH : H.IsLB) (e : H.ι → Ω), M.GenTriv H e → ∀ (s : Fin m → H.Sec), (∀ k, M.HasVal e (s k) (ev (∑ j, g j k • b j))) → ∀ (hs : ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) (hdet : ∀ σ, (Mt σ).det ≠ 0) (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U), (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2) → ((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).shift (fun _ => t) (fun _ => rfl)).IsSelfInter (((d : ℝ) + 1) * (Module.finrank ℚ K : ℝ) * (imageDeg ev d : ℝ) * (imageHeight Nm L ev d + t)) := by
  intro HP hP K V Ω _ _ _ _ _ _ _ _ Nm L ev d N m b g A t hF hG hd M hNm hX H hH e he s hv hs Mt hdet hc hMt
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hcomb := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model.exists_comb ev b g hF.full
  obtain ⟨i, hi, -⟩ := hNm (genericPoint M.Z)
  have htop := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model.closure_eq_top ev (fun k => ev (∑ j, g j k • b j))
    hcomb i hi hG.2
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.pos; omega⟩
  obtain ⟨Z, hZ, hZp⟩ := GlobalTheory.ZH.exists_isCl_isProjOver (𝓞 K) Ω n _ ⟨i, hi⟩ htop
  have hZX : GlobalTheory.IsArithVar Z.s d := by
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ K := Algebra.IsAlgebraic.trans ℤ ℚ K
    have h1 : Algebra.trdeg ℤ Ω = d :=
      (GlobalTheory.trdeg_eq_of_isAlgebraic_bot ℤ K Ω).trans (ModelDimension.ModelDim.trdeg_eq ev hG hd)
    refine ⟨inferInstance, inferInstance, inferInstance, hZp, (GlobalTheory.flat_int_iff_charZero _).2 ?_,
      ModelDimension.ModelDim.topologicalKrullDim_model inferInstance Z h1⟩
    exact (Z.res ⊤ ⟨genericPoint Z.Z, trivial⟩).charZero
  obtain ⟨π, hπ⟩ := hZ.exists_isHom (M' := M) (φ := AlgHom.id _ _) hNm
  obtain ⟨H', hH', e', s', he', hv', hs'⟩ := exists_bundle Z _ hZ.1
  obtain ⟨N', b', f', hf'⟩ := (imageDeg_pos_iff ev d).1 hd
  have hf := isChowFormInt_basis ev b' b hf'
  set f := GlobalTheory.ChowHt.linSubst (b'.toMatrix b) f'
  set δ := imageDeg ev d with hδ
  have hN : 0 < N := by
    obtain ⟨y, hy, -⟩ := hf.exists_point
    obtain ⟨j, -⟩ := Function.ne_iff.1 hy
    exact j.pos
  have hδ0 : ((d : ℝ) + 1) * δ ≠ 0 := mul_ne_zero (by positivity) (Nat.cast_ne_zero.2 hd.ne')
  have hh : imageHeight Nm L ev d = GlobalTheory.ChowHt.formHeight δ g A f / (((d : ℝ) + 1) * δ) :=
    GlobalTheory.ImageHeightUnique.imageHeight_eq K V Ω Nm L ev d _
      ⟨N, _, b, g, A, δ, f, hF, hf, mul_div_cancel₀ _ hδ0⟩
  have hc0 : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos t).ne'
  have ht : (fun k => ev (∑ j, g j k • b j)) = fun k => ∑ j, algebraMap K Ω (g j k) * ev (b j) := funext fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Algebra.smul_def]
  have hdet' : ∀ σ, (((Real.exp t : ℝ) : ℂ) • Mt σ).det ≠ 0 := fun σ => by
    rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) (hdet σ)
  have hc' : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ, ((Real.exp t : ℝ) : ℂ) • Mt ((starRingEnd ℂ).comp σ) =
      (((Real.exp t : ℝ) : ℂ) • Mt σ).map (starRingEnd ℂ) * U := fun σ => by
    obtain ⟨U, hU, h⟩ := hc σ
    refine ⟨U, hU, ?_⟩
    rw [h, ← smul_mul_assoc]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  have h1 := HP K Ω d N (n + 1) δ g (fun σ => ((Real.exp t : ℝ) : ℂ) • A σ) hF.full
    (fun σ => by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) (hF.herm σ))
    (conjCompat_smul hF.herm hF.conj hc0) (fun j => ev (b j)) Z (ht ▸ hZ) hZX f hf H' hH' e' he' s'
    (fun k => congrFun ht k ▸ hv' k) hs' (fun σ => ((Real.exp t : ℝ) : ℂ) • Mt σ) hdet' hc'
    (fun σ x => by rw [sum_smul, archSize_smul_sq, hMt])
  have h2 := (hP.p4.arProj _ _ _ Z.s M.s d hZX hX π hπ.inducedModelMorphism_comp_structureMap (map_generic hπ)
    (by rw [residueDegree_eq_one hπ]; exact one_ne_zero)).1 _ _ h1
  have h3 := (isometric_pull_fs hπ hH' he' hv' hs' hH he hv hs Mt _ hdet hc hdet' hc' t
    (fun _ => rfl)).isSelfInter hX h2
  convert h3 using 1
  rw [residueDegree_eq_one hπ, formHeight_smul hN g hF.herm hf.ne_zero hf.homog, hh]
  push_cast
  field_simp
end
end
end
