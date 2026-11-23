module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetricStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbeddingStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionLocConstTrivial
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym

-- Source module: Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstant

section

@[expose] public section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv


open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem const_of_orthogonal_log_units : ∀ (F : Type) [Field F] [NumberField F] (m : (F →+* ℂ) → ℝ),
    (∀ sg, m (ComplexEmbedding.conjugate sg) = m sg) →
    (∀ θ : (𝓞 F)ˣ, ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = 0) →
    ∀ sg sg', m sg = m sg' := by
  open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem in
  intro F _ _ m hconj horth
  classical

  have hdesc : ∀ sg sg' : F →+* ℂ, InfinitePlace.mk sg = InfinitePlace.mk sg' → m sg = m sg' := by
    intro sg sg' h
    rcases InfinitePlace.mk_eq_iff.mp h with h | h
    · rw [h]
    · rw [← h, hconj]
  set mw : InfinitePlace F → ℝ := fun w => m w.embedding with hmw
  have hmk : ∀ sg : F →+* ℂ, m sg = mw (InfinitePlace.mk sg) := by
    intro sg
    exact hdesc _ _ (by simp [InfinitePlace.mk_embedding])

  have hplace : ∀ θ : (𝓞 F)ˣ,
      ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) * mw w = 0 := by
    intro θ
    rw [← horth θ, ← Finset.sum_fiberwise Finset.univ (fun sg : F →+* ℂ => InfinitePlace.mk sg)]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hfib : ∀ sg ∈ Finset.univ.filter (fun sg : F →+* ℂ => InfinitePlace.mk sg = w),
        Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = Real.log (w ((θ : 𝓞 F) : F)) * mw w := by
      intro sg hsg
      have hsg' : InfinitePlace.mk sg = w := (Finset.mem_filter.mp hsg).2
      rw [hmk sg, hsg', ← hsg', InfinitePlace.apply]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul,
      mul_assoc]

  let L : logSpace F →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ w, x w * (mw w.1 - mw w₀)
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }
  have hLunit : ∀ θ : (𝓞 F)ˣ, L (logEmbedding F (Additive.ofMul θ)) = 0 := by
    intro θ
    have h1 : ∑ w : InfinitePlace F, (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) = 0 := by
      exact_mod_cast sum_mult_mul_log θ
    have h2 : ∑ w : InfinitePlace F,
        (mult w : ℝ) * Real.log (w ((θ : 𝓞 F) : F)) * (mw w - mw w₀) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hplace θ, ← Finset.sum_mul, h1]
      simp
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace F)] at h2
    simpa [L, logEmbedding_component] using h2
  have hL : L = 0 := by
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ Submodule.span ℝ (unitLattice F : Set (logSpace F)) := by
      rw [unitLattice_span_eq_top]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      exact hLunit (Additive.toMul a)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  have hconst : ∀ w : InfinitePlace F, mw w = mw w₀ := by
    intro w
    by_cases hw : w = w₀
    · rw [hw]
    · have := LinearMap.congr_fun hL (Pi.single ⟨w, hw⟩ 1)
      have h3 : mw w - mw w₀ = 0 := by
        simpa [L, Pi.single_apply, Finset.sum_ite_eq] using this
      linarith
  intro sg sg'
  rw [hmk sg, hmk sg', hconst (InfinitePlace.mk sg), hconst (InfinitePlace.mk sg')]

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AdelicProofs.UnitLogOrthogonalWeightConstantStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.unit_log_orthogonal_weight_constant : ∀ (F : Type) [Field F] [NumberField F] (m : (F →+* ℂ) → ℝ), (∀ sg, m (ComplexEmbedding.conjugate sg) = m sg) → (∀ θ : (𝓞 F)ˣ, ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * m sg = 0) → ∀ sg sg', m sg = m sg' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.const_of_orthogonal_log_units | exact GlobalTheory.CompanionTheory.Ar.Giv.const_of_orthogonal_log_units | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.const_of_orthogonal_log_units <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEqStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.unit_ratio_divisor_support_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℕ) (f g : MRing ι) (θ : Ω), IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f d → IsMultiHomog g d → aeval y g ≠ 0 → θ ≠ 0 → IsIntegral ℤ θ → IsIntegral ℤ θ⁻¹ → aeval y f = θ * aeval y g → divSupp (mCoordIdeal y) f = divSupp (mCoordIdeal y) g ∧ ∀ W ∈ divSupp (mCoordIdeal y) g, multAt ((mCoordIdeal y) ⊔ Ideal.span {f}) W = multAt ((mCoordIdeal y) ⊔ Ideal.span {g}) W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio | exact GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance

section

@[expose] public section

set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem sum_log_unit_mul_mass_eq_zero : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  intro hSys hInt K _ ι _ Ω _ F _ _ _ y D L θ hP hbir hL hex
  classical
  obtain ⟨II, hII, -⟩ := hSys
  obtain ⟨x, hx⟩ : ∃ x : F, x = ((θ : 𝓞 F) : F) := ⟨_, rfl⟩
  have hmul : ((((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) * x = 1 := by
    rw [hx]
    have h1 : (((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (θ : 𝓞 F)) = 1 := by simp
    exact_mod_cast congrArg (fun u : 𝓞 F => (u : F)) h1
  have hxinv : ((((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) = x⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact zero_ne_one hmul
  have hxI : IsIntegral ℤ x := hx ▸ RingOfIntegers.isIntegral_coe (θ : 𝓞 F)
  have hxI' : IsIntegral ℤ x⁻¹ := hxinv ▸ RingOfIntegers.isIntegral_coe ((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  rw [← hx]
  have ht0 : algebraMap F Ω x ≠ 0 := (map_ne_zero _).mpr hx0
  have htI : IsIntegral ℤ (algebraMap F Ω x) := hxI.map (algebraMap F Ω).toIntAlgHom
  have htI' : IsIntegral ℤ (algebraMap F Ω x)⁻¹ := by
    rw [← map_inv₀]
    exact hxI'.map (algebraMap F Ω).toIntAlgHom
  obtain ⟨d, f, g, hf, hg, hg0, hfg⟩ := hbir (algebraMap F Ω x)
  have hf0 : aeval y f ≠ 0 := by
    rw [hfg]
    exact mul_ne_zero ht0 hg0
  have hgP : g ∉ mCoordIdeal y := fun h => hg0
    ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hg).mp h)
  have hfP : f ∉ mCoordIdeal y := fun h => hf0
    ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).mp h)
  obtain ⟨B, hB0, hBs, hBl⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun sg => ‖sg x‖) (fun sg => norm_pos_iff.mpr ((map_ne_zero sg).mpr hx0)) hex
  obtain ⟨A, hAa, hA⟩ : ∃ A : HermLine ι, (∀ k, A.a k = d k) ∧ IsSmoothHerm A :=
    ⟨HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (d k : ℤ)), fun _ => rfl,
      GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs _⟩
  have hAB : IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hBs
  have hABa : ∀ k, (A.tensor B).a k = d k := fun k => by
    simp [HermLine.tensor, hB0, hAa k]
  have hRA := (hII K ι).2.2 (mCoordIdeal y) D L A g d hP hL hA hAa hg hgP
  have hRB := (hII K ι).2.2 (mCoordIdeal y) D L (A.tensor B) f d hP hL hAB hABa hf hfP
  have hadd := (hII K ι).2.1 (mCoordIdeal y) D L A B hP hL hA hBs
  obtain ⟨hsupp, hmult⟩ := GlobalTheory.T.unit_ratio_divisor_support_eq K ι Ω y D d f g (algebraMap F Ω x) hP hf hg hg0 ht0 htI htI' hfg
  have hlog : ∀ z ∈ mcPts (mCoordIdeal y), logNorm (A.tensor B) f z = logNorm A g z := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = ‖sg x‖ := (hBl z hz sg hsg).self_of_nhds
    have hfz := hsg d f g x hf hg hfg
    have hs0 : ‖sg x‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero sg).mpr hx0)
    have hAz : A.h z ≠ 0 := (A.pos z hz.1).ne'
    unfold logNorm
    congr 1
    show ‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z) = _
    rw [hfz, hval, norm_mul]
    field_simp
  have hrec : recR (II K ι) (mCoordIdeal y) L (A.tensor B) f = recR (II K ι) (mCoordIdeal y) L A g := by
    unfold recR
    rw [hsupp]
    congr 1
    · exact finsum_mem_congr rfl fun W hW => by rw [hmult W hW]
    · exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) hlog
  rw [← intersection_locConst_trivial hInt K ι Ω F y D L B (fun sg => ‖sg x‖) II hII hP hL hB0 hBs hex hBl]
  linarith [hRA, hRB, hadd, hrec]

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvarianceStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.sum_over_embeddings_unit_invariance : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

def fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) A.a

theorem fsOfDegree_a {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    (fsOfDegree A).a = A.a := rfl

theorem isSmoothHerm_fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    IsSmoothHerm (fsOfDegree A) :=
  GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs A.a

theorem isConjInvariantH_fsOfDegree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) :
    IsConjInvariantH (fsOfDegree A) := by
  intro z
  simp only [fsOfDegree, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [GroundTheory.Heights₂.Heights.FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]

theorem pieceDegree : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement →
    GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  intro hAr hRes hPts K _ ι _ Ω _ F _ _ _ y D L sg sg' har hbir hsm hone
  have hsm₀ : ∀ j, IsSmoothHerm (fsOfDegree (L j)) := fun j => isSmoothHerm_fsOfDegree _
  have hcj₀ : ∀ j, IsConjInvariantH (fsOfDegree (L j)) := fun j => isConjInvariantH_fsOfDegree _
  have hind : ∀ s : F →+* ℂ,
      ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) =
        ptsIntegral (mCoordIdeal y) (pot fun j => fsOfDegree (L j))
          ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) := fun s =>
    GlobalTheory.T.points_integral_independent_of_metric hAr hPts K ι Ω F y D L (fun j => fsOfDegree (L j)) s har hsm hsm₀
      (fun j => (fsOfDegree_a (L j)).symm) hone
  rw [hind sg, hind sg']
  exact GlobalTheory.T.unit_log_orthogonal_weight_constant F
    (fun s => ptsIntegral (mCoordIdeal y) (pot fun j => fsOfDegree (L j))
      ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)))
    (fun s => GlobalTheory.T.points_integral_unique_embedding hRes K ι Ω F y D _ s har hsm₀ hcj₀ hone)
    (fun θ => GlobalTheory.T.sum_over_embeddings_unit_invariance hAr hPts K ι Ω F y D _ θ har hbir hsm₀ hone) sg sg'

end

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolutionStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.piece_degree_of_intersection_and_resolution : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | exact GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree <;> assumption)
end
end
