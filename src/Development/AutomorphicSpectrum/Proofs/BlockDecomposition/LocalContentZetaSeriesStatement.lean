module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralOrderStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralUnramified
import Mathlib.Topology.Separation.CompletelyRegular

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingNormMeasure

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

section Ring

open scoped Pointwise

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A]

theorem map_mul_unit (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (u : Aˣ) :
    μ.map (fun x => (u : A) * x) = (distribHaarChar A u)⁻¹ • μ := by
  have hm : Measurable fun x : A => (u : A) * x := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun x : A => (u : A) * x) ⁻¹' B = u⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, map_inv]
  rfl

theorem exists_pos_finite (μ : Measure A) [μ.IsAddHaarMeasure] :
    ∃ K : Set A, μ K ≠ 0 ∧ μ K ≠ ∞ := by
  obtain ⟨K, hK, hn⟩ := exists_compact_mem_nhds (0 : A)
  refine ⟨K, ?_, hK.measure_lt_top.ne⟩
  exact (Measure.measure_pos_of_mem_nhds μ hn).ne'

theorem smul_inj (μ : Measure A) [μ.IsAddHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have e := congrArg (fun m : Measure A => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem char_map (s : A ≃+* A) (hs : Continuous s) (hs' : Continuous s.symm) (u : Aˣ) :
    distribHaarChar A (Units.map (s : A →* A) u) = distribHaarChar A u := by
  let H : A ≃ₜ A := ⟨s.toEquiv, hs, hs'⟩
  let μ : Measure A := Measure.addHaar
  have : (μ.map H).IsAddHaarMeasure := s.toAddEquiv.isAddHaarMeasure_map μ hs hs'
  have : (μ.map H).Regular := Measure.Regular.map H
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have hap : ∀ S : Set A, (μ.map H) S = μ (H ⁻¹' S) := fun S =>
    H.toMeasurableEquiv.map_apply S
  have hpre : H ⁻¹' (H '' K) = K := H.injective.preimage_image K
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.map H) (s := H '' K)
    (by rwa [hap, hpre]) (by rwa [hap, hpre]) ?_
  rw [hap, hap, hpre, distribHaarChar_mul]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, hy⟩
    refine ⟨k, hk, H.injective ?_⟩
    rw [← hy]
    simp [H, Units.smul_def]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨H k, ⟨k, hk, rfl⟩, ?_⟩
    simp [H, Units.smul_def]

end Ring

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

theorem coordK_map_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (c : Fv F v ⊗[F] E) (t : Fv F v) (w : ℕ), IsUnit c → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = ((qv v : ℝ) ^ w)⁻¹ → (coordK (Fv F v) b lam).map (fun x => c * x) = (qv v ^ w) • coordK (Fv F v) b lam := by
  intro F E _ _ _ _ _ σ hσ d b v lam hlam c t w hc ht hnorm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, hsc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set μ := coordK (Fv F v) b lam with hμ
  haveI : μ.Regular := inferInstance
  have hss : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, sigma_sigma σ hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  let s : (Fv F v ⊗[F] E) ≃+* (Fv F v ⊗[F] E) :=
    { toFun := sigR (Fv F v) σ, invFun := sigR (Fv F v) σ, left_inv := hss, right_inv := hss,
      map_mul' := map_mul _, map_add' := map_add _ }
  let u : (Fv F v ⊗[F] E)ˣ := hc.unit
  have hu : (u : Fv F v ⊗[F] E) = c := hc.unit_spec
  have hchar := char_map s hsc hsc u
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hqv : (qv v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by simp [qv]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero, hqv] at hnorm
    exact inv_ne_zero (pow_ne_zero w hq) hnorm.symm
  have hk : ‖t‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ w := by
    rw [hnorm, hqv, inv_pow]
  have h1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam t ht0 w hk
  have h2 := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam t ht0 _ h1
  have h3 := map_mul_unit μ (Units.map (s : _ →* _) u * u)
  have hval : ((Units.map (s : _ →* _) u * u : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t := by
    rw [ht, ← hu]
    rfl
  rw [hval, h2, map_mul, hchar] at h3
  have h4 := smul_inj μ h3
  have h5 : (distribHaarChar (Fv F v ⊗[F] E) u)⁻¹ = qv v ^ w := by
    refine (pow_left_inj₀ zero_le' zero_le' two_ne_zero).1 ?_
    rw [inv_pow, pow_two]
    exact h4.symm
  rw [← h5, ← map_mul_unit μ u, hu]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingNormMeasureStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass


theorem _root_.GlobalTheory.T.local_unit_scaling_norm_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (c : Fv F v ⊗[F] E) (t : Fv F v) (w : ℕ), IsUnit c → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = ((qv v : ℝ) ^ w)⁻¹ → (coordK (Fv F v) b lam).map (fun x => c * x) = (qv v ^ w) • coordK (Fv F v) b lam := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralUnramifiedStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass


theorem _root_.GlobalTheory.T.quadratic_basis_integral_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → (¬ ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1) → IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (2 * i))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadField.inert_content | exact GlobalTheory.CompanionTheory.SW.QuadField.inert_content | (intros; apply GlobalTheory.CompanionTheory.SW.QuadField.inert_content <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContentZetaSeries

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content

theorem one_lt_qv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : 1 < (qv v : ℝ) := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have : 1 < Ideal.absNorm v.asIdeal := by omega
  simp only [qv, NNReal.coe_natCast]
  exact_mod_cast this

theorem hasSum_field (q : ℝ) (hq : 1 < q) (s : ℕ) (hs : 1 ≤ s) :
    HasSum (fun k : ℕ => ((q ^ (2 * k))⁻¹) ^ s) (1 - (q ^ (2 * s))⁻¹)⁻¹ := by
  have h0 : 0 < q := by linarith
  have hr : (q ^ (2 * s))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have := hasSum_geometric_of_lt_one (r := (q ^ (2 * s))⁻¹) (by positivity) hr
  convert this using 2 with k
  rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul]
  congr 2
  ring

theorem hasSum_split (q : ℝ) (hq : 1 < q) (s : ℕ) (hs : 1 ≤ s) :
    HasSum (fun p : ℕ × ℕ => ((q ^ (p.1 + p.2))⁻¹) ^ s) (((1 - (q ^ s)⁻¹)⁻¹) ^ 2) := by
  have h0 : 0 < q := by linarith
  have hr : (q ^ s)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have hg := hasSum_geometric_of_lt_one (r := (q ^ s)⁻¹) (by positivity) hr
  have hn : Summable fun k : ℕ => ‖((q ^ s)⁻¹) ^ k‖ := hg.summable.norm
  have := hg.mul hg (summable_mul_of_summable_norm hn hn)
  have e : (fun p : ℕ × ℕ => ((q ^ (p.1 + p.2))⁻¹) ^ s) = fun p : ℕ × ℕ => ((q ^ s)⁻¹) ^ p.1 * ((q ^ s)⁻¹) ^ p.2 := by
    funext p
    rw [← pow_add, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm s]
  rw [e, pow_two]
  exact this

theorem content : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ (ι : Type) (_ : Countable ι) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w ∧ ∀ s : ℕ, 1 ≤ s → HasSum (fun i => (((qv v : ℝ) ^ w i)⁻¹) ^ s) (zetaV E v s) := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.T.integral_almost_all_places F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 hBC hCB
  have hq := one_lt_qv v
  by_cases hres : ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1
  · obtain ⟨e, he⟩ : ∃ e : Fv F v, e ^ 2 = algebraMap F (Fv F v) D := by
      obtain ⟨e, he⟩ := hres
      have hDR : algebraMap F (Fv F v) D ∈ v.adicCompletionIntegers F := hD1.le
      have h2' : Valued.v (2 : Fv F v) = 1 := by simpa [map_ofNat] using h21
      have := GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2' ⟨_, hDR⟩ hD1 ?_
      · obtain ⟨r, hr⟩ := this
        exact ⟨r, by rw [pow_two]; exact hr.symm⟩
      · refine ⟨IsLocalRing.residue _ e, ?_⟩
        rw [← map_mul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
        intro h1
        have : Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) = 1 := by
          rw [← Valuation.map_neg]
          simpa [pow_two] using h1
        exact absurd he (by rw [this]; exact lt_irrefl _)
    obtain ⟨hnf, c, c1, c3, c4, c5⟩ := GlobalTheory.T.quadratic_basis_integral_order F E σ h d b b₂ D hb0 hσ1 hD v hD1 h21 hBC hCB e he
    refine ⟨ℕ × ℕ, inferInstance, c, fun i => i.1 + i.2, ⟨c1, ?_, c3, c4, c5⟩, ?_⟩
    · intro i lam hlam
      obtain ⟨t, ht, hn⟩ := c3 i
      exact GlobalTheory.T.local_unit_scaling_norm_measure F E σ h d b v lam hlam (c i) t _ (c1 i).1 ht hn
    · intro s hs
      rw [zetaV, if_neg hnf]
      exact hasSum_split _ hq s hs
  · obtain ⟨hf, c, c1, c3, c4, c5⟩ := GlobalTheory.T.quadratic_basis_integral_unramified F E σ h d b b₂ D hb0 hσ1 hD v hD1 h21 hBC hCB hres
    refine ⟨ℕ, inferInstance, c, fun i => 2 * i, ⟨c1, ?_, c3, c4, c5⟩, ?_⟩
    · intro i lam hlam
      obtain ⟨t, ht, hn⟩ := c3 i
      exact GlobalTheory.T.local_unit_scaling_norm_measure F E σ h d b v lam hlam (c i) t _ (c1 i).1 ht hn
    · intro s hs
      rw [zetaV, if_pos hf]
      exact hasSum_field _ hq s hs

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContentZetaSeriesStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

theorem _root_.GlobalTheory.T.local_content_zeta_series : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ (ι : Type) (_ : Countable ι) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w ∧ ∀ s : ℕ, 1 ≤ s → HasSum (fun i => (((qv v : ℝ) ^ w i)⁻¹) ^ s) (zetaV E v s) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content <;> assumption)
end
end
