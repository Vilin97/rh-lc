module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegralStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductRenormalizationStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhereStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRange
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneEulerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneProductStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneIsotropicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneNormalisedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjectionsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscreteStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodularStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobalStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureNonzeroVectorsBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolumeStatement
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import GroundTheory.GlobalFields.LocalFieldAtPlace
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProductStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.global_volume_rank_one_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → SigmaFinite (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) ∧ (∀ v, SigmaFinite (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) ∧ ((framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0 ∧ ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureLocallyFiniteInvariant

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame

theorem free_act {S : Type} [CommRing S] {M n : ℕ} (g : GL (Fin M) S) {Y : Fin n → Fin M → S}
    (hY : LinearIndependent S Y) :
    LinearIndependent S fun a => (g : Matrix (Fin M) (Fin M) S) *ᵥ Y a := by
  have hk : LinearMap.ker (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) S)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    have h2 := congrArg (Matrix.mulVec ((g⁻¹ : GL (Fin M) S) : Matrix (Fin M) (Fin M) S)) h
    simpa [Matrix.mulVec_mulVec] using h2
  exact hY.map' _ hk

theorem free_of_unit {S : Type} [CommRing S] {M : ℕ} {Y : Fin 1 → Fin M → S} {i : Fin M}
    (hu : IsUnit (Y 0 i)) : LinearIndependent S Y := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h1 := congrFun hg i
  simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Subsingleton.elim a 0]
  exact hu.mul_left_eq_zero.1 h1

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem free_ratTup (R : Type) [CommRing R] [Algebra F R] {M : ℕ} {X : Fin 1 → Fin M → E}
    (hX : LinearIndependent E X) : LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hX.ne_zero 0)
  exact free_of_unit (i := i) ((isUnit_iff_ne_zero.2 hi).map (inclR (F := F) R))

variable [NumberField F]

theorem projInf_ratTup {M n : ℕ} (X : Fin n → Fin M → E) :
    projInf (ratTup (F := F) (AF F) X) = ratTup (Ainf F) X := by
  funext a i
  simp [projInf, ratTup, inclR]

theorem projV_ratTup (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → E) :
    projV v (projFin (ratTup (F := F) (AF F) X)) = ratTup (Fv F v) X := by
  funext a i
  simp [projV, projFin, ratTup, inclR]

theorem act_rat_free {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (γ : HFinIn (AF F) σ J)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    ∃ X' : Fin n → Fin M → E, LinearIndependent E X' ∧
      actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X' := by
  obtain ⟨γ, g, -, e⟩ := γ
  refine ⟨fun a => g.val *ᵥ X a, free_act g hX, funext fun a => funext fun i => ?_⟩
  have e' : (HA.mat (AF F) σ J γ).val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm

  simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

end Rat

theorem theta_inv_of_stable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (hμ : IsHaarH F E σ M J μ)
    (h𝓕 : IsFDH F E σ M J μ 𝓕) (n : ℕ) (S : Set (Fin n → Fin M → E))
    (hS : ∀ (γ : HFinIn (AF F) σ J) (X : Fin n → Fin M → E), X ∈ S →
      ∃ X' ∈ S, actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X')
    (h : HA (AF F) σ J) :
    (thetaMeas σ J μ 𝓕 S).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 S := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n S
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hm : Measurable (actW (AF F) σ J h : (Fin n → Fin M → _) → _) :=
    (ac.comp (continuous_const.prodMk continuous_id)).measurable
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  obtain ⟨-, _, -⟩ := GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [lintegral_map hΦ hm, hl (fun X => Φ (actW (AF F) σ J h X)) (hΦ.comp hm), hl _ hΦ]
  congr 1
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : S,
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t hts ht using fun X : S => hS γ⁻¹ X.1 X.2
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hti : Function.Injective fun X => (⟨t X, hts X⟩ : S) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hD := h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ h).quasiMeasurePreserving (e := id)
    Function.bijective_id fun γ g => (mul_assoc _ _ _)
  rw [h𝓕'.setLIntegral_eq hD f hinv, ← (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulRight _)]
  simp only [hf, mul_inv_rev, ← a2, mul_inv_cancel_left]

theorem measurableSet_free (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧
      LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))} := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm _ (Module.finBasis F E) 1 M
  have o1 : IsOpen {X : Fin 1 → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    PI.VolStabSW.TensAllW.isOpen_linIndep (Module.finBasis F E) (Ainf F) (PI.VolStabSW.isOpen_units_Ainf F)
      (PI.VolStabSW.lip_ainf F)
  have o2 : ∀ v, IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := fun v =>
    PI.VolStabSW.TensAllW.isOpen_linIndep (Module.finBasis F E) (Fv F v) (PI.VolStabSW.isOpen_units_Fv F v)
      (PI.VolStabSW.TensAllW.lip_field _)
  have m1 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F))} :=
    (isClosed_eq (hg 1 M J) continuous_const).measurableSet
  have m2 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) (projInf X)} :=
    (o1.preimage c1).measurableSet
  have m3 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun v => (((o2 v).preimage (c3 v)).preimage c2).measurableSet
  exact m1.inter (m2.inter m3)

theorem theta_frames_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM μ 𝓕 hμ h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact 1
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ 1 0 0).2
  obtain ⟨pinf, p, hp, -, -⟩ := GlobalTheory.T.adelic_unitary_group_projections F E σ hcm M J hJ
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  refine ⟨⟨fun X => ?_⟩, fun h => ?_, ?_⟩
  · obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X
    obtain ⟨N, r, hN, hr, hsub⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm _ (Module.finBasis F E) 1 M).2 K hK
    obtain ⟨C, hC⟩ := GlobalTheory.T.theta_measure_nonzero_vectors_bound F E σ hcm M J hJ hM _ (Module.finBasis F E) μ 𝓕 hμ h𝓕 N hN
    refine ⟨K, hX, lt_of_le_of_lt (le_trans ?_ ((measure_mono (fun X hX => hsub X hX)).trans (hC r hr))) ENNReal.ofReal_lt_top⟩
    have hm : Measurable (K.indicator (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
    rw [← lintegral_indicator_one hK.measurableSet, ← lintegral_indicator_one hK.measurableSet,
      hl _ _ hm, hl _ _ hm]
    have hs : framesE σ J (0 : Matrix (Fin 1) (Fin 1) E) ⊆ {X | X ≠ 0} :=
      fun X hX h0 => hX.1.ne_zero 0 (congrFun h0 0)
    exact mul_le_mul_right (lintegral_mono fun h => ENNReal.tsum_mono_subtype (fun X => K.indicator
      (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))) hs) _
  · refine theta_inv_of_stable F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1 _ (fun γ X hX => ?_) h
    obtain ⟨X', hX', e⟩ := act_rat_free γ hX.1
    refine ⟨X', ⟨hX', ?_⟩, e⟩
    refine Matrix.map_injective hinj ?_
    show (gramE σ J X').map (inclR (AF F)) = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F))
    rw [← hrat, ← e]
    refine (ag _ _).trans ?_
    rw [hrat, hX.2]
  · have hc := (measurableSet_free F E σ hcm M J).compl
    rw [← lintegral_indicator_one hc, hl _ _ (measurable_one.indicator hc)]
    have e : ∀ (h : HA (AF F) σ J) (X : framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)), Set.indicator
        {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧
          LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ
        (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
        (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) = 0 := fun h X => by
      apply Set.indicator_of_notMem
      rw [Set.notMem_compl_iff]
      refine ⟨?_, ?_, fun v => ?_⟩
      · rw [ag, hrat, X.2.2]
      · rw [(hp 1 h⁻¹ _).1, projInf_ratTup]
        exact free_act (HA.mat (Ainf F) σ J (pinf h⁻¹)) (free_ratTup _ X.2.1)
      · rw [(hp 1 h⁻¹ _).2 v, projV_ratTup]
        exact free_act (HA.mat (Fv F v) σ J (p v h⁻¹)) (free_ratTup _ X.2.1)
    simp only [e, tsum_zero, lintegral_zero, mul_zero]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureLocallyFiniteInvariantStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.theta_measure_locally_finite_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame.theta_frames_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeZeroRankOneOfThreeLe

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.OneZero

theorem one_vector_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → SWFree σ J (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM h₀ hne d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  classical
  obtain ⟨t0, t1, t2⟩ := GlobalTheory.T.theta_measure_locally_finite_invariant F E σ hcm M J hJ hM μ 𝓕 hμ h𝓕
  set I := thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) with hI
  set m0 : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
    fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) with hm0
  set mi0 := mi (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) with hmi0
  obtain ⟨sfi, sfv, hnz⟩ := GlobalTheory.T.global_volume_rank_one_product F E σ hcm M J hJ hM h₀ d b li lam hli hlam mi hmi m hm
  obtain ⟨nzi, nzv⟩ := hnz hne
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_volume_rank_one_product F E σ hcm M J hJ hM h₀ d b lam hlam m hm
  choose cS hcS using GlobalTheory.T.global_volume_rank_one_isotropic F E σ hcm M J hJ hM h₀ d b li lam hli hlam mi hmi m hm I t0 t1 t2
  obtain ⟨A, hAm, hA0, hAt⟩ := @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ mi0 sfi nzi
  choose B hBm hB0 hBt using fun v => @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (m0 v) (sfv v) (nzv v)
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
      (cS S : ℝ) = cS (insert v S) * (m0 v (latV b v)).toReal := by
    intro S _ v hv
    have hlatm : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) := by
      haveI := GlobalTheory.CompanionTheory.SW.Fact.borel_tup σ hcm (Fv F v) (hLv v) 1 M
      exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v).2.measurableSet
    let φ0 : ∀ w : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F w ⊗[F] E) → ℝ≥0∞ :=
      fun w => (B w).indicator 1
    let φ1 := Function.update φ0 v ((latV b v).indicator 1)
    have hφ0 : ∀ w, Measurable (φ0 w) := fun w => measurable_one.indicator (hBm w)
    have hφ1 : ∀ w, Measurable (φ1 w) := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa [φ1] using measurable_one.indicator hlatm
      · simpa [φ1, Function.update_of_ne hw] using hφ0 w
    have hAφ : Measurable (A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hAm
    have e1 : ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I = (cS S : ℝ≥0∞) * ((∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0) * ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m0 w)) :=
      hcS S _ φ0 hAφ hφ0
    have e2 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I = (cS (insert v S) : ℝ≥0∞) * ((∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0) * ∏ w ∈ insert v S, ∫⁻ X, φ1 w X ∂(m0 w)) :=
      hcS (insert v S) _ φ1 hAφ hφ1
    have e3 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I =
        ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I :=
      lintegral_congr fun X => GlobalTheory.CompanionTheory.SW.Fact.pureL_insert b S v hv _ φ0 X
    rw [e3, e1, Finset.prod_insert hv] at e2
    have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(m0 w) = ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m0 w) :=
      Finset.prod_congr rfl fun w hw => by
        have hne : w ≠ v := fun h => hv (h ▸ hw)
        simp only [φ1, Function.update_of_ne hne]
    have hL : ∫⁻ X, φ1 v X ∂(m0 v) = m0 v (latV b v) := by
      simp only [φ1, Function.update_self]
      exact lintegral_indicator_one hlatm
    have hB : ∀ w, ∫⁻ X, φ0 w X ∂(m0 w) = m0 w (B w) := fun w => lintegral_indicator_one (hBm w)
    have hA : ∫⁻ X, A.indicator (1 : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂mi0 = mi0 A :=
      lintegral_indicator_one hAm
    rw [hp, hL, hA] at e2
    simp only [hB] at e2
    set Q := ∏ w ∈ S, m0 w (B w) with hQ
    set a := mi0 A with ha
    set L := m0 v (latV b v) with hLdef
    have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
    have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
    have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
    have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
    have e4 : (cS S : ℝ≥0∞) * (a * Q) = ((cS (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
      rw [e2]; ring
    have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
    have e6 := congrArg ENNReal.toReal e5
    simpa [ENNReal.toReal_mul] using e6
  obtain ⟨c, S₀, -, hS₀⟩ := GlobalTheory.T.infinite_product_renormalization _ (fun v => (m0 v (latV b v)).toReal) cS ∅
    (fun _ => ENNReal.toReal_nonneg) hsum hstep
  have hc : IsEulerProd b I c mi0 m0 := by
    refine ⟨hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    refine (hcS S φinf φ hφi hφ).trans ?_
    have hcS' : (cS S : ℝ≥0∞) = (c : ℝ≥0∞) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m0 v.1 (latV b v.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := cS S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal]
    rw [hcS']
    ring
  suffices h : c = 1 from h ▸ hc
  obtain ⟨φ, C, φc, φp, φf, hb⟩ := GlobalTheory.T.global_volume_rank_one_normalised F E σ hcm M J hJ hM h₀ d b li lam hli hlam μ 𝓕 hμ h𝓕 mi hmi m hm
  obtain ⟨hdf, κ, hκ, hg⟩ := GlobalTheory.T.finite_volume_rank_one_euler F E σ hcm M J hJ hM h₀ d b lam hlam m hm nzv
  have : BorelSpace (Fin 1 → Fin M → Ainf F ⊗[F] E) := by
    have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
    exact (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 M
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) := φc.measurable.ennreal_ofReal
  set w := ∫⁻ X, ENNReal.ofReal (φ X) ∂mi0 with hw
  have hw0 : 0 < w.toReal := ENNReal.toReal_pos (fun h => nzi (by
    rw [hw, lintegral_eq_zero_iff hφm] at h
    exact ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (h.mono fun X hX =>
      (ENNReal.ofReal_pos.2 (φp X)).ne' hX)))) φf.ne
  have key : ∀ k : ℕ, ∃ a : ℕ, k < a ∧ |(c : ℝ) - 1| * (w.toReal * κ) * (a : ℝ) ≤ |C| := fun k => by
    obtain ⟨a, ha, h1⟩ := hg k
    have ha0 : 0 < a := lt_of_le_of_lt k.zero_le ha
    have haE : (a : E) ≠ 0 := by exact_mod_cast ha0.ne'
    obtain ⟨I', e1, e2⟩ := hb a ha0
    have hA : ∀ v, MeasurableSet {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} := fun v => by
      have hR := GlobalTheory.T.completion_is_local_ring F v
      obtain ⟨_, _, _, _, -⟩ := hR
      have : BorelSpace (Fv F v) := ⟨rfl⟩
      obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
      have := hB 1 M
      have hu : IsUnit (a : Fv F v ⊗[F] E) := by simpa using (Ne.isUnit haE).map (inclR (F := F) (Fv F v))
      have hK : IsCompact {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} :=
        (Homeomorph.smul hu.unit).isCompact_preimage.2 ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v).1
      exact hK.measurableSet
    obtain ⟨-, e3⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 M _ c _ _ hc _ _ hφm (fun v => hA v) (fun v => hdf a ha0 v)
      (((GlobalTheory.T.lattice_stable_almost_everywhere F E σ hcm d b 1 M).1 (Matrix.of fun _ _ => (a : E)) ((Matrix.det_unique _).trans_ne haE)).mono fun v hv => Set.ext fun X => by
        refine Iff.trans (Iff.of_eq (congrArg (· ∈ latV b v) (funext fun p => funext fun i => ?_))) (hv X)
        rw [Subsingleton.elim p 0]
        simp [rmul, mul_comm])
    generalize (∏' v, (m0 v {X : Fin 1 → Fin M → Fv F v ⊗[F] E |
      (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal) = P at h1 e2 e3
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have hP : 0 ≤ P := le_trans (by positivity) h1
    have e4 := congrArg ENNReal.toReal (e1.symm.trans e3)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hP, ENNReal.coe_toReal, ENNReal.coe_toReal] at e4
    rw [e4, show (c : ℝ) * w.toReal * P - w.toReal * P = (c - 1) * (w.toReal * P) by ring, abs_mul,
      abs_of_nonneg (mul_nonneg hw0.le hP)] at e2
    have hD : 0 < Module.finrank ℚ F := Module.finrank_pos
    have h2 : (a : ℝ) * (a : ℝ) ^ (Module.finrank ℚ F * M) ≤ (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) := by
      rw [← pow_succ']
      refine pow_le_pow_right₀ haR ?_
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      rw [show 2 * (M' + 3) - 2 = M' + 3 + (M' + 1) by omega, mul_add _ (M' + 3)]
      exact Nat.add_le_add_left (Nat.mul_pos hD (Nat.succ_pos _)) _
    refine ⟨a, ha, le_of_mul_le_mul_right ?_ (show (0 : ℝ) < (a : ℝ) ^ (Module.finrank ℚ F * M) by positivity)⟩
    calc _ = |(c : ℝ) - 1| * (w.toReal * (κ * ((a : ℝ) * (a : ℝ) ^ (Module.finrank ℚ F * M)))) := by ring
      _ ≤ |(c : ℝ) - 1| * (w.toReal * P) := by
          gcongr
          exact (mul_le_mul_of_nonneg_left h2 hκ.le).trans h1
      _ ≤ _ := e2.trans (by gcongr; exact le_abs_self C)
  by_contra hne'
  have hp : 0 < |(c : ℝ) - 1| * (w.toReal * κ) :=
    mul_pos (abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hne'))) (mul_pos hw0 hκ)
  obtain ⟨k, hk⟩ := exists_nat_gt (|C| / (|(c : ℝ) - 1| * (w.toReal * κ)))
  obtain ⟨a, ha, h⟩ := key k
  rw [div_lt_iff₀' hp] at hk
  have : (k : ℝ) < a := by exact_mod_cast ha
  nlinarith

end GlobalTheory.CompanionTheory.SW.OneZero
end
end
end
