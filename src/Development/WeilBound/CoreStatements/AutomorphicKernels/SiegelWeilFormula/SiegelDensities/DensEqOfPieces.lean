module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Bridge
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianNondegRepresentsNonzeroScalar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryIsomOfIsometry
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.IsEulerProdConstIff
import Mathlib.Tactic.Linter.HaveILetI
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBlockOneAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesCongruentTargetAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberMeasuresAgreeAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.NotRep
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RightMultiplicationEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentTarget
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosurePropertiesStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.SmulIndicatorMass

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Induct

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

theorem swMeasC_succ (hB : BaseOne) (hI : IsomC) (hS : ScaleC) (hSt : StepC) (hN : NotRepC) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ J → PositivityTheory.PfSWUS.HMass.IsAnisoH σ J →
    ∀ (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeasC σ J T hT := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro J hJ _ T hT hd
    exact hB F E σ hσ J hJ T hT hd
  | succ n ih =>
    intro J hJ ha T hT hd
    obtain ⟨t, x, ht, hx⟩ := GlobalTheory.CompanionTheory.SW.HermRep.exists_repr F E σ hσ (n + 1) T ⟨hT, hd⟩
    obtain ⟨g, T₁, hT₁, hb, -⟩ :=
      GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ (n + 1) T ⟨hT, hd⟩ t x ht hx
    obtain ⟨hdet, hblk, -, -⟩ := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hσ (n + 1) T₁ t
    have hT' := hblk hT₁.1
    have htE : algebraMap F E t ≠ 0 := by
      simpa using ht
    have hd' : (blockOne (algebraMap F E t) T₁).det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero htE hT₁.2
    refine hS F E σ hσ (n + 2) J hJ (n + 2) T hT hd g _ hT' hb ?_
    by_cases hrep : ∃ y : Fin (n + 2) → E, hE σ J y y = algebraMap F E t
    · obtain ⟨y, hy⟩ := hrep
      obtain ⟨g', J₁, hJ₁, hb', -⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ (n + 1) J hJ t y ht hy
      have ha' : PositivityTheory.PfSWUS.HMass.IsAnisoH σ (blockOne (algebraMap F E t) J₁) := by
        rw [hb']
        exact PositivityTheory.PfSWUS.HMass.isAnisoH_of_isometry σ J g' ha
      refine hI F E σ hσ (n + 2) J hJ g' _ hb' (n + 2) _ hT' hd' ?_
      exact hSt F E σ hσ (n + 1) J₁ hJ₁ (by omega) t ht ha' T₁ hT₁.1 hT₁.2 hT'
        (ih J₁ hJ₁ (PositivityTheory.PfSWUS.HMass.isAnisoH_of_block σ _ J₁ ha') T₁ hT₁.1 hT₁.2)
    · exact hN F E σ hσ (n + 1) J hJ (by omega) ha t ht T₁ hT₁.1 hT₁.2 hT' (fun y hy => hrep ⟨y, hy⟩)

theorem swMeasCAll_of (hB : BaseOne) (hI : IsomC) (hS : ScaleC) (hSt : StepC) (hN : NotRepC) : SWMeasCAll := by
  intro F E _ _ _ _ _ σ hσ M hM J hJ ha T hT hd
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  exact swMeasC_succ hB hI hS hSt hN F E σ hσ n J hJ ha T hT hd

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.IsomC

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SWIsom
open scoped TensorProduct ENNReal NNReal Matrix

theorem isomC : IsomC := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ'eq n T hT _ hSW
  subst hJ'eq
  have hJ' := isHermND_conj σ hCM J hJ g
  intro d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g _ rfl (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  obtain ⟨tg', -, -, -, bs', -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M _ hJ' (AF F)
  haveI := tg
  haveI := tg'
  haveI := bs
  haveI := bs'
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M _ (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M _ (μ.map He.symm) (He ⁻¹' 𝓕) :=
    isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := haar_of_loc σ hCM (Ainf F) hLi b laminf hinf.1 n M
  have hWv := fun v => haar_of_loc σ hCM (Fv F v) (hLv v) b (lam v) (hlam v).1 n M
  obtain ⟨minf', hminf'⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M _ hJ' (Ainf F) hLi n _ _ hWi.1 hWi.2
  choose m' hm' using fun v =>
    GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M _ hJ' (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2
  obtain ⟨cinf, c, hUP, hci, hcv⟩ := GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hCM n M g
  obtain ⟨κ, hEul, hκ⟩ := hSW d b laminf lam hinf hlam (μ.map He.symm) (He ⁻¹' 𝓕) hμ' h𝓕' minf' m' hminf' hm'
  refine ⟨κ, ?_, hκ⟩
  have hfin : ∀ v, (cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤ := by
    intro v
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Fv F v) (hLv v) n _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermOf (Fv F v) σ T hT)).1
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).1.measure_lt_top
  have hproj : ∀ X : Fin n → Fin M → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) g) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) g) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) g) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact map_actTup (fstA F) g X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Af F) (bc (inclR (Af F)) g) (projFin X) := by
        funext a i
        exact map_actTup (sndA F) g X a i
      rw [h1]
      funext a i
      exact map_actTup (evalV F v) g (projFin X) a i
  have hlocI := local_map σ hCM J hJ g (Ainf F) hLi n _ _ hWi.1 hWi.2 minf minf' hminf hminf' cinf
    (hci _ hWi.1) (hermOf (Ainf F) σ T hT)
  have hlocV := fun v => local_map σ hCM J hJ g (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2 (m v) (m' v) (hm v)
      (hm' v) (c v) (hcv v _ (hWv v).1) (hermOf (Fv F v) σ T hT)
  have key := GlobalTheory.T.euler_product_measure_transport F E σ hCM d b n M _ (κ • minf' (hermOf (Ainf F) σ T hT))
    (κ • minf (hermOf (Ainf F) σ T hT)) (fun v => cfac E v • m' v (hermOf (Fv F v) σ T hT))
    (fun v => cfac E v • m v (hermOf (Fv F v) σ T hT)) (actTup (AF F) (bc (inclR (AF F)) g))
    (actTup (Ainf F) (bc (inclR (Ainf F)) g)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) g))
    (measurable_actTup σ hCM (AF F) _) (measurable_of_loc σ hCM (Ainf F) hLi _)
    (fun v => measurable_of_loc σ hCM (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b n M).2.1 g) cinf c hUP
    (by
      rw [Measure.map_smul, hlocI, smul_comm]
      exact (measurable_of_loc σ hCM (Ainf F) hLi _).aemeasurable)
    (fun v => by
      rw [Measure.map_smul, hlocV v, smul_comm]
      exact (measurable_of_loc σ hCM (Fv F v) (hLv v) _).aemeasurable) hfin
    ((isEulerProd_const_iff b _ κ _ _).1 hEul)
  have hth := theta_map (n := n) σ hCM J hJ g He hmat μ 𝓕 T
  rw [hth] at key
  exact (isEulerProd_const_iff b _ κ _ _).2 key

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.MassGoodEq

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open GlobalTheory.CompanionTheory.SW.GoodMass

theorem mass_good_eq (hE2 : PositivityTheory.PfSWUS.HMass.OneVecBinaryMass) (hO : MassOne) (hcm : IsCMExt F E σ) :
    ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ J →
    ∀ (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J (n + 1) (coordW (Fv F v) b lam (n + 1) (n + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m →
      |((cfac E v : ℝ≥0∞) * m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤
        C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro J hJ T hT hdet d b
    obtain ⟨β, -, hβ0, hβ⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
    have hβ0 := hβ0 hdet
    refine ⟨0, ?_⟩
    filter_upwards [hO F E σ hcm J hJ d b, (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 β hβ0] with v hv hu lam hl m hm
    rw [hβ (Fv F v), hv lam hl m hm _ hu]
    simp
  | succ n ih =>
    intro J hJ T hT hdet d b
    obtain ⟨x, t, ht, hx⟩ := exists_aniso hcm T hT hdet
    obtain ⟨g, T₁, hT₁, hblock, -⟩ :=
      AlgSplit.split_anisotropic F E σ hcm (n + 1) T ⟨hT, hdet⟩ t x ht hx
    have hbh : ∀ a b, σ (blockOne (algebraMap F E t) T₁ b a) = blockOne (algebraMap F E t) T₁ a b :=
      blockOne_herm _ (σ.commutes t) _ hT₁.1
    have hgdet : (g : Matrix (Fin (n + 2)) (Fin (n + 2)) E).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    have hone : IsHermND σ (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := one_hermND (n + 1)
    have hJ' : IsHermND σ (blockOne (algebraMap F E t) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E)) :=
      blockOne_hermND t ht
    obtain ⟨C₁, hC₁⟩ := ih 1 hone T₁ hT₁.1 hT₁.2 d b
    obtain ⟨C₀, hC₀⟩ := PositivityTheory.PfSWUS.HMass.one_vec_bound hE2 hcm (n + 2) _ hJ' (by omega) b
    refine ⟨|C₀| + |C₁| + |C₀| * |C₁|, ?_⟩
    have e1 := GlobalTheory.T.local_densities_congruent_target_almost_all F E σ hcm (n + 2) J hJ (n + 2) T hT hdet g hgdet _ hbh hblock d b
    have e2 := GlobalTheory.T.local_gram_fiber_measures_agree_almost_all F E σ hcm (n + 2) J hJ _ hJ' d b (n + 2)
    have e3 := GlobalTheory.T.local_densities_block_one_almost_all F E σ hcm (n + 1) 1 hone t ht (n + 1) T₁ hT₁.1 hT₁.2 hbh d b
    have e5 := (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 t ht
    filter_upwards [e1, e2, e3, hC₀, e5, hC₁] with v h1 h2 h3 h4 h5 h6 lam hl m hm
    obtain ⟨m', hm'⟩ := exists_family hcm hJ' b v lam hl (n + 2)
    obtain ⟨m₁, hm₁⟩ := exists_family hcm hJ' b v lam hl 1
    obtain ⟨m₂, hm₂⟩ := exists_family hcm hone b v lam hl (n + 1)
    have a1 := h1 lam hl m hm
    have a2 := h2 lam hl m m' hm hm' (hermOf (Fv F v) σ _ hbh)
    have a3 := h3 lam hl m' m₁ m₂ hm' hm₁ hm₂
    have a4 := h4 lam hl m₁ hm₁ _ h5
    have a6 := h6 lam hl m₂ hm₂
    rw [← a1, a2, a3, mul_left_comm, ENNReal.toReal_mul]
    exact PositivityTheory.PfSWUS.HMass.arith2 (absNorm_one_le v) a4 a6

end Main

theorem massCAll_of (hE2 : PositivityTheory.PfSWUS.HMass.OneVecBinaryMass) (hO : MassOne) : MassCAll := by
  intro F E _ _ _ _ _ σ hCM M hM J hJ T hT hdet d b lam hlam m hm
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · intro v
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh.2.1 (n + 1) (n + 1)
    haveI hH := hh.2.2 (n + 1)
    haveI hlf := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM (n + 1) J hJ (Fv F v) hloc (n + 1) _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b (n + 1) (n + 1) v).1.measure_lt_top
  · obtain ⟨C, hC⟩ := mass_good_eq hE2 hO hCM n J hJ T hT hdet d b
    refine Summable.of_norm_bounded_eventually
      (g := fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
      ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C) ?_
    filter_upwards [hC] with v hv
    have := hv (lam v) (hlam v) (m v) (hm v)
    rw [Real.norm_eq_abs, abs_abs, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    simpa [div_eq_mul_inv] using this

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.ScaleC

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Scale
open scoped TensorProduct ENNReal NNReal Matrix

theorem scaleC : ScaleC := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT _ g T' hT' hrel hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m
    hminf hm
  have hinv := (HaarCoord.conj_facts hcm).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin n) (Fin n) E, G = (g : Matrix (Fin n) (Fin n) E) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H : Matrix (Fin n) (Fin n) E, H = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) :=
    ⟨_, rfl⟩
  have hGH : G * H = 1 := by rw [hG, hHd]; exact Units.mul_inv g
  have hHG : H * G = 1 := by rw [hG, hHd]; exact Units.inv_mul g
  rw [← hG] at hrel
  have hdetH : H.det ≠ 0 := by
    intro h0
    have : H.det * G.det = 1 := by rw [← Matrix.det_mul, hHG, Matrix.det_one]
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hrel' : cT (σ : E →+* E) H * T' * H = T := by
    rw [hrel]
    calc cT (σ : E →+* E) H * (cT (σ : E →+* E) G * T * G) * H
        = (cT (σ : E →+* E) H * cT (σ : E →+* E) G) * T * (G * H) := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [← cT_mul, hGH, cT_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨ai, a, hau, hai, hav⟩ := GlobalTheory.T.right_multiplication_euler_product F E σ hcm n M H hdetH
  obtain ⟨ci, c, hcu, hci, hcv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm n H hdetH
  obtain ⟨-, -, -, -, hq, -⟩ := GlobalTheory.T.unit_product_closure_properties F ai ci a c hau hcu
  obtain ⟨hci0, hc0, -⟩ := GlobalTheory.T.unit_product_closure_properties F ci ai c a hcu hau
  have hrI : IsLocR (Ainf F) := isLocR_Ainf F hcm.1
  have hrV : ∀ v, IsLocR (Fv F v) := fun v => LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have sInf := unitary_conjugate_local σ hcm hinv J hJ (Ainf F) hrI b laminf hinf.1 minf hminf H T T' hdetH hT hT'
    hrel' ai ci hci0 hai hci
  have sV := fun v => unitary_conjugate_local σ hcm hinv J hJ (Fv F v) (hrV v) b (lam v) (hv v).1 (m v) (hm v) H T T'
    hdetH hT hT' hrel' (a v) (c v) (hc0 v) (hav v) (hcv v)
  obtain ⟨⟨t1, t2, t3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have me := measurable_rmul σ hcm (AF F) n M (H.map (inclR (F := F) (AF F)))
  have mi : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E =>
      rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))) := by
    obtain ⟨r1, r2, r3, r4, -⟩ := hrI
    exact measurable_rmul σ hcm (Ainf F) n M _
  have mv : ∀ v, Measurable fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
      rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v))) := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := hrV v
    exact measurable_rmul σ hcm (Fv F v) n M _
  obtain ⟨κ, hE, hκ⟩ := hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m hminf hm
  refine ⟨κ, ?_, hκ⟩
  have hth := theta_map σ hcm J hJ μ 𝓕 hH hF G H T T' hGH hHG hrel' hrel.symm me
  have hlat := (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b n M).2.2.2
  have hfin : ∀ v, (cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤ := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := id (hrV v)
    obtain ⟨-, hW, hHm⟩ := coord_measures_haar F E σ hcm (Fv F v) d b (lam v) (hv v).1
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm M J hJ (Fv F v) (hrV v) n _ _ (m v) (hW n M) (hHm n) (hm v)
      (hermOf (Fv F v) σ T hT)).1
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hlat.1 v).1.measure_lt_top
  rw [isEulerProd_const_iff, ← hth]
  exact GlobalTheory.T.euler_product_measure_transport F E σ hcm d b n M _ (κ • minf (hermOf (Ainf F) σ T' hT')) (κ • minf (hermOf (Ainf F) σ T hT))
    (fun v => cfac E v • m v (hermOf (Fv F v) σ T' hT')) (fun v => cfac E v • m v (hermOf (Fv F v) σ T hT))
    (fun X => rmul (AF F) X (H.map (inclR (F := F) (AF F))))
    (fun X => rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))))
    (fun v X => rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v)))) me mi mv
    (fun X => ⟨projInf_rmul X H, fun v => projV_rmul v X H⟩)
    ((LatRat.latV_rational F E σ hcm d b n M).1 H hdetH)
    (ai / ci) (fun v => a v / c v) hq (by rw [Measure.map_smul, sInf, smul_comm]; exact mi.aemeasurable)
    (fun v => by rw [Measure.map_smul, sV v, smul_comm]; exact (mv v).aemeasurable) hfin
    ((isEulerProd_const_iff b _ κ _ _).1 hE)

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.DensEqOfPieces

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

theorem densEq_of_pieces (hE1 : PositivityTheory.PfSWUS.HMass.OneVecBinary) (hE2 : PositivityTheory.PfSWUS.HMass.OneVecBinaryMass)
    (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) (hBase : BaseOne) (hO : MassOne) : PositivityTheory.SiegelWeilFormula.Gen.DensEq :=
  densEq_of_C hB (swMeasCAll_of hBase isomC scaleC (stepC_of hE1 (massCAll_of hE2 hO))
    (notRepC_of hE1 (massCAll_of hE2 hO)))

end PositivityTheory.SiegelWeilFormula.Densx

end
end
end
