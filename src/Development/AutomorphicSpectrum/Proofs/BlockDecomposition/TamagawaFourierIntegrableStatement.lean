module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversion
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Compactness.Paracompact
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasure

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit


open GlobalTheory.SWQ GlobalTheory.PoissonReindex in
theorem GlobalTheory.SWLit.tamagawa_eq_map_pi : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  intro F _ _ κ _ N e ν hν μ ⟨hμ, 𝓕, h𝓕1, h𝓕⟩
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨hHaar, hmem, -, -, D, hDm, hD, hD1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  haveI := hμ
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  let L := (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range
  let L' := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))
  have hmap : ∀ g : L', T g.1 ∈ L := by
    intro g
    obtain ⟨ξ, hξ⟩ := (hmem g.1).1 g.2
    exact ⟨fun i => ξ (e i), by rw [hξ]; rfl⟩
  let φ : L' → L := fun g => ⟨T g.1, hmap g⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => Subtype.ext (T.injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, η, rfl⟩
    refine ⟨⟨rat fun j => η (e.symm j), (hmem _).2 ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
    funext i
    show algebraMap F (AF F) (η (e.symm (e i))) = algebraMap F (AF F) (η i)
    rw [e.symm_apply_apply]
  have hmp : MeasurePreserving Tm.symm (Measure.map Tm (muV N ν)) (muV N ν) :=
    MeasurePreserving.symm Tm ⟨Tm.measurable, rfl⟩
  have hD' : IsAddFundamentalDomain L (Tm.symm ⁻¹' D) (Measure.map Tm (muV N ν)) := by
    refine hD.preimage_of_equiv hmp.quasiMeasurePreserving hφ fun g x => ?_
    show T.symm (T g.1 + x) = g.1 + T.symm x
    rw [map_add (f := _), T.symm_apply_apply]
  have hD'1 : Measure.map Tm (muV N ν) (Tm.symm ⁻¹' D) = 1 := by
    rw [hmp.measure_preimage hDm.nullMeasurableSet, hD1]
  have hac : μ ≪ Measure.map Tm (muV N ν) := by
    rw [hr]
    exact Measure.smul_absolutelyContinuous
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable L := by
    have : Countable (Set.range (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ)) :=
      (Set.countable_range _).to_subtype
    exact this
  have h1 : μ (Tm.symm ⁻¹' D) = 1 := by
    rw [← h𝓕1]
    exact (hD'.mono hac).measure_eq h𝓕
  have hr1 : r = 1 := by
    rw [hr, Measure.smul_apply, hD'1] at h1
    simpa using h1
  rw [hr1, one_smul] at hr
  exact hr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasureStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit


theorem _root_.GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  first | exact @GlobalTheory.SWLit.tamagawa_eq_map_pi | exact GlobalTheory.SWLit.tamagawa_eq_map_pi | (intros; apply GlobalTheory.SWLit.tamagawa_eq_map_pi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierInversionSchwartzAdelic

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section

namespace GlobalTheory.TamFourier

theorem fourier_inversion_tamagawa : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ → ∀ Φ ∈ schA F κ, ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x) := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ Φ hΦ x
  have hFT : ∀ H ∈ schA F κ, (fun y : κ → AF F => ∫ z, H z * ψ (z ⬝ᵥ y) ∂μ) ∈ schA F κ :=
    GlobalTheory.T.adelicFourier_mem_schwartz_totallyReal F hF ψ hψ κ μ hμ.1
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hψ
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : GlobalTheory.SWQ.Ctx ψ lam ν a := ⟨hF, hψ, hlam, hν, fun _ => by norm_num [a]⟩
  have hμeq := GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure F κ N e ν hν μ hμ
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := GlobalTheory.PoissonReindex.reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  have key : ∀ (H : (κ → AF F) → ℂ) (y' : Fin N → AF F),
      ∫ z, H z * ψ (z ⬝ᵥ T y') ∂μ = GlobalTheory.SWQ.Fo ψ ν a (fun u => H (T u)) y' := by
    intro H y'
    have hm : μ = Measure.map Tm (GlobalTheory.SWQ.muV N ν) := hμeq
    rw [hm, integral_map_equiv]
    simp only [GlobalTheory.SWQ.Fo, hTm, a, GlobalTheory.PoissonReindex.Bd_half, T, GlobalTheory.PoissonReindex.dot_reidx]
  set G : (κ → AF F) → ℂ := fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have hG' : (fun u => G (T u)) = GlobalTheory.SWQ.Fo ψ ν a Φ' := funext fun u => key Φ u
  have hGG : (fun u => (∫ z, G z * ψ (z ⬝ᵥ T u) ∂μ)) = GlobalTheory.SWQ.Fo ψ ν a (GlobalTheory.SWQ.Fo ψ ν a Φ') := by
    rw [← hG']
    exact funext fun u => key G u
  have hΦs : Φ' ∈ schA F (Fin N) := GlobalTheory.PoissonReindex.mem_schA_reidx e hΦ
  have hGs : G ∈ schA F κ := hFT Φ hΦ
  have hGGs : (fun y : κ → AF F => ∫ z, G z * ψ (z ⬝ᵥ y) ∂μ) ∈ schA F κ := hFT G hGs
  have hD1 : GlobalTheory.SWQ.Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦs
  have hD2 : GlobalTheory.SWQ.Decay (GlobalTheory.SWQ.Fo ψ ν a Φ') := by
    rw [← hG']
    exact GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ (GlobalTheory.PoissonReindex.mem_schA_reidx e hGs)
  have hD3 : GlobalTheory.SWQ.Decay (GlobalTheory.SWQ.Fo ψ ν a (GlobalTheory.SWQ.Fo ψ ν a Φ')) := by
    rw [← hGG]
    exact GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ (GlobalTheory.PoissonReindex.mem_schA_reidx e hGGs)
  have hinv := GlobalTheory.SWQ.fourier_inversion F N ψ lam ν a hC Φ' hD1 hD2 hD3
  have hx : T (T.symm x) = x := T.apply_symm_apply x
  have h1 := congrFun hGG (T.symm x)
  rw [hinv, hx] at h1
  have hcomm : ∀ y : κ → AF F, y ⬝ᵥ x = x ⬝ᵥ y := fun y => dotProduct_comm y x
  calc ∫ y, G y * ψ (y ⬝ᵥ x) ∂μ = ∫ z, G z * ψ (z ⬝ᵥ x) ∂μ := rfl
    _ = GlobalTheory.SWQ.Da (-1) Φ' (T.symm x) := h1
    _ = Φ (-x) := by
      simp only [GlobalTheory.SWQ.Da, hΦ', neg_one_smul, map_neg, hx]

end GlobalTheory.TamFourier

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrable

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem pair_abs {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) [SFinite μ]
    (ν : Measure Y) [SFinite ν] (k : X → Y → ℂ) (e : X → X → ℂ)
    (hk : Measurable (Function.uncurry k)) (he : Measurable (Function.uncurry e))
    (hkn : ∀ v y, ‖k v y‖ = 1) (hen : ∀ v z, ‖e v z‖ = 1)
    (φ : Y → ℂ) (hφ : Integrable φ ν) (hJ : Integrable (fun v => ∫ y, φ y * k v y ∂ν) μ)
    (Φ : X → ℂ) (hΦ : Integrable Φ μ) (H : X → ℂ) (hHi : Integrable H μ)
    (hH : ∀ v, H v = ∫ z, Φ z * e v z ∂μ) (hinv : ∀ y, ∫ v, H v * k v y ∂μ = 0) :
    ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ = 0 := by
  have h1 : Integrable (Function.uncurry fun (z v : X) =>
      (∫ y, φ y * k v y ∂ν) * e v z * Φ z) (μ.prod μ) := by
    refine Integrable.mono (hΦ.mul_prod hJ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × X => ∫ y, φ y * k p.2 y ∂ν) (μ.prod μ) :=
        hJ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × X => e p.2 p.1) (μ.prod μ) :=
        (he.comp measurable_swap).aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × X => Φ p.1) (μ.prod μ) :=
        hΦ.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨z, v⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hen, mul_one]
      exact le_of_eq (mul_comm _ _)
  have h2 : Integrable (Function.uncurry fun (v : X) (y : Y) => φ y * k v y * H v) (μ.prod ν) := by
    refine Integrable.mono (hHi.mul_prod hφ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × Y => φ p.2) (μ.prod ν) :=
        hφ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × Y => k p.1 p.2) (μ.prod ν) :=
        hk.aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × Y => H p.1) (μ.prod ν) :=
        hHi.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨v, y⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hkn, mul_one]
      exact le_of_eq (mul_comm _ _)
  calc ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ
      = ∫ z, ∫ v, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := by
        congr 1; funext z
        exact (integral_mul_const (Φ z) _).symm
    _ = ∫ v, ∫ z, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := integral_integral_swap h1
    _ = ∫ v, (∫ y, φ y * k v y ∂ν) * H v ∂μ := by
        congr 1; funext v
        rw [hH v, ← integral_const_mul]
        congr 1; funext z; ring
    _ = ∫ v, ∫ y, φ y * k v y * H v ∂ν ∂μ := by
        congr 1; funext v
        exact (integral_mul_const (H v) _).symm
    _ = ∫ y, ∫ v, φ y * k v y * H v ∂μ ∂ν := integral_integral_swap h2
    _ = ∫ y, φ y * ∫ v, H v * k v y ∂μ ∂ν := by
        congr 1; funext y
        rw [← integral_const_mul]
        congr 1; funext v; ring
    _ = 0 := by simp [hinv]

theorem haar_facts {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] :
    SFinite μ ∧ μ.IsNegInvariant :=
  ⟨inferInstance, inferInstance⟩

theorem pair_ring {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (μ : Measure (κ → R)) [SFinite μ]
    [μ.IsNegInvariant] (ψ : AddChar R ℂ) (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → R)
    (hφ : Integrable φ ν) (hg : Measurable g)
    (hJ : Integrable (fun v : κ → R => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ)
    (Φ : (κ → R) → ℂ) (hΦi : Integrable Φ μ)
    (hHi : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ)
    (hinv : ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x))
    (h0 : ∀ y, Φ (g y) = 0) :
    ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → R) × (κ → R) => p.1 ⬝ᵥ p.2) :=
    continuous_fst.dotProduct continuous_snd
  have hk : Measurable (Function.uncurry fun (v : κ → R) (y : Y) => ψ (v ⬝ᵥ g y)) := by
    have hm : Measurable (fun p : (κ → R) × (κ → R) => ψ (p.1 ⬝ᵥ p.2)) :=
      (hc.comp hdot).measurable
    exact hm.comp (measurable_fst.prodMk (hg.comp measurable_snd))
  have he : Measurable (Function.uncurry fun (v z : κ → R) => ψ (-(v ⬝ᵥ z))) :=
    (hc.comp hdot.neg).measurable
  have hHi' : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (-(w ⬝ᵥ z)) ∂μ) μ := by
    refine hHi.comp_neg.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [dotProduct_neg]
    congr 1; funext z
    rw [dotProduct_comm]
  have hinv' : ∀ y, ∫ v, (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y) ∂μ = 0 := by
    intro y
    have h1 := hinv (-(g y))
    rw [neg_neg, h0 y] at h1
    refine (integral_neg_eq_self
      (fun v => (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y)) μ).symm.trans (Eq.trans ?_ h1)
    congr 1; funext v
    simp only [neg_dotProduct, neg_neg, dotProduct_neg]
    congr 1; congr 1; funext z
    rw [dotProduct_comm]
  exact pair_abs μ ν (fun v y => ψ (v ⬝ᵥ g y)) (fun v z => ψ (-(v ⬝ᵥ z))) hk he
    (fun v y => hn _) (fun v z => hn _) φ hφ hJ Φ hΦi _ hHi' (fun v => rfl) hinv'

theorem pair_vanish : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Y _ ν _ φ g hφ hg hJ Φ hΦ h0
  have hH : μ.IsAddHaarMeasure := hμ.1
  obtain ⟨hS, hN⟩ := haar_facts μ
  have hc : Continuous ψ := hψ.1
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  obtain ⟨-, -, hint⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  have hinv := GlobalTheory.TamFourier.fourier_inversion_tamagawa F hF ψ hψ κ μ hμ Φ hΦ
  have hHi : Integrable (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ := by
    by_contra hni
    have hzero : ∀ x, Φ x = 0 := by
      intro x
      have h1 := hinv (-x)
      rw [neg_neg] at h1
      rw [← h1]
      apply integral_undef
      intro hi
      apply hni
      exact integrable_of_mul_unimodular μ (fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ)
        (fun y => ψ (y ⬝ᵥ -x)) hi
        ((hc.comp (continuous_id.dotProduct continuous_const)).aestronglyMeasurable) (fun y => hn _)
    apply hni
    have hfun : (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) = fun _ => (0 : ℂ) := by
      funext w; simp [hzero]
    rw [hfun]
    exact integrable_zero _ _ _
  exact pair_ring μ ψ hc hn ν φ g hφ hg hJ Φ (hint μ hH) hHi hinv h0

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrableStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.tamagawa_fourier_integrable : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish <;> assumption)
end
end
