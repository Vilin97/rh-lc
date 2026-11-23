module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomainStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomain
public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreserving
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.MoebiusJetDuality.StatementU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodicSchwarzLemma
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingGlueLowerUnitriangularBlocksStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralProdChartCoordinatesEqProd

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivialStatement

section

@[expose] public section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.domain_point_stabilizer_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1 := by
  first | exact @GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq | exact GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq | (intros; apply GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomainStatement

section

@[expose] public section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q → ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  first | exact @GlobalTheory.FlagFibre.signs_over_dom | exact GlobalTheory.FlagFibre.signs_over_dom | (intros; apply GlobalTheory.FlagFibre.signs_over_dom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomainStatement

section

@[expose] public section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  first | exact @GlobalTheory.FlagFibreInt.lintegral_dens_glue | exact GlobalTheory.FlagFibreInt.lintegral_dens_glue | (intros; apply GlobalTheory.FlagFibreInt.lintegral_dens_glue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreservingStatement

section

@[expose] public section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.lintegral_pi_fibre_measurePreserving : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  first | exact @GlobalTheory.ProdFibre.lintegral_pi_fibre | exact GlobalTheory.ProdFibre.lintegral_pi_fibre | (intros; apply GlobalTheory.ProdFibre.lintegral_pi_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinatesStatement

section

@[expose] public section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.measurePreserving_flagFibreChartCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), MeasurePreserving (coords X κ) volume volume := by
  first | exact @GlobalTheory.FlagFibre.measurePreserving_coords_sorted | exact GlobalTheory.FlagFibre.measurePreserving_coords_sorted | (intros; apply GlobalTheory.FlagFibre.measurePreserving_coords_sorted <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCurry

section

@[expose] public section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.FlagFibre

theorem measurePreserving_curry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  apply _root_.GlobalTheory.IntBall.measurePreserving_curry_lowCoord <;> assumption

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

theorem mem_OmF_of_proj (hp : X.p0 = r - j) {z : V (nd X)} (hz : proj X hj κ z ∈ DomFlat Tau j (r - j)) :
    z ∈ OmF X (x0F X) := by
  intro τ
  obtain ⟨t, rfl⟩ := κ.surjective τ
  refine ⟨?_, fun i => ?_⟩
  · have e : mat (cpt X (x0F X) z) (κ t) = mat (x0F X) (κ t) * uni (coords X κ z t) := rfl
    rw [e, det_mul, det_uni, mul_one]
    exact det_x0F X _
  · rw [dmin_cpt X κ z t i, hp]
    refine GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) _ (reindex_sgn hj) _ ?_ i
    have h := hz t
    have e : unflat (proj X hj κ z) t = toMat (base (idx hj) (coords X κ z t)) := by
      ext a b; exact proj_eq X hj κ z t (a, b)
    rwa [e] at h

theorem inter_OmF (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hD : S ⊆ DomFlat Tau j (r - j)) :
    proj X hj κ ⁻¹' S ∩ OmF X (x0F X) = proj X hj κ ⁻¹' S :=
  Set.inter_eq_left.2 fun _ hz => mem_OmF_of_proj X hj κ hp (hD hz)

theorem densF_eq (z : V (nd X)) :
    densF X (x0F X) z = ∏ t, dens (sgnMat r X.p0) (coords X κ z t) := by
  rw [densF, ← κ.prod_comp]
  exact Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => by rw [dmin_cpt X κ z t]

theorem muF_preimage (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hS : MeasurableSet S)
    (hD : S ⊆ DomFlat Tau j (r - j)) :
    muF X (x0F X) (proj X hj κ ⁻¹' S) =
      ENNReal.ofReal ((flagConst j * flagConst (r - j))⁻¹ ^ Fintype.card Tau) * muD Tau j (r - j) S := by
  have hS' := measurable_proj X hj κ hS
  set c := MeasurableEquiv.curry Tau (Fin j × Fin (r - j)) ℂ with hc
  set φ : (Tau → Fin j × Fin (r - j) → ℂ) → ℝ≥0∞ := (c.symm ⁻¹' S).indicator 1 with hφ
  have hφm : Measurable φ := measurable_one.indicator (c.symm.measurable hS)
  have hDm : Measurable fun y => ENNReal.ofReal (dens (sgnMat r (r - j)) y) := (measurable_dens _).ennreal_ofReal
  have key := GlobalTheory.T.lintegral_pi_fibre_measurePreserving Tau _ _ _ (glue (idx hj)) (base (idx hj)) _ φ (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ _ (isBlockOrderedSumEquiv_trueIndex hj))
    (measurable_base _) (base_glue (isBlockOrderedSumEquiv_trueIndex hj)) hDm hφm
  have hm : Measurable fun y : Tau → Low r → ℂ => φ (fun t => base (idx hj) (y t)) *
      ∏ t, ENNReal.ofReal (dens (sgnMat r (r - j)) (y t)) :=
    (hφm.comp (Measurable.of_eval fun t => (measurable_base _).comp (measurable_pi_apply t))).mul
      (Finset.measurable_prod _ fun t _ => hDm.comp (measurable_pi_apply t))
  rw [← (GlobalTheory.T.measurePreserving_flagFibreChartCoordinates E r X Tau κ).lintegral_comp hm,
    ← (measurePreserving_curry Tau (Fin j × Fin (r - j))).lintegral_comp_emb c.measurableEmbedding] at key
  rw [muF, muD, withDensity_apply _ hS', withDensity_apply _ hS, Measure.restrict_restrict hS',
    Measure.restrict_restrict hS, Set.inter_eq_left.2 hD,
    inter_OmF X hj κ hp hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator hS', ← lintegral_indicator hS]
  refine Eq.trans (lintegral_congr fun z => ?_) (key.trans (lintegral_congr fun v => ?_))
  · have e : c.symm (fun t => base (idx hj) (coords X κ z t)) = proj X hj κ z :=
      funext fun s => (proj_eq X hj κ z s.1 s.2).symm
    by_cases h : proj X hj κ z ∈ S
    · rw [Set.indicator_of_mem (show z ∈ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_mem (by rwa [Set.mem_preimage, e]), Pi.one_apply, one_mul, densF_eq X κ, hp,
        ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _]
    · rw [Set.indicator_of_notMem (show z ∉ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_notMem (by rwa [Set.mem_preimage, e]), zero_mul]
  · by_cases h : v ∈ S
    · rw [Set.indicator_of_mem h, hφ, Set.indicator_of_mem (show c v ∈ c.symm ⁻¹' S from h), Pi.one_apply, one_mul]
      have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
      have hv : ∀ t, toMat (c v t) ∈ hcDom j (r - j) := hD h
      have hpos : ∀ t, 0 ≤ (hQ (toMat (c v t))).det.re ^ (-((j + (r - j) : ℕ) : ℤ)) := fun t =>
        zpow_nonneg (Complex.pos_iff.1 (PosDef.det_pos (hv t))).1.le _
      rw [Finset.prod_congr rfl fun t _ => GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) (sgnMat r (r - j))
        (reindex_sgn hj) (c v t) (hv t), ← ENNReal.ofReal_prod_of_nonneg fun t _ => div_nonneg (hpos t) hc0.le,
        ← ENNReal.ofReal_mul (by positivity), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        div_eq_inv_mul, inv_pow]
      rfl
    · rw [Set.indicator_of_notMem h, hφ, Set.indicator_of_notMem (show c v ∉ c.symm ⁻¹' S from h), zero_mul]

theorem covol_eq_muD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r)
    (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ F, IsFD (gammaU X hj κ) F →
    muD Tau j (r - j) F < ⊤ ∧
      covol X = grassConst j (r - j) ^ Fintype.card Tau * (muD Tau j (r - j) F).toReal := by
  intro E _ _ _ r j X hj Tau _ κ hp F hF
  obtain ⟨F', hm, hsub, h0, hfs⟩ := GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain E r j X hj Tau κ hp (GlobalTheory.T.domain_point_stabilizer_trivial E r j X hj Tau κ hp)
    (fun N hN hD h => by rw [muF_preimage X hj κ hp hN hD, h, mul_zero]) F hF
  have hD := hsub.trans hF.2.1
  rw [inter_OmF X hj κ hp hD] at hfs
  obtain ⟨h1, h2⟩ := covol_eq X (isOrth_x0F X) hfs
  have e : muD Tau j (r - j) F' = muD Tau j (r - j) F := (measure_eq_measure_of_null_diff hsub h0)
  have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
  rw [muF_preimage X hj κ hp hm hD, e] at h1 h2
  refine ⟨?_, ?_⟩
  · refine lt_top_iff_ne_top.2 fun h => h1.ne ?_
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  · have e1 : flagConst r = grassConst j (r - j) * (flagConst j * flagConst (r - j)) := by
      rw [← mul_assoc, ← flagConst_add, Nat.add_sub_cancel' hj]
    have e2 : X.Ψ.card = Fintype.card Tau := by rw [Fintype.card_congr κ, Fintype.card_coe]
    rw [h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), e1, e2, mul_pow, inv_pow]
    field_simp

end GlobalTheory.FlagFibre
end
end
end
