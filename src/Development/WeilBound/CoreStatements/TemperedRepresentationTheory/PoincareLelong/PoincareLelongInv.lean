module

public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDivisorCompare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisorGeneralPointBranches
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConePtsSubsetMcPtsOfMinimal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DomCellLogNormMeasurableInvariant
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCxVarOfMemMinimalPrimesCxIdeal
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFinite
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDimLt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentsMeetNull
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LelongLimitAtBranches
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIdentityAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceReducedAwayZariski
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.Development

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFiniteStatement

section

@[expose] public section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)


theorem _root_.GlobalTheory.T.lintegral_fibre_logNorm_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top <;> assumption)
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartRatioImageNull

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

theorem ChartRatioImageNull.volume_eq_zero_of_dimH_lt {e : ℕ} {S : Set (Fin e → ℂ)}
    (hS : dimH S < 2 * (e : ℝ≥0∞)) : volume S = 0 := by
  let E : ((Σ _ : Fin e, Fin 2) → ℝ) ≃L[ℝ] (Fin e → ℂ) :=
    (Pi.basis (fun _ : Fin e => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin e, Fin 2) = 2 * e := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := hausdorffMeasure_of_dimH_lt (s := E ⁻¹' S) (d := ((2 * e : ℕ) : ℝ≥0)) (by
      rw [ContinuousLinearEquiv.dimH_preimage]
      simpa using hS)
    simpa using h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin e → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

theorem ChartRatioImageNull.proof : ChartRatioImageNull.Statement := by
  intro K _ ι _ J e Ψ hdim
  classical
  set S := {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
    (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} with hSdef
  by_cases hJ : J = ⊤
  · have hS : S = ∅ := by
      ext y
      simp only [hSdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, -⟩
      have h1 := hz 1 (hJ ▸ Submodule.mem_top)
      simp at h1
    rw [hS, measure_empty]
  have : Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Σ k, ι k) ℂ ⧸ J)
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := by
    rcases e with _ | m
    · exact absurd (h0.trans_lt hdim) (by simp)
    · exact ⟨m, rfl⟩
  have hle : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) ≤ (m : WithBot ℕ∞) := by
    rcases hx : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) with _ | x
    · exact bot_le
    · rw [hx] at hdim
      have hx' : x < (m : ℕ∞) + 1 := by
        have h5 : ((x : WithBot ℕ∞)) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hdim
        have h6 := WithBot.coe_lt_coe.1 h5
        exact_mod_cast h6
      exact WithBot.coe_le_coe.2 ((ENat.lt_add_one_iff (ENat.natCast_ne_top m)).1 hx')

  let eqv : (Σ k, ι k) ≃ Fin (Fintype.card (Σ k, ι k)) := Fintype.equivFin _
  let J' : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) := J.map (rename eqv)
  have hdim' : ringKrullDim (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J') ≤ (m : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv J J' (renameEquiv ℂ eqv).toRingEquiv rfl)]
    exact hle
  have hV' := GroundTheory.Heights₂.Heights.ZeroLocusDimH.full _ m J' hdim'
  let L : ((Σ k, ι k) → ℂ) ≃L[ℂ] (Fin (Fintype.card (Σ k, ι k)) → ℂ) :=
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) eqv).toContinuousLinearEquiv
  have hVsub : zeroLocus ℂ J ⊆ L ⁻¹' {x | ∀ q ∈ J', eval x q = 0} := by
    intro z hz q hq
    have hJle : J ≤ (RingHom.ker (eval (L z))).comap (rename eqv) := by
      intro p hp
      simp only [Ideal.mem_comap, RingHom.mem_ker, eval_rename]
      have h2 : (L z) ∘ eqv = z := by
        funext i; simp [L]
      rw [h2]
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz p hp
    exact Ideal.map_le_iff_le_comap.mpr hJle hq
  have hV : dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) ≤ 2 * (m : ℝ≥0∞) :=
    (dimH_mono hVsub).trans ((L.dimH_preimage _).le.trans hV')

  let G : ((Σ k, ι k) → ℂ) → (Fin (m + 1) → ℂ) := fun z j => (Ψ (segre z) 0)⁻¹ * Ψ (segre z) j.succ
  let U := {z : (Σ k, ι k) → ℂ | Ψ (segre z) 0 ≠ 0}
  have hSsub : S ⊆ G '' (zeroLocus ℂ J ∩ U) := by
    rintro y ⟨z, hz, hz0, hy⟩
    refine ⟨z, ⟨hz, hz0⟩, ?_⟩
    funext j
    have h3 := congrFun hy j.succ
    simpa [G] using h3.symm
  have hsmooth : ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z)) := by
    have h1 : ContDiff ℂ ⊤ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by
      apply contDiff_pi.2
      intro i
      exact contDiff_prod (fun k _ => contDiff_apply ℂ (fun _ => ℂ) _)
    exact (LinearMap.toContinuousLinearMap Ψ).contDiff.comp h1
  have hc : ∀ i, ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z) i) :=
    fun i => (contDiff_apply ℂ (fun _ => ℂ) i).comp hsmooth
  have hG : ∀ z ∈ U, ContDiffAt ℂ 1 G z := by
    intro z hz
    apply contDiffAt_pi.2
    intro j
    exact (((hc 0).contDiffAt.inv hz).mul (hc j.succ).contDiffAt).of_le le_top
  have hGdim : dimH (G '' (zeroLocus ℂ J ∩ U)) ≤ dimH (zeroLocus ℂ J ∩ U) := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro z hz
    obtain ⟨C, t, ht, hlip⟩ := (hG z hz.2).exists_lipschitzOnWith
    exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩
  apply ChartRatioImageNull.volume_eq_zero_of_dimH_lt
  calc dimH S ≤ dimH (G '' (zeroLocus ℂ J ∩ U)) := dimH_mono hSsub
    _ ≤ dimH (zeroLocus ℂ J ∩ U) := hGdim
    _ ≤ dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) := dimH_mono inter_subset_left
    _ ≤ 2 * (m : ℝ≥0∞) := hV
    _ < 2 * ((m + 1 : ℕ) : ℝ≥0∞) := by
      have h4 : 2 * m < 2 * (m + 1) := by omega
      exact_mod_cast h4

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableAbsFibreSumOfIsCxVar

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxAbs

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (absLogNorm)

theorem absFibreSum_eq_sum_components_ae {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι} {A : HermLine ι}
    {s : MRing ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w| =
      ∑ᶠ Q ∈ (cxIdeal P).minimalPrimes, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w| := by
  classical
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hmeet := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentsMeetNull.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDimLt.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartRatioImageNull.proof K ι P e Ψ hfin.toFinset hP hΨ
    (fun W hW => hfin.mem_toFinset.1 hW)
  filter_upwards [compl_mem_ae_iff.mpr hmeet, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hone : ∀ Q ∈ (cxIdeal P).minimalPrimes, ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q →
      z ∈ conePts Q' → Ψ (segre z) = Fin.cons 1 y → Q' = Q := by
    intro Q hQ Q' hQ' z hz hz' hΨz
    by_contra hne
    refine hyN ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hΨz, Q, hfin.mem_toFinset.2 hQ, Q',
      hfin.mem_toFinset.2 hQ', fun h => hne h.symm, ?_, ?_⟩
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz.2 f hf
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz'.2 f hf
  have hunion : fibre P Ψ y = ⋃ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y := by
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz, hzw, hΨw⟩
      obtain ⟨Q, hQ, hzQ⟩ := exists_minimal_of_mem_mcPts hz
      exact ⟨Q, hQ, z, hzQ, hzw, hΨw⟩
    · rintro ⟨Q, hQ, z, hz, hzw, hΨw⟩
      exact ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hzw, hΨw⟩
  have hsub : ∀ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y ⊆ fibre P Ψ y := by
    intro Q hQ w hw
    rw [hunion]
    exact Set.mem_biUnion hQ hw
  have hdisj : ((cxIdeal P).minimalPrimes).PairwiseDisjoint fun Q => setFibre (conePts Q) Ψ y := by
    intro Q hQ Q' hQ' hne
    refine Set.disjoint_left.2 ?_
    rintro w ⟨z, hz, hzw, hΨw⟩ ⟨z', hz', hzw', -⟩
    have hzQ' : z ∈ conePts Q' := mem_conePts_of_segre_eq hP hQ' hz' hz.1 (hzw'.trans hzw.symm)
    exact hne (hone Q hQ Q' hQ' z hz hzQ' (by rw [hzw]; exact hΨw)).symm
  rw [hunion, finsum_mem_biUnion hdisj hfin
    (fun Q hQ => (fibreFinite K ι P e Ψ hP hΨ y).subset (hsub Q hQ))]
  refine finsum_mem_congr rfl fun Q hQ => finsum_mem_congr rfl fun w hw => ?_
  refine congrArg abs ?_
  have hiff : (∃ γ, IsSheet P Ψ y w γ) ↔ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ :=
    ⟨fun ⟨γ, h⟩ => ⟨γ, isSetSheet_of_isSheet hP hQ (hone Q hQ) hw h⟩,
      fun ⟨γ, h⟩ => ⟨γ, isSheet_of_isSetSheet hQ h⟩⟩
  rw [sheetDensity_eq_setSheetDensity]
  unfold setSheetDensity
  by_cases hex : ∃ γ, IsSheet P Ψ y w γ
  · have hexQ := hiff.1 hex
    have hexP : ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dite_eq_left hexP, dite_eq_left hexQ]
    exact hind w _ _ hexP.choose_spec (isSheet_of_isSetSheet hQ hexQ.choose_spec)
  · have hexQ : ¬ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ := fun h => hex (hiff.2 h)
    have hexP : ¬ ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dite_eq_right hexP, dite_eq_right hexQ]

theorem abs_setSheetDensity_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} (hS : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (A : HermLine ι) (s : MRingOver ℂ ι) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    |setSheetDensity S Ψ φ (logNormC A s) y w| =
      max (setSheetDensity S Ψ φ (absLogNorm A s) y w) 0 +
        max (setSheetDensity S Ψ φ (fun z => -absLogNorm A s z) y w) 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · have hz := hS _ hγ.choose_spec.2.self_of_nhds.2.1
    have ha : absLogNorm A s (hγ.choose y) = |logNormC A s (hγ.choose y)| := by
      simp only [absLogNorm, if_pos hz]
    beta_reduce
    rw [ha, abs_mul]
    generalize maDensity (fun j y' => φ j (hγ.choose y')) y = m
    generalize logNormC A s (hγ.choose y) = g
    have hg := abs_nonneg g
    rcases le_total 0 m with hm | hm
    · rw [abs_of_nonneg hm, max_eq_left (mul_nonneg hg hm),
        max_eq_right (by nlinarith : -|g| * m ≤ 0), add_zero]
    · rw [abs_of_nonpos hm, max_eq_right (by nlinarith : |g| * m ≤ 0),
        max_eq_left (by nlinarith : 0 ≤ -|g| * m), zero_add]
      ring
  · simp

theorem integrable_absFibreSum_of_isCxVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) (hsQ : s ∉ Q) :
    Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) := by
  classical
  have hS : ∀ z ∈ conePts Q, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun z hz => hz.1
  have hfin := GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ hQ hΨ
  have hm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.measurable_absLogNorm A hA s
  have hdeg := fun (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) =>
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.absLogNorm_blockScale A hAa hs hc z
  have h1 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm hdeg
  have h2 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm.neg
    (g := fun z => -absLogNorm A s z) (fun c z hc => by simp only [hdeg c z hc])
  have heq : (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) =
      fun y => cxPosDens (conePts Q) Ψ (pot L) (absLogNorm A s) y +
        cxPosDens (conePts Q) Ψ (pot L) (fun z => -absLogNorm A s z) y := by
    funext y
    unfold cxPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => abs_setSheetDensity_eq hS Ψ (pot L) A s y w
  refine ⟨?_, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => abs_nonneg _)).2
    (GlobalTheory.T.lintegral_fibre_logNorm_finite K ι Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ)⟩
  rw [heq]
  exact (h1.add h2).aestronglyMeasurable

theorem ptsAbsIntegrable : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hae := absFibreSum_eq_sum_components_ae hP hΨ hL hA hs
  obtain ⟨a, hAa, hsa, hsP⟩ := hs
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hsa' : IsMultiHomog (map (Int.castRingHom ℂ) s : MRingOver ℂ ι) a := fun m hm k =>
    hsa m (support_map_subset _ _ hm) k
  have hcomp : ∀ Q ∈ (cxIdeal P).minimalPrimes, Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w|) := by
    intro Q hQ
    obtain ⟨hQv, hc⟩ := isCxVar_of_mem_minimalPrimes_cxIdeal K ι P e hP Q hQ
    refine integrable_absFibreSum_of_isCxVar hQv
      (fun z hz => hΨ z (conePts_subset_mcPts_of_minimal hQ hz)) hL hA hAa hsa' fun hmem => hsP ?_
    rw [← hc]
    exact hmem
  refine (integrable_finsetSum hfin.toFinset fun Q hQ => hcomp Q (hfin.mem_toFinset.1 hQ)).congr ?_
  filter_upwards [hae] with y hy
  rw [hy]
  exact (finsum_mem_eq_finite_toFinset_sum _ hfin).symm

end GlobalTheory.CompanionTheory.Ar.Pub.CxAbs
end
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.PoincareLelongInv

section

@[expose] public section

namespace PositivityTheory.Tls2.Pl

theorem poincareLelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong :=
  poincareLelong_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

theorem poincareLelongInv : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv :=
  poincareLelongInv_of_leaves GlobalTheory.CompanionTheory.Ar.Pub.CxAbs.ptsAbsIntegrable GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral
    GlobalTheory.CompanionTheory.Ar.chartDivisorCompare GlobalTheory.CompanionTheory.ComplexSets.divisorGeneralPointBranches
    GlobalTheory.CompanionTheory.Ar.Lelong.lelongLimitAtBranches GlobalTheory.CompanionTheory.Heights.BranchOrder.localOrder
    GlobalTheory.CompanionTheory.VarLelong.regMassNearSmall

end PositivityTheory.Tls2.Pl
end
end
