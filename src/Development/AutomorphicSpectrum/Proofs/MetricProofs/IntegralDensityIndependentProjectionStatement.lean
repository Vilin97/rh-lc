module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSheetLift
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsWeightedHomogeneousOfIsMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreDensityIndependentProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZeroStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimpleOfCount

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory Filter Topology Matrix SheetLift CxInt
open ReciprocityTheory.ChartRestriction.G.Geo (segre_differentiableAt)

section Count

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cone_lift_spec [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    (i0 : (k : K) → ι k) (k0 : K) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) (hne : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) ∈ conePts Q ∧ segre (lift i0 k0 (segre z)) = segre z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hne) k (Finset.mem_univ k)
  rw [lift_segre i0 k0 hne]
  refine ⟨cone_scale hP (c := fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩)
    (fun k => div_ne_zero (by split_ifs <;> simp [hne]) (h0 k)) hz, ?_⟩
  have hprod : ∏ k, (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩ = 1 := by
    rw [Finset.prod_div_distrib, Finset.prod_ite_eq' Finset.univ k0, if_pos (Finset.mem_univ _)]
    exact div_self hne
  rw [segre_bsmul, hprod]
  funext i
  rw [one_mul]

theorem cone_sheetLift {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ)
    (hev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h y' ∧ (∃ z ∈ conePts Q, segre z = h y') ∧
      Ψ (h y') = Fin.cons 1 y') :
    ∃ γ, IsSetSheet (conePts Q) Ψ y (h y) γ := by
  classical
  obtain ⟨hd0, ⟨z0, hz0, hs0⟩, -⟩ := hev.self_of_nhds
  rcases isEmpty_or_nonempty K with hK | ⟨⟨k0⟩⟩
  · refine ⟨fun _ => z0, hs0, hev.mono fun y' ⟨_, ⟨z, hz, hs⟩, hΨ⟩ => ?_⟩
    have hzz : z0 = z := funext fun p => (IsEmpty.false p.1).elim
    refine ⟨differentiableAt_const _, hzz ▸ hz, ?_⟩
    show Ψ (segre z0) = _
    rw [hzz, hs]
    exact hΨ
  · choose i0 hi0 using hz0.1
    have hy : h y i0 ≠ 0 := by
      rw [← hs0]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hi0 k
    have hnear : ∀ᶠ y' in 𝓝 y, h y' i0 ≠ 0 :=
      (differentiableAt_pi.mp hd0 i0).continuousAt.eventually_ne hy
    refine ⟨fun y' => lift i0 k0 (h y'), ?_, (hev.and hnear).mono fun y' ⟨⟨hd, ⟨z, hz, hs⟩, hΨ⟩, hne⟩ => ?_⟩
    · show segre (lift i0 k0 (h y)) = h y
      rw [← hs0]
      exact (cone_lift_spec hP i0 k0 hz0 (hs0 ▸ hy)).2
    · have hne' : segre z i0 ≠ 0 := hs ▸ hne
      obtain ⟨h1, h2⟩ := cone_lift_spec hP i0 k0 hz hne'
      refine ⟨differentiableAt_lift i0 k0 hd hne, ?_, ?_⟩
      · show lift i0 k0 (h y') ∈ conePts Q
        rw [← hs]
        exact h1
      · show Ψ (segre (lift i0 k0 (h y'))) = _
        rw [← hs, h2, hs]
        exact hΨ

theorem mem_setFibre_iff {S : Set ((Σ k, ι k) → ℂ)} {e m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ) (x : Fin m → ℂ) :
    (fun i' => x (σ.symm i')) ∈ setFibre S Ψ y ↔
      x ∈ setChartSet S σ Ψ ∧ chartProjMatrix σ Ψ *ᵥ x = y := by
  constructor
  · rintro ⟨z, hz, hzw, hΨ⟩
    have hx : x = fun a => segre z (σ a) := by
      funext a
      rw [hzw]
      simp
    refine ⟨⟨z, hz, by rw [hzw, hΨ]; rfl, hx⟩, ?_⟩
    funext r
    rw [chartProjMatrix_mulVec, hΨ]
    rfl
  · rintro ⟨⟨z, hz, h0, rfl⟩, hA⟩
    have hw : (fun i' => segre z (σ (σ.symm i'))) = segre z := by
      funext i'
      simp
    refine ⟨z, hz, hw.symm, ?_⟩
    rw [hw]
    funext j
    refine Fin.cases ?_ (fun r => ?_) j
    · rw [h0]
      rfl
    · have h := congrFun hA r
      rw [chartProjMatrix_mulVec, hw] at h
      rw [h]
      rfl

theorem cxGenericCount {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} (hQ : IsCxVar Q e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsSetGoodProj (conePts Q) Ψ) :
    ∃ d : ℕ, (∀ y, (setFibre (conePts Q) Ψ y).encard ≤ d) ∧
      volume {y : Fin e → ℂ | ¬ ((setFibre (conePts Q) Ψ y).encard = d ∧
        ∀ w ∈ setFibre (conePts Q) Ψ y, ∃ γ, IsSetSheet (conePts Q) Ψ y w γ)} = 0 := by
  classical
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  set σ := (Fintype.equivFin ((k : K) → ι k)).symm
  obtain ⟨hZ, hJ⟩ := cxChartModel hQ σ Ψ hΨ
  set I := setChartIdeal (conePts Q) σ Ψ
  set F := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).toFinset
  set A := chartProjMatrix σ Ψ
  have hF : ∀ J, J ∈ F ↔ J ∈ I.minimalPrimes := fun J => Set.Finite.mem_toFinset _

  have hU : ∀ x, (∃ J ∈ F, x ∈ zeroSet J) ↔ x ∈ setChartSet (conePts Q) σ Ψ := by
    intro x
    rw [← hZ]
    constructor
    · rintro ⟨J, hJF, hx⟩ q hq
      exact hx q (((hF J).1 hJF).1.2 hq)
    · intro hx
      have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => RingHom.mem_ker.2 (hx q hq)
      have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
      obtain ⟨J, hJm, hJle⟩ := Ideal.exists_minimalPrimes_le hle
      exact ⟨J, (hF J).2 hJm, fun q hq => RingHom.mem_ker.1 (hJle hq)⟩
  obtain ⟨hle, Δ, hΔ, hgen⟩ := ComponentsGenericCount.proof _ e F A
    (fun J hJF => ⟨((hF J).1 hJF).1.1, hJ J ((hF J).1 hJF)⟩)
    (fun J hJF J' hJ'F hJJ' => le_antisymm hJJ' (((hF J').1 hJ'F).2 ((hF J).1 hJF).1 hJJ'))

  have hfib : ∀ y, setFibre (conePts Q) Ψ y = (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) ''
      {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} := by
    intro y
    ext w
    constructor
    · intro hw
      have hw' : (fun i' => (fun a => w (σ a)) (σ.symm i')) = w := by
        funext i'
        simp
      rw [← hw'] at hw
      obtain ⟨hxS, hxA⟩ := (mem_setFibre_iff σ Ψ y (fun a => w (σ a))).1 hw
      exact ⟨_, ⟨(hU _).2 hxS, hxA⟩, hw'⟩
    · rintro ⟨x, ⟨hxU, hxA⟩, rfl⟩
      exact (mem_setFibre_iff σ Ψ y x).2 ⟨(hU x).1 hxU, hxA⟩
  have hinj : Function.Injective (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) := by
    intro x x' h
    funext a
    simpa using congrFun h (σ a)
  have henc : ∀ y, (setFibre (conePts Q) Ψ y).encard = {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard :=
    fun y => by rw [hfib y, hinj.injOn.encard_image]
  refine ⟨∑ J ∈ F, projDegree J A, fun y => (henc y).trans_le (hle y), ?_⟩
  refine measure_mono_null (fun y hy => ?_) (DiscriminantSheetCover.volume_zero_set Δ hΔ)
  by_contra h0
  obtain ⟨hcount, hsec⟩ := hgen y h0
  refine hy ⟨(henc y).trans hcount, fun w hw => ?_⟩
  rw [hfib y] at hw
  obtain ⟨x, ⟨hxU, hxA⟩, rfl⟩ := hw
  obtain ⟨U, g, hUo, hyU, hg, hgy, hgU⟩ := hsec x hxU hxA
  rw [← hgy]
  refine cone_sheetLift hR Ψ y (fun y' i' => g y' (σ.symm i')) ?_
  filter_upwards [hUo.mem_nhds hyU] with y' hy'
  obtain ⟨hAg, J, hJF, hgJ⟩ := hgU y' hy'
  obtain ⟨z, hz, hzw, hΨz⟩ := (mem_setFibre_iff σ Ψ y' (g y')).2 ⟨(hU _).1 ⟨J, hJF, hgJ⟩, hAg⟩
  have hgd : DifferentiableAt ℂ g y' := hg.differentiableAt (hUo.mem_nhds hy')
  exact ⟨differentiableAt_pi.2 fun i' => differentiableAt_pi.1 hgd (σ.symm i'), ⟨z, hz, hzw⟩, hΨz⟩

theorem cxSimple_of_count {S : Set ((Σ k, ι k) → ℂ)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (setFibre S Ψ y').encard ≤ d) (hy : (setFibre S Ψ y).encard = d)
    (hsh : ∀ w ∈ setFibre S Ψ y, ∃ γ, IsSetSheet S Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ setFibre S Ψ y) : CxComp.cxSimple S Ψ w := by
  have hF : (setFibre S Ψ y).Finite := Set.finite_of_encard_eq_coe hy
  choose! γ hγ using hsh
  obtain ⟨U, hU, hdisj⟩ := hF.t2_separation

  have hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ setFibre S Ψ y,
      (γ a y' ∈ S ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a := by
    refine (hF.eventually_all).2 fun a ha => ?_
    have hc := (segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt
    have hmem : U a ∈ 𝓝 (segre (γ a y)) := by
      rw [(hγ a ha).1]
      exact (hU a).2.mem_nhds (hU a).1
    filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2
    exact ⟨⟨h1.2.1, h1.2.2⟩, h2⟩

  have hfib : ∀ y', (∀ a ∈ setFibre S Ψ y, (γ a y' ∈ S ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧
      segre (γ a y') ∈ U a) → setFibre S Ψ y' = (fun a => segre (γ a y')) '' setFibre S Ψ y := by
    intro y' h
    have hinj : Set.InjOn (fun a => segre (γ a y')) (setFibre S Ψ y) := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)
    have hsub : (fun a => segre (γ a y')) '' setFibre S Ψ y ⊆ setFibre S Ψ y' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩
    refine ((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hinj.encard_image, hy]
    exact hbd y'
  refine ⟨y, γ w, hγ w hw, ?_⟩
  filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2
  rw [hfib q.1 hq.1] at hq2
  obtain ⟨a, ha, hqa⟩ := hq2
  have haw : a = w := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2
  rw [← hqa, haw]

end Count

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSheetSimpleNull

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory CxInt CxComp

theorem cxSheetSimpleNull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  intro K _ ι _ Q e Ψ hQ hΨ
  obtain ⟨d, hbd, hnull⟩ := cxGenericCount hQ Ψ hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (cxSimple_of_count hbd hgood.1 hgood.2 hw)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjection

section

@[expose] public section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep

theorem cx_fibre_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → ∀ y, (setFibre (conePts Q) Ψ y).Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite <;> assumption)

theorem cx_posDens_aemeasurable : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    AEMeasurable (cxPosDens (conePts Q) Ψ (pot L) g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable <;> assumption)

theorem cx_simple_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cxSheetSimpleNull <;> assumption)

theorem cxPosDens_split {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {Q : Ideal (MRingOver ℂ ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (setFibre (conePts Q) Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) → ∀ z ∈ conePts Q, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (cxPosDens (conePts Q) Ψ φ g y) =
      ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) Ψ φ ((E k).indicator g) y) := by
  classical
  unfold cxPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (setSheetDensity (conePts Q) Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (setSheetDensity (conePts Q) Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (setSheetDensity (conePts Q) Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ setFibre (conePts Q) Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSetSheet (conePts Q) Ψ y w γ
    · have hz : hs.choose y ∈ conePts Q := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [setSheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [setSheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [setSheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm

theorem cx_posPart_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) g y) =
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) g y) := by
  intro K _ ι _ Q e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0
  classical

  set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv

  set Gd : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ conePts Q ∧
    cxSimple (conePts Q) Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧
    cxSimple (conePts Q) Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hGd
  have key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Gd z → z ∈ W) ∧
      ∀ E, MeasurableSet E → Inv E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) (E.indicator g) y) =
          ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) (E.indicator g) y) := by
    intro z
    by_cases hz : Gd z
    · obtain ⟨W, hW, hzW, hWi, hWE⟩ := GlobalTheory.T.fibre_density_independent_projection K ι Q e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2
      exact ⟨W, hW, hWi, fun _ => hzW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [cxPosDens, setSheetDensity]
  choose W hWo hWi hzW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨f, hf⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE
  have hEm : ∀ k, MeasurableSet (E k) := MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet
  have hEW : ∀ k, E k ⊆ W (f k) := disjointed_subset _
  have hEd : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed _
  have hEi : ∀ k, Inv (E k) := by
    intro k c z' hc
    simp only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      hWi _ c z' hc]
  have hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z' := by
    intro k c z' hc
    simp only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]
  have hcov : ∀ z, Gd z → ∃ k, z ∈ E k := by
    intro z hq
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem 0 hiT
    have : z ∈ ⋃ k, E k := by
      rw [hE, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hzi⟩
    exact Set.mem_iUnion.1 this

  have hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsSetGoodProj (conePts Q) B → IsSetGoodProj (conePts Q) B' →
      (∀ z ∈ conePts Q, cxSimple (conePts Q) B ((B (segre z) 0)⁻¹ • segre z) →
        cxSimple (conePts Q) B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y) := by
    intro B B' hB hB' hc
    have hnull := measure_union_null (cx_simple_null K ι Q e B hP hB) (GlobalTheory.T.volume_nonsimple_fibres_eq_zero K ι Q e B B' hP hB hB')
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine cxPosDens_split _ _ E y (cx_fibre_finite K ι Q e B hP hB y) hEd fun w hw hs z hz hzw => ?_
    have hw1 : B w 0 = 1 := by
      obtain ⟨_, _, _, h⟩ := hw
      rw [h]
      rfl
    have hs1 : cxSimple (conePts Q) B w := by
      by_contra hn
      exact hy (Or.inl ⟨w, hw, hs, hn⟩)
    have hs2 : cxSimple (conePts Q) B' ((B' w 0)⁻¹ • w) := by
      by_contra hn
      exact hy (Or.inr ⟨w, hw, hs1, hn⟩)
    subst hzw
    refine hc z hz ?_ hs2
    rwa [hw1, inv_one, one_smul]
  have hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsSetGoodProj (conePts Q) B →
      (∀ᵐ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y)) →
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) g y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) B (pot L) ((E k).indicator g) y) := by
    intro B hB h2
    rw [lintegral_congr_ae h2, lintegral_tsum fun k =>
      (cx_posDens_aemeasurable K ι Q e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]
  rw [hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩),
    hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]
  exact tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)

end GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjectionStatement

section

@[expose] public section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)


theorem _root_.GlobalTheory.T.integral_density_independent_projection : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) g y) =
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) g y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep <;> assumption)
end
end
