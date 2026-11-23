module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchFillDimension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchGermDimOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCentredDiscCoverCurve
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDominantFibreBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOffZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceOnComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarMassNearSmall
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchFillDimension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchGermDimOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCentredDiscCoverCurve
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveMinimalPrimeQuotient
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDominantFibreBound
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOffZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimComponentBound
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogIntegrable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StReducedNormalisationPlace
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
import Mathlib.Tactic.TypeStar
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PReducedNormalisationPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarIntAdd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarMassNearSmall
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroDimIsolated
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Algebra.MvPolynomial
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveMinimalPrimeQuotient

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveMinimalPrimeQuotient.proof : CurveMinimalPrimeQuotient.Statement := by
  intro n I q p hp
  have hpP : p.IsPrime := hp.1.1

  let ext : Ideal (MvPolynomial (Fin n) ℂ) → Ideal (Localization.AtPrime (RingHom.ker (eval q))) :=
    fun K ↦ K.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  let mk := Ideal.Quotient.mk (ext I)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomp : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) =
      mk.comp (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) := rfl

  let P : Ideal (Localization.AtPrime (RingHom.ker (eval q))) := p.comap mk
  have hPP : P.IsPrime := Ideal.comap_isPrime mk p
  have hIP : ext I ≤ P := fun x hx ↦ by
    change mk x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact p.zero_mem
  have hpmap : P.map mk = p := Ideal.map_comap_of_surjective mk hmk p
  let J : Ideal (MvPolynomial (Fin n) ℂ) :=
    P.comap (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  have hJP : J.IsPrime := Ideal.comap_isPrime _ P
  have hJmem : ∀ f, f ∈ J ↔ algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ p := fun f ↦ by
    rw [hcomp]; rfl
  have hextJ : ext J = P := IsLocalization.map_under (RingHom.ker (eval q)).primeCompl _ P
  have hIJ : I ≤ J := fun f hf ↦ hIP (Ideal.mem_map_of_mem _ hf)
  have hJm : J ≤ RingHom.ker (eval q) := by
    intro f hf
    by_contra h
    exact hpP.ne_top (Ideal.eq_top_of_isUnit_mem _ ((hJmem f).1 hf)
      (isUnit_algebraMap_curveLocalRing I q f fun h' ↦ h (RingHom.mem_ker.2 h')))

  have hJmin : J ∈ I.minimalPrimes := by
    refine ⟨⟨hJP, hIJ⟩, fun J' hJ' hJ'J ↦ ?_⟩
    obtain ⟨hJ'P, hIJ'⟩ := hJ'
    have hdisj : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J' :=
      Set.disjoint_left.2 fun x hx hx' ↦ hx (hJm (hJ'J hx'))
    have hP'P : (ext J').IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J' hJ'P hdisj
    have hIP' : ext I ≤ ext J' := Ideal.map_mono hIJ'
    have hker : RingHom.ker mk ≤ ext J' := by
      rw [Ideal.mk_ker]; exact hIP'
    have hp'P : ((ext J').map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk hker
    have hp'le : (ext J').map mk ≤ p := by
      rw [← hpmap, ← hextJ]
      exact Ideal.map_mono (Ideal.map_mono hJ'J)
    have hpp' : p ≤ (ext J').map mk := hp.2 ⟨hp'P, bot_le⟩ hp'le
    intro f hf
    have h1 : mk (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) ∈ (ext J').map mk :=
      hpp' ((hJmem f).1 hf)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective mk hmk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hIP'] at h1
    have h2 := (IsLocalization.under_map_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl
      (Localization.AtPrime (RingHom.ker (eval q))) hJ'P hdisj)
    rw [← h2]
    exact h1

  have hle : ext I ≤ ext J := Ideal.map_mono hIJ
  refine ⟨J, hJmin, hJm, (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q),
    Ideal.Quotient.factor_surjective hle, ?_, fun f ↦ Ideal.Quotient.factor_mk hle _⟩
  change RingHom.ker (Ideal.Quotient.factor hle) = p
  rw [Ideal.Quotient.factor_ker, hextJ]
  exact hpmap

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimComponentBound

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem comap_curveLocalRing_strictMono (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    StrictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q))) := by
  refine Monotone.strictMono_of_injective (fun P Q h ↦ Ideal.comap_mono h) ?_
  intro P Q h
  apply PrimeSpectrum.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := I.map
    (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
  apply PrimeSpectrum.localization_comap_injective _ (RingHom.ker (eval q)).primeCompl
  exact h

theorem le_comap_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    I ≤ (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal := by
  intro x hx
  have h0 : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q)))))
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hx)
  change algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x ∈ P.asIdeal
  rw [show algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x = 0 from h0]
  exact P.asIdeal.zero_mem

theorem comap_curveLocalRing_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal ≤
      RingHom.ker (eval q) := by
  intro x hx
  by_contra h
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
    (isUnit_algebraMap_curveLocalRing I q x fun h' ↦ h (RingHom.mem_ker.2 h')))

theorem LocalDimComponentBound.proof : LocalDimComponentBound.Statement := by
  intro n I q hq
  rcases subsingleton_or_nontrivial (curveLocalRing I q) with hO | hO
  · refine ⟨RingHom.ker (eval q), inferInstance, fun x hx ↦ RingHom.mem_ker.2 (hq x hx),
      fun x hx ↦ RingHom.mem_ker.1 hx, ?_⟩
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set f := algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)
  set p := LTSeries.longestOf (PrimeSpectrum (curveLocalRing I q))
  set W := (PrimeSpectrum.comap f p.head).asIdeal with hW
  have hWle : ∀ i, W ≤ (PrimeSpectrum.comap f (p i)).asIdeal := fun i ↦
    Ideal.comap_mono (p.monotone (Fin.zero_le i))
  let p' : LTSeries (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) W) :=
    { length := p.length
      toFun := fun i ↦ ⟨PrimeSpectrum.comap f (p i), hWle i⟩
      step := fun i ↦ comap_curveLocalRing_strictMono I q (p.step i) }
  refine ⟨W, (PrimeSpectrum.comap f p.head).isPrime, le_comap_curveLocalRing I q _,
    fun x hx ↦ RingHom.mem_ker.1 (comap_curveLocalRing_le I q _ hx), ?_⟩
  rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder, ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim p'

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceOnComponent

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] (hR : ringKrullDim R = 1) {p : Ideal R} (hp : p ∈ minimalPrimes R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = p) : ringKrullDim S = 1 := by
  have hpp : p.IsPrime := hp.1.1
  refine le_antisymm (hR ▸ ringKrullDim_le_of_surjective φ hφ) ?_
  obtain ⟨x, y, hxy⟩ := Order.one_le_krullDim_iff.1 (le_of_eq hR.symm : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
  have hxm : x.asIdeal < IsLocalRing.maximalIdeal R :=
    lt_of_lt_of_le hxy (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)
  have hpm : p < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top) fun h ↦ ?_
    have hpx : p ≤ x.asIdeal := hp.2 ⟨x.isPrime, bot_le⟩ (h ▸ hxm.le)
    exact (lt_of_le_of_lt hpx hxm).ne h
  have hk : ∀ K : Ideal R, p ≤ K → (K.map φ).comap φ = K := fun K hK ↦ by
    rw [Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.2 hK]
  have h0 : (p.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hker.le
  have h1 : ((IsLocalRing.maximalIdeal R).map φ).IsPrime :=
    Ideal.map_isPrime_of_surjective hφ (hker.le.trans hpm.le)
  refine Order.one_le_krullDim_iff.2 ⟨⟨_, h0⟩, ⟨_, h1⟩, ?_⟩
  change p.map φ < (IsLocalRing.maximalIdeal R).map φ
  refine lt_of_le_of_ne (Ideal.map_mono hpm.le) fun h ↦ hpm.ne ?_
  rw [← hk p le_rfl, h, hk _ hpm.le]

theorem PlaceOnComponent.proof (h₁ : ReducedNormalisationPlace.Statement)
    (h₂ : CurveMinimalPrimeQuotient.Statement) : PlaceOnComponent.Statement := by
  intro n I q hrad hdim P
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  have : Nontrivial (curveLocalRing I q) := by
    refine not_subsingleton_iff_nontrivial.1 fun h ↦ ?_
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨p, hp, hS⟩ := h₁ (curveLocalRing I q) P
  obtain ⟨J, hJ, hJq, φ, hφ, hker, hφf⟩ := h₂ n I q p hp
  obtain ⟨P', hP'⟩ := hS (curveLocalRing J q) φ hφ hker
  refine ⟨J, hJ, hJq, ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes hdim hp φ hφ hker, P', fun f ↦ ?_⟩
  have e := hP' (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)
  rw [hφf] at e
  exact e

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroDimIsolated

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem ZeroDimIsolated.proof : ZeroDimIsolated.Statement := by
  intro n I q hdim
  classical
  have : Ring.KrullDimLE 0 (curveLocalRing I q) := Ring.krullDimLE_iff.2 (by simpa using hdim)
  have hnil : ∀ i : Fin n, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧
      ∃ k : ℕ, s * (X i - C (q i)) ^ k ∈ I := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i - C (q i)) ∈
        Ring.jacobson (curveLocalRing I q) := by
      rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
      intro P hP
      have hP' : Ideal.IsMaximal P := hP
      let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
      have hPm : (Ideal.comap π P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective (H := hP')
      have hL : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
          (X i - C (q i)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q))) := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker (eval q))]
        simp [RingHom.mem_ker]
      rw [← IsLocalRing.eq_maximalIdeal hPm] at hL
      exact hL
    rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero, mem_nilradical] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [← map_pow] at hk
    have hmap : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
        ((X i - C (q i)) ^ k) ∈
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hk
    obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) I _).1 hmap
    exact ⟨m, fun h ↦ hm (RingHom.mem_ker.2 h), k, hmI⟩
  choose s hs k hk using hnil
  refine ⟨{x | eval x (∏ i, s i) ≠ 0}, ?_, ?_⟩
  · apply (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).mem_nhds
    simp [map_prod, Finset.prod_ne_zero_iff, hs]
  · rintro x ⟨hxZ, hxN⟩
    simp only [Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff] at hxN
    rw [Set.mem_singleton_iff]
    funext i
    have h := hxZ _ (hk i)
    simp only [map_mul, map_pow, map_sub, eval_X, eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (hxN i (Finset.mem_univ i))
    · exact sub_eq_zero.1 h

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds

section

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.LogIntegrable : GroundTheory.Heights₂.Heights.LogIntegrable.Statement :=
  @GroundTheory.Heights₂.Heights.LogIntegrable.proof GroundTheory.Heights₂.Heights.SheetSumMeasurable.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompare GroundTheory.Heights₂.Heights.VarSlabMeasure.full GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.MassFinite

theorem GroundTheory.Heights₂.Heights.AutoClose.VarIntAdd : GroundTheory.Heights₂.Heights.VarIntAdd.Statement :=
  @GroundTheory.Heights₂.Heights.VarIntAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.BranchGermDimOne : GroundTheory.Heights₂.Heights.BranchGermDimOne.Statement :=
  @GroundTheory.Heights₂.Heights.BranchGermDimOne.proof GroundTheory.Heights₂.Heights.LocalDimComponentBound.proof GroundTheory.Heights₂.Heights.ZeroDimIsolated.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.full

theorem GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound : GroundTheory.Heights₂.Heights.DominantFibreBound.Statement :=
  @GroundTheory.Heights₂.Heights.DominantFibreBound.proof GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.full

theorem GroundTheory.Heights₂.Heights.AutoClose.branchFillDimension_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.centredDiscCoverCurve_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredDiscCoverCurve.proof GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PuncturedCoverCycles.full

theorem GroundTheory.Heights₂.Heights.AutoClose.PlaceOnComponent : GroundTheory.Heights₂.Heights.PlaceOnComponent.Statement :=
  @GroundTheory.Heights₂.Heights.PlaceOnComponent.proof GroundTheory.Heights₂.Heights.ReducedNormalisationPlace.proof GroundTheory.Heights₂.Heights.CurveMinimalPrimeQuotient.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.DiscriminantSheetCover : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement :=
  @GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ComplexSets.DiscriminantCover

theorem GroundTheory.Heights₂.Heights.AutoClose.LelongLimitOffZero : GroundTheory.Heights₂.Heights.LelongLimitOffZero.Statement :=
  @GroundTheory.Heights₂.Heights.LelongLimitOffZero.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact

theorem GroundTheory.Heights₂.Heights.AutoClose.VarMassNearSmall : GroundTheory.Heights₂.Heights.VarMassNearSmall.Statement :=
  @GroundTheory.Heights₂.Heights.VarMassNearSmall.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact
end
end
