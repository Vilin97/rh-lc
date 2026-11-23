module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsQuaternionNormOneReEq
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionNormOneNearReSqNeOneStatement
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenPiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenProdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZeroStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZeroStatement
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsQuaternionNormOneReEqStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.eventually_exists_quaternion_norm_one_re_eq : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq | exact GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq | (intros; apply GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBot

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory.QSA

theorem infinitePlace_completion_nhdsNE_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  intro F _ _ w
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  have h2 : ‖(2 : w.Completion)‖ = 2 := by
    have := (AddMonoidHomClass.isometry_iff_norm _).1 hiso (2 : w.Completion)
    rw [← this, map_ofNat]; simp
  letI : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by rw [h2]; norm_num⟩ }
  exact NormedField.nhdsNE_neBot (0 : w.Completion)
end GlobalTheory.QSA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBotStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  first | exact @GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | exact GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | (intros; apply GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneReOpenNearOfIsUnit

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

theorem traceOpen_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro R _ _ _ a b hsq g hg hu W hW
  set s := g.re with hs
  let φ : R × R → ℍ[R, a, b] := fun p => ⟨p.1, p.2 * g.imI, p.2 * g.imJ, p.2 * g.imK⟩
  have hφ : Continuous φ := by
    apply continuous_induced_rng.2
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [coords, φ] using continuous_fst
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
  have hφs : φ (s, 1) = g := by ext <;> simp [φ, s]
  have hpre : φ ⁻¹' W ∈ 𝓝 (s, (1 : R)) := hφ.continuousAt.preimage_mem_nhds (by rw [hφs]; exact hW)
  obtain ⟨O₀, hO₀, V, hV, hOV⟩ := mem_nhds_prod_iff.1 hpre
  obtain ⟨U, hU, hUV⟩ := hsq V hV
  set c : R := ((hu.unit⁻¹ : Rˣ) : R) with hc_def
  have hc : c * (1 - s ^ 2) = 1 := by
    rw [hc_def]
    have := hu.unit.inv_mul
    simpa using this
  let r : R → R := fun t => (1 - t ^ 2) * c
  have hr : Continuous r := (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
  have hrs : r s = 1 := by simp only [r]; rw [mul_comm]; exact hc
  refine ⟨interior (O₀ ∩ r ⁻¹' U), isOpen_interior, ?_, ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hO₀ ?_
    exact hr.continuousAt.preimage_mem_nhds (by rw [hrs]; exact hU)
  · intro t ht
    have ht' := interior_subset ht
    obtain ⟨μ, hμV, hμ⟩ := hUV (r t) ht'.2
    refine ⟨φ (t, μ), hOV (Set.mk_mem_prod ht'.1 hμV), ?_, rfl⟩
    have hμ' : μ ^ 2 = (1 - t ^ 2) * c := hμ
    simp only [nrm, φ] at hg ⊢
    linear_combination μ ^ 2 * hg + (1 - s ^ 2) * hμ' + (1 - t ^ 2) * hc

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneReOpenNearOfIsUnitStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.quaternion_normOne_re_open_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  first | exact @GlobalTheory.traceOpen_near_of_isUnit | exact GlobalTheory.traceOpen_near_of_isUnit | (intros; apply GlobalTheory.traceOpen_near_of_isUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenFiniteAdeleRingStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_finiteAdeleRing : ∀ (F : Type) [Field F] [NumberField F] (a b : F), (∀ v : HeightOneSpectrum (𝓞 F), TraceOpen (v.adicCompletion F) (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b)) → (∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F) → TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by
  first | exact @GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele | exact GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele | (intros; apply GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneAdicCompletionNumberField

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

noncomputable section

namespace GlobalTheory.QSA

theorem sqOpen_and_nhdsNE_zero_neBot_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  intro F _ _ v
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    intro h
    have h' : algebraMap F (v.adicCompletion F) 2 = algebraMap F (v.adicCompletion F) 0 := by
      rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero ((algebraMap F (v.adicCompletion F)).injective h')
  refine ⟨GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero (v.adicCompletion F) h2, ?_⟩
  infer_instance

end GlobalTheory.QSA

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneAdicCompletionNumberFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  first | exact @GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | exact GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | (intros; apply GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenAdeles

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem traceOpen_field (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
    (h2 : (2 : K) ≠ 0) (hnb : (𝓝[≠] (0 : K)).NeBot) (hsq : SqOpen K) (a b : K) (ha : a ≠ 0) : TraceOpen K a b := by
  intro g hg W hW
  obtain ⟨g', hg'1, hg're, hW'⟩ := GlobalTheory.T.exists_quaternion_normOne_near_re_sq_ne_one K h2 hnb a b ha g hg W hW
  have hu : IsUnit (1 - g'.re ^ 2) := IsUnit.mk0 _ (sub_ne_zero.2 (Ne.symm hg're))
  obtain ⟨O, hO, hmem, hO'⟩ := GlobalTheory.T.quaternion_normOne_re_open_near_of_isUnit K a b hsq g' hg'1 hu W hW'
  exact ⟨O, hO, ⟨_, hmem⟩, hO'⟩

theorem traceOpen_inf (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) :
    TraceOpen (InfiniteAdeleRing F) (algebraMap F (InfiniteAdeleRing F) a) (algebraMap F (InfiniteAdeleRing F) b) := by
  refine GlobalTheory.T.quaternionNormOneTraceOpen_pi (InfinitePlace F) (fun w => w.Completion) _ _ (fun w => ?_)
  have h2 : (2 : w.Completion) ≠ 0 := by
    have := (map_ne_zero (algebraMap F w.Completion)).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  exact traceOpen_field _ h2 (GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot F w) (GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero _ h2) _ _ ((map_ne_zero (algebraMap F w.Completion)).2 ha)

theorem traceOpen_fin (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a)
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by
  refine GlobalTheory.T.quaternionNormOneTraceOpen_finiteAdeleRing F a b (fun v => ?_) (GlobalTheory.T.eventually_exists_quaternion_norm_one_re_eq F a b ha hb)
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have := (map_ne_zero (algebraMap F (v.adicCompletion F))).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  exact traceOpen_field _ h2 (GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField F v).2 (GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField F v).1 _ _ ((map_ne_zero (algebraMap F _)).2 ha)

theorem traceOpen_adele : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ g : DA F a b, nrm g = 1 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ O : Set (AF F), IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro F _ _ a b ha hb g hg W hW
  have H : TraceOpen (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b) :=
    GlobalTheory.T.quaternionNormOneTraceOpen_prod _ _ _ _ _ _ (traceOpen_inf F a b ha) (traceOpen_fin F a b ha hb)
  exact H g hg W hW
end GlobalTheory.QSA
end
end
