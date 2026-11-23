module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LaurentCechNerveLevelSpecTensorPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogCoveringFormsStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogNonvanishingRatioStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogRatioInductionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelevantPrimeOverMultihomogStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HomogeneousPairComponent

section

@[expose] public section

open MvPolynomial

namespace PositivityTheory.Xgn.HomogeneousComponentProduct

theorem comp_mul {σ M R : Type*} [CommRing R] [AddCancelCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (b : M)
    (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w (b + bg) (s * g) = weightedHomogeneousComponent w b s * g := by
  conv_lhs => rw [s.as_sum, Finset.sum_mul]
  conv_rhs => rw [s.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hm : IsWeightedHomogeneous w (monomial d (AddMonoidAlgebra.coeff s d)) (Finsupp.weight w d) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  by_cases h : Finsupp.weight w d = b
  · subst h
    rw [(hm.mul hg).weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]
  · rw [(hm.mul hg).weightedHomogeneousComponent_ne _ (fun h' => h (add_right_cancel h').symm),
      hm.weightedHomogeneousComponent_ne _ (Ne.symm h), zero_mul]

theorem comp_mul_zero {σ M R : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (c : M)
    (hc : ∀ b, c ≠ b + bg) (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w c (s * g) = 0 := by

  rw [s.as_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  exact ((isWeightedHomogeneous_monomial _ _ _ rfl).mul hg).weightedHomogeneousComponent_ne _ (hc _)

end PositivityTheory.Xgn.HomogeneousComponentProduct

theorem PositivityTheory.Xgn.homogeneous_pair_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P := by
  intro K _ _ ι _ P hP hH f g u₀ v₀ bf bg a hf hg hfP hrel hu
  have h := hH _ hrel (a + bf)
  rw [map_sub, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ f bf hf] at h
  by_cases hb : ∃ b, a + bf = b + bg
  · obtain ⟨b, hb⟩ := hb
    rw [hb, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ g bg hg] at h
    exact ⟨b, _, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hb, h⟩
  · rw [PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul_zero _ g bg hg _
      (fun b hb' => hb ⟨b, hb'⟩), sub_zero] at h
    rcases hP.mem_or_mem h with h | h
    · exact absurd h hu
    · exact absurd h hfP
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogComponentQuotient

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo

theorem multihomog_component_relation : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P :=
  @PositivityTheory.Xgn.homogeneous_pair_component

end GlobalTheory.CompanionTheory.Ggeo
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogComponentQuotientStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.multihomog_component_quotient : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.multihomog_component_relation | exact GlobalTheory.CompanionTheory.Ggeo.multihomog_component_relation | (intros; apply GlobalTheory.CompanionTheory.Ggeo.multihomog_component_relation <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogIdealEquivalence

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo.CompMem

theorem blockWeight_weight_apply {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  · intro b _ hb
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_eq_of_ne hb.symm]
  · simp

theorem comp_mem : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  intro K _ _ ι _ P hP f hf b
  obtain ⟨S, hS, rfl⟩ := hP
  classical
  letI := weightedGradedAlgebra ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι)
  refine weightedHomogeneousComponent_mem_of_mem ℤ _ ?_ hf b
  refine Ideal.homogeneous_span _ S fun g hg => ?_
  obtain ⟨a, ha⟩ := hS g hg
  refine ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 fun m hm => ?_⟩
  funext k
  rw [blockWeight_weight_apply]
  exact ha m (mem_support_iff.2 hm) k

end GlobalTheory.CompanionTheory.Ggeo.CompMem
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogIdealEquivalenceStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.isMultiHomogIdeal_transfer : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem | exact GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem | (intros; apply GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsometricHermLine

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem twist_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A : HermLine ι, A.a = T.x () → IsSmoothHerm A → IsConjInvariantH A → ∃ A' : HermLine ι, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ T.IsIsometric P (fun _ => A) (fun _ => A') := by
  intro K _ _ ι _ P D hP S T hT A hAx hAs hAc
  obtain ⟨_, ⟨hPp, hPh, _⟩, _, _⟩ := hP
  have hPh' := GlobalTheory.T.isMultiHomogIdeal_transfer K ι P hPh
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hW⟩ := hT ()
  generalize hfd : T.f () = f at *
  generalize hgd : T.g () = g at *
  let Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop :=
    fun a b u v => GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u * f - v * g ∈ P
  have hQmul : ∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m) := by
    rintro a b d u v m ⟨hu, hv, hab, hr⟩ hm
    refine ⟨hu.mul hm, hv.mul hm, ?_, ?_⟩
    · rw [add_right_comm, hab, add_right_comm]
    · have : u * m * f - v * m * g = m * (u * f - v * g) := by ring
      rw [this]
      exact P.mul_mem_left _ hr
  have hcompP : ∀ z ∈ mcPts P, ∀ (a : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℤ),
      eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 → s ∉ P := fun z hz _ s hs hm =>
    hs (hz.2 s hm)
  have hin : ∀ z ∈ mcPts P, (∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) ∧
      (∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) := by
    intro z hz
    obtain ⟨W, hWp, hPW, hWr, hWc, hWs⟩ := GlobalTheory.T.relevant_prime_over_multihomog K ι P z hPh' hz
    obtain ⟨u₀, v₀, hu₀, hv₀, hr⟩ := hW W hWp hPW hWr (fun p _ => hWc p)
    constructor
    · obtain ⟨a, ha⟩ := hWs u₀ hu₀
      obtain ⟨b, v, hv, hab, hr'⟩ := GlobalTheory.T.multihomog_component_quotient K ι P hPp hPh' f g u₀ v₀ bf bg a hf hg hfP hr
        (hcompP z hz a _ ha)
      exact ⟨a, b, _, v, ⟨weightedHomogeneousComponent_isWeightedHomogeneous a u₀, hv, hab, hr'⟩, ha⟩
    · obtain ⟨b, hb⟩ := hWs v₀ hv₀
      have hr₂ : v₀ * g - u₀ * f ∈ P := by
        have := P.neg_mem hr
        rwa [neg_sub] at this
      obtain ⟨a, u, hu, hab, hr'⟩ := GlobalTheory.T.multihomog_component_quotient K ι P hPp hPh' g f v₀ u₀ bg bf b hg hf hgP hr₂
        (hcompP z hz b _ hb)
      refine ⟨a, b, u, _, ⟨hu, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hab.symm, ?_⟩, hb⟩
      have := P.neg_mem hr'
      rwa [neg_sub] at this
  have hout : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → z ∉ mcPts P →
      ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
    intro z hc hz
    have : ∃ q ∈ P, eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hz ⟨hc, hne⟩
    obtain ⟨q, hq, hqz⟩ := this
    obtain ⟨a, b, u, v, hu, hv, hab, huP, hvP, huz, hvz⟩ := GlobalTheory.T.multihomog_nonvanishing_ratio K ι P bf bg z q hPh' hc hq hqz
    refine ⟨a, b, u, v, ⟨hu, hv, hab, ?_⟩, huz, hvz⟩
    exact P.sub_mem (P.mul_mem_right _ huP) (P.mul_mem_right _ hvP)
  obtain ⟨Aₐ, B, n, u, v, hAB, hQ, hu, hv⟩ := GlobalTheory.T.multihomog_ratio_induction K ι Q bf bg hQmul (fun a b u v h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun z hc => by
      by_cases hz : z ∈ mcPts P
      · exact (hin z hz).1
      · obtain ⟨a, b, u, v, h, h1, _⟩ := hout z hc hz
        exact ⟨a, b, u, v, h, h1⟩)
    (fun z hc => by
      by_cases hz : z ∈ mcPts P
      · exact (hin z hz).2
      · obtain ⟨a, b, u, v, h, _, h1⟩ := hout z hc hz
        exact ⟨a, b, u, v, h, h1⟩)
  obtain ⟨A', ha', hs', hc', hh'⟩ := GlobalTheory.T.multihomog_covering_forms K ι A Aₐ B n u v (fun j => (hQ j).1) (fun j => (hQ j).2.1)
    hu hv hAs hAc
  refine ⟨A', hs', hc', fun _ => ⟨hAx, ?_, fun z hz => ?_⟩⟩
  · rw [ha', hAx]
    funext k
    have h1 := congrFun hdeg k
    have h2 : (Aₐ k : ℤ) + bf k = B k + bg k := by exact_mod_cast congrFun hAB k
    simp only [Pi.sub_apply] at h1
    linarith
  · show ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.f ()))‖ * A'.h z =
      ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.g ()))‖ * A.h z
    rw [hfd, hgd, hh']
    set fz := eval z (MvPolynomial.map (Int.castRingHom ℂ) f)
    set gz := eval z (MvPolynomial.map (Int.castRingHom ℂ) g)
    have hrel : ∀ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 * ‖fz‖ ^ 2 =
        ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2 * ‖gz‖ ^ 2 := by
      intro j
      have h0 := hz.2 _ (hQ j).2.2.2
      simp only [map_sub, map_mul] at h0
      have h1 := sub_eq_zero.mp h0
      have h2 := congrArg norm h1
      rw [norm_mul, norm_mul] at h2
      rw [← mul_pow, ← mul_pow, h2]
    have hD : 0 < ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2 := by
      obtain ⟨j, hj⟩ := hv z hz.1
      exact Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, by positivity⟩
    have hsum : (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) * ‖fz‖ ^ 2 =
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2) * ‖gz‖ ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => hrel j
    have key : ‖fz‖ * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) = ‖gz‖ := by
      rw [← Real.sqrt_sq (norm_nonneg fz), ← Real.sqrt_mul (by positivity)]
      rw [show ‖fz‖ ^ 2 * ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) = ‖gz‖ ^ 2 by
        field_simp
        linarith]
      exact Real.sqrt_sq (norm_nonneg gz)
    calc ‖fz‖ * (A.h z * _) = (‖fz‖ * Real.sqrt _) * A.h z := by ring
      _ = ‖gz‖ * A.h z := by rw [key]

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsometricHermLineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

theorem _root_.GlobalTheory.T.exists_isometric_herm_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A : HermLine ι, A.a = T.x () → IsSmoothHerm A → IsConjInvariantH A → ∃ A' : HermLine ι, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ T.IsIsometric P (fun _ => A) (fun _ => A') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.twist_line | exact GlobalTheory.CompanionTheory.Ar.Num.twist_line | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.twist_line <;> assumption)
end
end
