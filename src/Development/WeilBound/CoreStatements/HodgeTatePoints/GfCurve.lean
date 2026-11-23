module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

-- Source module: GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open MvPolynomial NumbersDVR

noncomputable section

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type} [Field F]

theorem exists_forms_mem_of_not_le_relevant {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    (hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W → ¬ J ≤ W) :
    ∃ n : ℕ, ∀ m : K → ℕ, (∀ k, n * Fintype.card (ι k) < m k) →
      ∀ x : MRing ι F, IsMultiHomog x m → x ∈ J := by
  classical

  let e : (∀ k, ι k) → (Σ k, ι k) →₀ ℕ := fun σ =>
    Finsupp.equivFunOnFinite.symm (fun v => if v.2 = σ v.1 then 1 else 0)
  have he : ∀ σ v, e σ v = if v.2 = σ v.1 then 1 else 0 := fun σ v => rfl
  have hrad : ∀ σ : (∀ k, ι k), (monomial (e σ) (1 : F)) ∈ J.radical := by
    intro σ
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro W hW
    have hWp : Ideal.IsPrime W := hW.1.1
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof F K ι J W hJ hW
    obtain ⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ W := by
      by_contra h
      push Not at h
      exact hrel W hWp hWh h hW.1.2
    refine Ideal.mem_of_dvd _ ?_ (hk (σ k))
    rw [← pow_one (X _), X_pow_eq_monomial, monomial_dvd_monomial]
    refine ⟨Or.inr ?_, one_dvd _⟩
    rw [Finsupp.single_le_iff, he]
    simp
  have hrad' : ∀ σ : (∀ k, ι k), ∃ n : ℕ, (monomial (e σ) (1 : F)) ^ n ∈ J := fun σ => hrad σ
  choose N hN using hrad'
  refine ⟨Finset.univ.sup N, fun m hm x hx => ?_⟩
  rw [x.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hw := hx (mem_support_iff.mp hd)
  rw [Bridge.weight_blockWeight] at hw
  have hσ : ∀ k, ∃ i : ι k, Finset.univ.sup N ≤ d ⟨k, i⟩ := by
    intro k
    by_contra h
    push Not at h
    have h1 : ∑ i, d ⟨k, i⟩ ≤ ∑ _i : ι k, Finset.univ.sup N :=
      Finset.sum_le_sum fun i _ => (h i).le
    have h2 := congrFun hw k
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1 h2
    have h3 := hm k
    rw [h2] at h1
    rw [mul_comm] at h3
    omega
  choose σ hσ using hσ
  have hmem : monomial (e σ) (1 : F) ^ Finset.univ.sup N ∈ J :=
    Ideal.pow_mem_of_pow_mem _ (hN σ) (Finset.le_sup (Finset.mem_univ σ))
  refine Ideal.mem_of_dvd _ ?_ hmem
  rw [monomial_pow, one_pow, monomial_dvd_monomial]
  refine ⟨Or.inr ?_, one_dvd _⟩
  intro v
  rw [Finsupp.smul_apply, he, smul_eq_mul]
  split_ifs with hv
  · obtain ⟨k, i⟩ := v
    simp only at hv
    subst hv
    simpa using hσ k
  · simp

theorem hilbFn_sub_le_of_regular {P : Ideal (MRing ι F)} (hP : IsMultiProjPrime P) {b : K → ℤ}
    {f g : MRing ι F} (hs : IsRegularSection P b f g) :
    ∀ᶠ m in Filter.atTop, hilbFn P (m - b) ≤ hilbFn P m := by
  classical
  have := hP.isPrime
  obtain ⟨bf, bg, hf, hg, hb⟩ := hs.degrees
  set J : Ideal (MRing ι F) := (P ⊔ Ideal.span {g}).colon {f} with hJdef
  have hJh : IsMultiHomogIdeal J :=
    ColonMultiHomog.proof F K ι _ f bf
      (SupSpanMultiHomog.proof F K ι P g bg hP.multiHomog hg) hf
  have hPJ : P ≤ J := fun p hp => by
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    exact Ideal.mem_sup_left (P.mul_mem_right f hp)
  have hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W →
      ¬ J ≤ W := by
    intro W hWp hWh hWr hJW
    obtain ⟨u, v, hu, huv⟩ := hs.regular W ⟨hWp, hWh, hWr⟩ (hPJ.trans hJW)
    apply hu
    apply hJW
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    have : u * f = (u * f - v * g) + v * g := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left huv)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  obtain ⟨n, hn⟩ := exists_forms_mem_of_not_le_relevant hJh hrel
  rw [Filter.eventually_atTop]
  refine ⟨fun k => |b k| + (n * Fintype.card (ι k) : ℕ) + 1, fun m hm => ?_⟩
  have hm' : ∀ k, |b k| + (n * Fintype.card (ι k) : ℕ) + 1 ≤ m k := fun k => hm k
  have hb' : ∀ k, b k = (bf k : ℤ) - bg k := fun k => (congrFun hb k).symm
  have hm0 : ∀ k, 0 ≤ m k := fun k => by have := hm' k; have := abs_nonneg (b k); omega
  have hmb0 : ∀ k, 0 ≤ (m - b) k := fun k => by
    have := hm' k; have := le_abs_self (b k); simp only [Pi.sub_apply]; omega
  set M : K → ℕ := fun k => (m k).toNat with hM
  set M' : K → ℕ := fun k => ((m - b) k).toNat with hM'
  have hdeg : M' + bf = M + bg := by
    funext k
    have := hm0 k; have := hmb0 k; have := hb' k
    simp only [Pi.add_apply, hM, hM', Pi.sub_apply] at *
    omega
  have hbig : ∀ k, n * Fintype.card (ι k) < M' k := by
    intro k
    have := hm' k; have := le_abs_self (b k)
    simp only [hM', Pi.sub_apply]
    omega
  have hfin := (FieldNumbers.GradedFinite.proof F K ι P M).1
  have hfin' := (FieldNumbers.GradedFinite.proof F K ι P M').1
  have e1 : hilbFn P m = Module.finrank F (gradedPiece P M) := by
    unfold hilbFn; rw [if_pos hm0]
  have e2 : hilbFn P (m - b) = Module.finrank F (gradedPiece P M') := by
    unfold hilbFn; rw [if_pos hmb0]
  rw [e1, e2, Nat.cast_le]

  let φ : MRing ι F → (MRing ι F ⧸ P) →ₗ[F] (MRing ι F ⧸ P) := fun a =>
    LinearMap.mulLeft F (Ideal.Quotient.mk P a)
  have hinj : ∀ a, a ∉ P → Function.Injective (φ a) := by
    intro a ha
    exact mul_right_injective₀ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hle : (gradedPiece P M').map (φ f) ≤ (gradedPiece P M).map (φ g) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxh : IsMultiHomog x M' := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx
    have hxJ : x ∈ J := hn M' hbig x hxh
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_sup] at hxJ
    obtain ⟨p, hp, q, hq, hpq⟩ := hxJ
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    set y := weightedHomogeneousComponent (blockWeight ι) M a
    have hxf : IsMultiHomog (x * f) (M + bg) := by
      rw [← hdeg]; exact hxh.mul hf
    have hcomp := congrArg (weightedHomogeneousComponent (blockWeight ι) (M + bg)) hpq
    rw [map_add (f := _), ← component_mul_multiHomog a g M bg hg,
      hxf.weightedHomogeneousComponent_same] at hcomp
    have hpc : weightedHomogeneousComponent (blockWeight ι) (M + bg) p ∈ P :=
      hP.multiHomog p hp _
    refine ⟨Ideal.Quotient.mk P y, ⟨y, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      rfl⟩, ?_⟩
    simp only [φ, LinearMap.mulLeft_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.toLinearMap_apply,
      ← map_mul]
    rw [Ideal.Quotient.eq, mul_comm f x, ← hcomp]
    have : g * y - (weightedHomogeneousComponent (blockWeight ι) (M + bg) p + y * g) =
      -weightedHomogeneousComponent (blockWeight ι) (M + bg) p := by ring
    rw [this]
    exact P.neg_mem hpc
  calc Module.finrank F (gradedPiece P M')
      = Module.finrank F ((gradedPiece P M').map (φ f)) :=
        (Submodule.equivMapOfInjective _ (hinj f hs.num_not_mem) _).finrank_eq
    _ ≤ Module.finrank F ((gradedPiece P M).map (φ g)) := by
        have : FiniteDimensional F ((gradedPiece P M).map (φ g)) :=
          Module.Finite.map _ _
        exact LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
          (Submodule.inclusion_injective hle)
    _ = Module.finrank F (gradedPiece P M) :=
        ((Submodule.equivMapOfInjective _ (hinj g hs.den_not_mem) _).finrank_eq).symm

end

theorem SectionNef.proof : SectionNef.Statement := by
  intro K _ _ ι _ F _ P hP _ b f g hs
  have hev := hilbFn_sub_le_of_regular hP hs
  unfold intNum eventualValue
  split_ifs with h
  · obtain ⟨m, hm1, hm2⟩ := (h.choose_spec.and hev).exists
    rw [← hm1]
    simp only [mixedDiff, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      Matrix.cons_val_zero, diffStep]
    linarith
  · exact le_rfl

end

end GroundTheory.Heights₂.Heights.Model
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.GeoNumNonnegOfRegular

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Bridge.GeoNum (red red_surjective ker_red comap_map_eq quotEquiv)

namespace PositivityTheory.HtPt.Gf

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem geoNum_nonneg_of_regular (p : ℕ) [Fact p.Prime] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hp : (p : MRing J) ∈ W) (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {f g : MRing J} {bf bg : K → ℕ} {a : K → ℤ} (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (ha : ∀ k, (bf k : ℤ) - bg k = a k) (hfW : f ∉ W) (hgW : g ∉ W)
    (hreg : ∀ t : ∀ k, J k, (∀ k, (X ⟨k, t k⟩ : MRing J) ∉ W) → ∃ (n : ℕ) (c : K → ℕ) (v : MRing J),
      ¬ p ∣ n ∧ n * mon t c * f - v * g ∈ W) : 0 ≤ geoNum 1 W (fun _ => a) := by
  classical
  have hC : (MvPolynomial.C (p : ℤ) : MRing J) ∈ W := by
    simpa [map_natCast] using hp
  have hker : RingHom.ker (red (ι := J) p) ≤ W := by
    rw [ker_red]
    exact (Ideal.span_le).2 (by simpa using hC)
  set P := Ideal.map (red (ι := J) p) W with hPdef
  have hcomap : Ideal.comap (red (ι := J) p) P = W := comap_map_eq p hker
  have hWp : W.IsPrime := hW.1
  have hPprime : P.IsPrime := Ideal.map_isPrime_of_surjective (red_surjective p) hker
  have hsupp : ∀ h : MRing J, ∀ b : K → ℕ, IsMultiHomog h b →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (red (ι := J) p h) b := by
    intro h b hh
    rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff]
    intro m hm k
    exact hh m (MvPolynomial.support_map_subset _ _ hm) k
  have hPhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
    rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, rfl⟩ := hW.2.1
    refine ⟨(red (ι := J) p) '' S, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨b, hb⟩ := hS h hh
      exact ⟨b, (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 (hsupp h b hb)⟩
    · rw [hPdef, Ideal.map_span]
  have hPrel : GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant P := by
    rw [← GroundTheory.Heights₂.Heights.Bridge.GeoNum.isRelevant_comap_iff p P, hcomap]
    exact hW.2.2
  have hPm : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime P := ⟨hPprime, hPhom, hPrel⟩
  have hdimP : ringKrullDim (GroundTheory.Heights₂.Heights.NumbersDVR.MRing J (ZMod p) ⧸ P) =
      ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hdim, ← ringKrullDim_eq_of_ringEquiv (quotEquiv p P), hcomap]
  have hreg' : GroundTheory.Heights₂.Heights.Model.IsRegularSection P a (red (ι := J) p f) (red (ι := J) p g) := by
    refine ⟨⟨bf, bg, hsupp f bf hf, hsupp g bg hg, funext ha⟩, ?_, ?_, ?_⟩
    · intro hm
      exact hfW (by rw [← hcomap]; exact hm)
    · intro hm
      exact hgW (by rw [← hcomap]; exact hm)
    · intro W' hW' hPW'
      set W'' := Ideal.comap (red (ι := J) p) W'
      have hW'pr : W'.IsPrime := hW'.1
      have hW''pr : W''.IsPrime := Ideal.comap_isPrime _ _
      have hWW'' : W ≤ W'' := by
        rw [← hcomap]
        exact Ideal.comap_mono hPW'
      have hrel : IsRelevant W'' :=
        (GroundTheory.Heights₂.Heights.Bridge.GeoNum.isRelevant_comap_iff p W').2 hW'.relevant
      choose t ht using hrel
      obtain ⟨n, c, v, hn, hv⟩ := hreg t (fun k hk => ht k (hWW'' hk))
      refine ⟨red (ι := J) p ((n : MRing J) * mon t c), red (ι := J) p v, ?_, ?_⟩
      · intro hu
        have hu' : ((n : MRing J) * mon t c) ∈ W'' := hu
        rcases hW''pr.mem_or_mem hu' with h1 | h1
        · exact natCast_not_mem hW''pr.ne_top (hWW'' hp) hn h1
        · exact mon_not_mem hW''pr ht c h1
      · have := Ideal.mem_map_of_mem (red (ι := J) p) hv
        simpa [map_sub, map_mul] using this
  have key := GroundTheory.Heights₂.Heights.Model.SectionNef.proof K J (ZMod p) P hPm hdimP a
    (red (ι := J) p f) (red (ι := J) p g) hreg'
  rw [GroundTheory.Heights₂.Heights.Bridge.intNum_map_eq_geoNum p 1 W hW hC hdim] at key
  have hfun : (![a] : Fin 1 → K → ℤ) = fun _ => a := by
    funext i
    fin_cases i
    rfl
  rwa [hfun] at key

end PositivityTheory.HtPt.Gf
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.GfCurve

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem curve_sec_nef : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (W : Ideal (MRing J)) (a : K → ℤ) (r : (∀ k, J k) → Ω), IsMultiProjPrime W → mCoordIdeal y ≤ W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) → (∀ s, mseg y s ≠ 0 → r s ∈ chartRing o (mseg y) s) → (∀ s t, mseg y s ≠ 0 → mseg y t ≠ 0 → ∃ (n : ℕ) (z : Ω), z ∈ chartRing o (mseg y) t ∧ (mseg y s / mseg y t) ^ n * (r s * chartMon y s a / chartMon y t a - r t) = p * z) → (∃ (s : ∀ k, J k) (n d : ℕ) (g : MRing J), (∀ k, (X ⟨k, s k⟩ : MRing J) ∉ W) ∧ ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ g ∉ W ∧ n * r s * mseg y s ^ d = aeval y g) → 0 ≤ geoNum 1 W (fun _ => a) := by
  intro Ω _ _ K _ J _ y p _ o _ _ ho W a r hW hle hch hdim hr hov ⟨s, n, d, g, hs, hn, hg, hgW, hgy⟩
  have hp := natCast_mem_of_charOf hch
  have hP := hW.1
  have hs0 := mseg_ne_zero hle hs
  let ap : K → ℕ := fun k => (a k).toNat
  let am : K → ℕ := fun k => (-a k).toNat
  refine geoNum_nonneg_of_regular p hW hp hdim (hom_mul hg (hom_mon s ap))
    (hom_mul (hom_mon s fun _ => d) (hom_mon s am)) (fun k => ?_)
    (fun h => (hP.mem_or_mem h).elim hgW (mon_not_mem hP hs _))
    (fun h => (hP.mem_or_mem h).elim (mon_not_mem hP hs _) (mon_not_mem hP hs _)) fun t ht => ?_
  · simp only [Pi.add_apply, ap, am]
    omega
  have ht0 := mseg_ne_zero hle ht
  obtain ⟨m, z, hz, hrel⟩ := hov s t hs0 ht0
  obtain ⟨n₁, e₁, g₁, hn₁, hg₁, hy₁⟩ := exists_rep ho ht0 (hr t ht0)
  obtain ⟨n₂, e₂, g₂, hn₂, hg₂, hy₂⟩ := exists_rep ho ht0 hz
  refine ⟨n₁ * n₂, (fun _ => e₁ + e₂) + am, n * (n₂ * (g₁ * mon t (fun _ => e₂) * mon t ap)),
    fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hn₁ hn₂, ?_⟩
  have hsplit : mon t ((fun _ => e₁ + e₂) + am) = mon t (fun _ => e₁ + e₂) * mon t am := by
    simp [mon, pow_add, Finset.prod_mul_distrib]
  have hz0 : mon s (fun _ => m) * (((n₁ * n₂ : ℕ) : MRing J) * (mon t (fun _ => e₁ + e₂) * mon t am * (g * mon s ap)) -
      n * (n₂ * (g₁ * mon t (fun _ => e₂) * mon t ap * (mon s (fun _ => d) * mon s am)))) -
      p * (n * (n₁ * (g₂ * mon t (fun _ => e₁ + m) * mon s (fun _ => d) * mon s am * mon t ap))) ∈
        mCoordIdeal y := by
    refine mem_mCoordIdeal (d := fun k => m + e₁ + e₂ + d + ap k + am k) (hom_sub (hom_of_eq (hom_mul (hom_mon _ _)
      (hom_sub (hom_nat_mul _ (hom_mul (hom_mul (hom_mon _ _) (hom_mon _ _)) (hom_mul hg (hom_mon _ _))))
        (hom_nat_mul _ (hom_nat_mul _ (hom_of_eq (hom_mul (hom_mul (hom_mul hg₁ (hom_mon _ _)) (hom_mon _ _))
          (hom_mul (hom_mon _ _) (hom_mon _ _))) fun k => ?_))))) fun k => ?_)
      (hom_nat_mul _ (hom_nat_mul _ (hom_nat_mul _ (hom_of_eq (hom_mul (hom_mul (hom_mul (hom_mul hg₂ (hom_mon _ _))
        (hom_mon _ _)) (hom_mon _ _)) (hom_mon _ _)) fun k => ?_))))) ?_
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.add_apply]; omega
    rw [chartMon_eq_div hs0, chartMon_eq_div ht0] at hrel
    have hne : ∀ {u : ∀ k, J k}, mseg y u ≠ 0 → ∀ c, aeval y (mon u c) ≠ 0 := fun hu c => by
      rw [aeval_mon]
      exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (Finset.prod_ne_zero_iff.1 hu k (Finset.mem_univ k))
    have h1 := hne hs0 am
    have h2 := hne ht0 am
    have h3 := hne ht0 ap
    simp only [map_sub, map_mul, map_natCast, aeval_mon_const, ← hgy, ← hy₁, ← hy₂]
    change (mseg y s / mseg y t) ^ m * (r s * (aeval y (mon s ap) / aeval y (mon s am)) /
      (aeval y (mon t ap) / aeval y (mon t am)) - r t) = p * z at hrel
    generalize aeval y (mon s ap) = A at *
    generalize aeval y (mon s am) = B at *
    generalize aeval y (mon t ap) = A' at *
    generalize aeval y (mon t am) = B' at *
    rw [div_pow] at hrel
    field_simp at hrel
    push_cast
    linear_combination (n * n₁ * n₂ * mseg y t ^ (e₁ + e₂) * mseg y s ^ d) * hrel
  have h1 := (Ideal.add_mem_iff_left W (W.neg_mem (W.mul_mem_right _ hp))).1 (by
    rw [← sub_eq_add_neg]; exact hle hz0)
  have h2 := (hP.mem_or_mem h1).resolve_left (mon_not_mem hP hs _)
  rw [hsplit]
  convert h2 using 1
  ring

end PositivityTheory.HtPt.Gf
end
end
