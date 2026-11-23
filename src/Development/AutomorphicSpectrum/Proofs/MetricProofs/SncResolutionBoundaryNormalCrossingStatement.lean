module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSupStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRingStatement
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
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLocA
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartParametersAtConePointStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularAtConePointStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularWithBoundaryChoiceStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChartStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerInAffineChartStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UnitTimesParameterMonomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartMultihomogOrderAtPoint

section

@[expose] public section

noncomputable section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono

theorem exists_unit_mul_monomial_of_primes {m e : ℕ} (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) [hreg : IsRegularLocalRing (locRing I t)]
    (hdim : ringKrullDim (locRing I t) = e) (r : Fin e → MvPolynomial (Fin m) ℂ) (J : Finset (Fin e))
    (hspan : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t))
    (hpr : ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t →
      (Dc ≤ 𝔮 ↔ ∃ i ∈ J, r i ∈ 𝔮))
    (g : MvPolynomial (Fin m) ℂ)
    (hg : ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → g ∈ 𝔮 → Dc ≤ 𝔮) :
    ∃ (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ J → mm i = 0) ∧
      algebraMap _ (locRing I t) g = u * ∏ i ∈ J, algebraMap _ (locRing I t) (r i) ^ mm i := by
  classical
  have hdom : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  have hKt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := by
    rw [hspan, maximalIdeal_locRing hKt]
  have hdim' : (e : WithBot ℕ∞) = ringKrullDim (locRing I t) := hdim.symm
  have hprime : ∀ i, Prime (algebraMap _ (locRing I t) (r i)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim'

  have hcontr : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t))).IsPrime ∧
      I ≤ 𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) ∧
      𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) ≤ ptIdeal t := by
    intro 𝔓 h𝔓
    refine ⟨Ideal.comap_isPrime _ _, ?_, ?_⟩
    · intro h hh
      rw [Ideal.mem_comap]
      have : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hh)
      rw [this]
      exact 𝔓.zero_mem
    · intro h hh
      rw [Ideal.mem_comap] at hh
      by_contra hne
      have hne' : eval t h ≠ 0 := fun h0 => hne (RingHom.mem_ker.mpr h0)
      have hu := (IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI h).mpr hne'
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ hh hu)
  have hg0 : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) g ≠ 0 := by
    intro h0
    obtain ⟨h1, h2, h3⟩ := hcontr ⊥ Ideal.isPrime_bot
    have hgm : g ∈ (⊥ : Ideal (locRing I t)).comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) := by
      rw [Ideal.mem_comap, h0]; exact Ideal.zero_mem _
    obtain ⟨i, -, hi⟩ := (hpr _ h1 h2 h3).1 (hg _ h1 h2 h3 hgm)
    rw [Ideal.mem_comap, Ideal.mem_bot] at hi
    exact (hprime i).ne_zero hi
  have hrad : (∏ i ∈ J, algebraMap _ (locRing I t) (r i)) ∈
      (Ideal.span {algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) g}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro 𝔓 ⟨hle, h𝔓⟩
    obtain ⟨h1, h2, h3⟩ := hcontr 𝔓 h𝔓
    have hgm : g ∈ 𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) := by
      rw [Ideal.mem_comap]; exact hle (Ideal.mem_span_singleton_self _)
    obtain ⟨i, hiJ, hi⟩ := (hpr _ h1 h2 h3).1 (hg _ h1 h2 h3 hgm)
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hiJ) hi
  exact eq_unit_mul_monomial (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim' J hg0 hrad

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ideal_sup_le_of_mem (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (hP : IsMultiHomogIdeal P) (f : MvPolynomial (Σ k, ι k) ℂ)
    (hf : ∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D)
    (𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) (h𝔮 : 𝔮.IsPrime)
    (hI : SncRes.ideal P p ≤ 𝔮) (hg : bind₁ (SncRes.lift p) f ∈ 𝔮) :
    SncRes.ideal (P ⊔ D) p ≤ 𝔮 := by
  classical
  intro h hh
  have hvan : h ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
    rw [mem_vanishingIdeal_iff]
    intro w hw
    have hw0 : ∀ c ∈ 𝔮, eval w c = 0 := fun c hc => by simpa using hw c hc
    let w' : (Σ k, ι k) → ℂ := w ∘ Fintype.equivFin (Σ k, ι k)
    have hpt : renPt w' = w := by
      funext j
      simp [renPt, w']
    have hren : ∀ x, eval w (renC (Σ k, ι k) x) = eval w' x := fun x => by
      rw [← eval_renC w' x, hpt]
    have hchart : ∀ c ∈ chartIdeal P p, eval w' c = 0 := fun c hc => by
      rw [← hren]
      have hs : (renR (Σ k, ι k)).symm (renC (Σ k, ι k) c) = c := (renR (Σ k, ι k)).symm_apply_apply c
      have hm : renC (Σ k, ι k) c ∈ SncRes.ideal P p := by
        unfold SncRes.ideal
        rw [mem_map_renR_iff, hs]
        exact hc
      exact hw0 _ (hI hm)
    obtain ⟨hcone, h1, -⟩ := conePts_of_chartIdeal hP p w' hchart
    have hlift : (fun q => eval w (SncRes.lift p q)) = w' := by
      funext q
      unfold SncRes.lift
      split_ifs with hq
      · obtain ⟨k, i⟩ := q
        simp only at hq
        subst hq
        simp [h1 k]
      · simp [w']
    have hfz : eval w' f = 0 := by
      have h2 : eval w (bind₁ (SncRes.lift p) f) = eval (fun q => eval w (SncRes.lift p q)) f :=
        eval₂Hom_bind₁ _ _ _ _
      rw [← hlift, ← h2]
      exact hw0 _ hg
    have hD := hf w' hcone hfz
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval w') := by
      refine sup_le (sup_le (fun c hc => RingHom.mem_ker.mpr (hcone.2 c hc))
        (fun c hc => RingHom.mem_ker.mpr (hD.2 c hc))) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval w' _ = 0
      simp [h1 k]
    have h3 : eval w' ((renR (Σ k, ι k)).symm h) = 0 :=
      RingHom.mem_ker.mp (hle ((mem_map_renR_iff _ h).1 hh))
    have e1 : renC (Σ k, ι k) ((renR (Σ k, ι k)).symm h) = h := (renR (Σ k, ι k)).apply_symm_apply h
    show eval w h = 0
    rw [← e1, hren, h3]
  rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮.radical] at hvan

theorem exists_unit_mul_monomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → IsMultiHomog f a → (∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D) → ∃ (u : (locRing (SncRes.ideal P p) (renPt (affCoord p z)))ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ Jf → mm i = 0) ∧ algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (bind₁ (SncRes.lift p) f) = u * ∏ i ∈ Jf, algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r i) ^ mm i := by
  intro K _ ι _ P D e p z r Jf f a hP _ _ _ hI hreg hdim hspan hpr _ hf
  exact exists_unit_mul_monomial_of_primes (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) _ hI hdim r Jf
    hspan hpr _ fun 𝔮 h𝔮 hle _ hg => ideal_sup_le_of_mem P D p hP f hf 𝔮 h𝔮 hle hg

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartMultihomogOrderAtPointStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_chart_multihomog_order_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → IsMultiHomog f a → (∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D) → ∃ (u : (locRing (SncRes.ideal P p) (renPt (affCoord p z)))ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ Jf → mm i = 0) ∧ algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (bind₁ (SncRes.lift p) f) = u * ∏ i ∈ Jf, algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r i) ^ mm i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.UnitTimesParameterMonomialStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.unit_times_parameter_monomial : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionBoundaryNormalCrossing

section

@[expose] public section

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_sncData_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by
  intro K _ ι _ Ω _ _ y e J hA hJ hJn hS p x hx
  have hPm : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hA.2.1.2.1
  have hDm : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC J) := isMultiHomogIdeal_pC hJ
  have hz : ∀ k, SncRes.rep x ⟨k, p k⟩ ≠ 0 := hx
  have hzc := SncRes.rep_mem x
  obtain ⟨r, Jf, hIt, hreg, hdim, hspan, hpr⟩ := GlobalTheory.T.snc_chart_parameters_at_cone_point K ι Ω y e J hA hS p (SncRes.rep x) hzc hz
  have hID : SncRes.ideal (pC (mCoordIdeal y)) p ≤ SncRes.ideal (pC (mCoordIdeal y) ⊔ pC J) p :=
    Ideal.map_mono (sup_le_sup_right le_sup_left _)
  obtain ⟨h, hh, hmem, hle⟩ := GlobalTheory.T.exists_radical_locally_eq_span_prod _ e _ _ _ r Jf hID hIt hreg hdim hspan hpr
  obtain ⟨σ, hinj, hnone, hσ, hcov⟩ := GlobalTheory.T.snc_chart_regular_at_cone_point K ι _ (pC J) e p (SncRes.rep x) r Jf hPm hDm hzc hz hIt hreg hdim hspan hpr
  let d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)) :=
    { r := r, J := Jf, h := h, σ := σ, σ_injOn := hinj, σ_eq_none := hnone, span_eq := hspan, eval_h := hh,
      mem_bd := hmem, le_span := hle }
  refine ⟨d, GlobalTheory.T.snc_chart_regular_with_boundary_choice K ι _ (pC J) e p x r Jf σ hPm hDm hx hIt hreg hdim hspan hnone (fun l k hl => (hσ l k hl).1) hcov, ?_⟩
  intro f a hf hfP hfz
  obtain ⟨u, mm, hm0, hfac⟩ := GlobalTheory.T.snc_chart_multihomog_order_at_point K ι _ (pC J) e p (SncRes.rep x) r Jf f a hPm hDm hzc hz hIt hreg hdim hspan hpr hf hfz
  refine ⟨u.val, u.isUnit, ?_⟩
  refine hfac.trans (congrArg (fun w => u.val * w) (Finset.prod_congr rfl fun l hl => ?_))
  have hlJ : l ∈ Jf := hl
  obtain ⟨k, hk⟩ : ∃ k, σ l = some k := by
    cases hσl : σ l with
    | none => exact absurd hlJ ((hnone l).1 hσl)
    | some k => exact ⟨k, rfl⟩
  have hdσ : d.σ l = some k := hk
  rw [hdσ]
  obtain ⟨hQc, hX⟩ := hσ l k hk
  have hQmin := SncRes.compIdeal_mem (P := pC (mCoordIdeal y)) (pC J) k
  have hQm := GlobalTheory.T.minimal_primes_of_multihomog_sup K ι _ _ hPm hDm _ hQmin
  have hQp : (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k).IsPrime := hQmin.1.1
  have hord := GlobalTheory.T.unit_times_parameter_monomial _ e _ _ r Jf _ u mm hIt hreg hdim hspan hfac l hlJ
  have key : ∀ n : ℕ, (∃ s ∉ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k,
      s * f ∈ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k ^ n ⊔ pC (mCoordIdeal y)) ↔ n ≤ mm l := by
    intro n
    rw [← hord n, ← hQc]
    constructor
    · rintro ⟨s, hs, hsf⟩
      exact GlobalTheory.T.symbolic_power_from_affine_chart K ι _ _ p f s a n hPm hQm hQp hX hf hs hsf
    · rintro ⟨s', hs, hsf⟩
      exact GlobalTheory.T.symbolic_power_in_affine_chart K ι _ _ p f a n s' hPm hQm hQp hX hf hs hsf
  have hset : {n : ℕ | ∃ s ∉ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k,
      s * f ∈ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k ^ n ⊔ pC (mCoordIdeal y)} = Set.Iic (mm l) := by
    ext n
    exact key n
  show _ ^ mm l = _ ^ (SncRes.ordAlong _ _ f)
  rw [SncRes.ordAlong, hset, csSup_Iic]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionBoundaryNormalCrossingStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_resolution_boundary_normal_crossing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel <;> assumption)
end
end
