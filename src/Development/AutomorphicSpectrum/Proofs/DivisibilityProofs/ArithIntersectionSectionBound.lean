module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupportStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionRecursionStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsPrimeFiltrationOfIsMultiHomogIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RCombine
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinearStatement
import Development.WeilBound.CoreStatements.FlagImmersions.CombLineSmoothConjInvariant
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartLatticePowerSection

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top.EffNm

theorem exists_pow_mul_pow_mem {Ω : Type} [Field Ω] (R : Subalgebra ℤ Ω) {u g h : Ω}
    (hu : u ∈ integralClosure R Ω) (hg : g ∈ R) (hh : h ∈ R) (e : u * h = g) :
    ∃ M : ℕ, ∀ n : ℕ, h ^ M * u ^ n ∈ R := by
  classical
  have hI : IsIntegral R u := hu
  obtain ⟨S, hS⟩ := hI.fg_adjoin_singleton
  have key : ∀ x ∈ Algebra.adjoin R {u}, ∃ m : ℕ, h ^ m * x ∈ R := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨1, by rw [pow_one, mul_comm, e]; exact hg⟩
    | algebraMap r => exact ⟨0, by simpa using r.2⟩
    | add x z _ _ ihx ihz =>
      obtain ⟨m₁, h₁⟩ := ihx
      obtain ⟨m₂, h₂⟩ := ihz
      refine ⟨m₁ + m₂, ?_⟩
      have e' : h ^ (m₁ + m₂) * (x + z) = h ^ m₂ * (h ^ m₁ * x) + h ^ m₁ * (h ^ m₂ * z) := by
        rw [pow_add]; ring
      rw [e']
      exact add_mem (mul_mem (pow_mem hh _) h₁) (mul_mem (pow_mem hh _) h₂)
    | mul x z _ _ ihx ihz =>
      obtain ⟨m₁, h₁⟩ := ihx
      obtain ⟨m₂, h₂⟩ := ihz
      refine ⟨m₁ + m₂, ?_⟩
      have e' : h ^ (m₁ + m₂) * (x * z) = (h ^ m₁ * x) * (h ^ m₂ * z) := by
        rw [pow_add]; ring
      rw [e']
      exact mul_mem h₁ h₂
  have hfin : ∀ T : Finset Ω, (∀ x ∈ T, x ∈ Algebra.adjoin R {u}) →
      ∃ M : ℕ, ∀ x ∈ T, h ^ M * x ∈ R := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | insert x T _ ih =>
      intro hT
      obtain ⟨M, hM⟩ := ih fun z hz => hT z (Finset.mem_insert_of_mem hz)
      obtain ⟨m, hm⟩ := key x (hT x (Finset.mem_insert_self x T))
      refine ⟨M + m, fun z hz => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · have e' : h ^ (M + m) * z = h ^ M * (h ^ m * z) := by rw [pow_add]; ring
        rw [e']
        exact mul_mem (pow_mem hh _) hm
      · have e' : h ^ (M + m) * z = h ^ m * (h ^ M * z) := by rw [pow_add]; ring
        rw [e']
        exact mul_mem (pow_mem hh _) (hM z hz)
  have hSsub : ∀ x ∈ S, x ∈ Algebra.adjoin R {u} := by
    intro x hx
    have : x ∈ Subalgebra.toSubmodule (Algebra.adjoin R {u}) := hS ▸ Submodule.subset_span hx
    exact this
  obtain ⟨M, hM⟩ := hfin S hSsub
  refine ⟨M, fun n => ?_⟩
  have hn : u ^ n ∈ Subalgebra.toSubmodule (Algebra.adjoin R {u}) :=
    pow_mem (Algebra.subset_adjoin (Set.mem_singleton u)) n
  rw [← hS] at hn
  have hall : ∀ x ∈ Submodule.span R (S : Set Ω), h ^ M * x ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hM x hx
    | zero => simp
    | add x z _ _ ihx ihz => rw [mul_add]; exact add_mem ihx ihz
    | smul r x _ ih =>
      have e' : h ^ M * r • x = (r : Ω) * (h ^ M * x) := by
        rw [Algebra.smul_def]
        show h ^ M * ((r : Ω) * x) = _
        ring
      rw [e']
      exact mul_mem r.2 ih
  exact hall _ hn

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_form_at (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (hb : Birational y)
    (hs : s ∈ chartLatNm y a 1) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (e : K → ℕ) (F : MRing ι), IsMultiHomog F e ∧ aeval y F ≠ 0 ∧
      ∀ n : ℕ, aeval y F * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((e k : ℤ) + n * a k)) ∈ chartRingZ y c := by
  classical
  have hu := hs c hc
  set u : Ω := s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) with hudef
  obtain ⟨d, g, h, hg, hh, hh0, heq⟩ := hb u
  have hG := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) hg) c hc
  have hH := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) hh) c hc
  obtain ⟨M, hM⟩ := exists_pow_mul_pow_mem (chartRingZ y c) hu hG hH (by rw [heq]; ring)
  refine ⟨M • d, h ^ M, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_pow hh M, ?_, fun n => ?_⟩
  · rw [map_pow]; exact pow_ne_zero _ hh0
  · have e' : aeval y (h ^ M) * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((((M • d) k : ℕ) : ℤ) + n * a k)) =
        (aeval y h * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ^ M * u ^ n := by
      have e2 : ∏ k, y ⟨k, c k⟩ ^ (-((((M • d) k : ℕ) : ℤ) + n * a k)) =
          (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ^ M * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) ^ n := by
        rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hc k)]
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [e2, map_pow, hudef, mul_pow, mul_pow]
      ring
    rw [e']
    exact hM n

end GlobalTheory.CompanionTheory.Ar.Top.EffNm

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem exists_mul_pow_mem_chartLat_of_mem_chartLatNm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (s : Ω), IsArithVar (mCoordIdeal y) d → Birational y → s ∈ chartLatNm y a 1 → ∃ (b : K → ℤ) (c : Ω), c ≠ 0 ∧ ∀ n : ℕ, c * s ^ n ∈ chartLat y (b + (n : ℤ) • a) 1 := by
  intro K _ ι _ Ω _ y _ a s _ hb hs
  classical
  have hex : ∀ c : ∀ k, ι k, ∃ (e : K → ℕ) (F : MRing ι), IsMultiHomog F e ∧ aeval y F ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n : ℕ,
        aeval y F * s ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((e k : ℤ) + n * a k)) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨e, F, h1, h2, h3⟩ := EffNm.exists_form_at y a s hb hs c hc
      exact ⟨e, F, h1, h2, fun _ => h3⟩
    · exact ⟨0, 1, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp, fun h => absurd h hc⟩
  choose e F hF hF0 hFc using hex
  refine ⟨∑ c, fun k => (e c k : ℤ), ∏ c, aeval y (F c),
    Finset.prod_ne_zero_iff.2 fun c _ => hF0 c, fun n => ?_⟩
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one]
  intro c₀ hc₀
  have hP := (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).1
    (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_prod (y := y)
      (Finset.univ.erase c₀) (fun c => aeval y (F c)) (fun c k => (e c k : ℤ))
      (fun c _ => GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.chartLat_form (y := y) (hF c)))
    c₀ hc₀
  have hQ := hFc c₀ hc₀ n
  have e' : (∏ c, aeval y (F c)) * s ^ n *
        ∏ k, y ⟨k, c₀ k⟩ ^ (-(((∑ c, fun k => (e c k : ℤ)) + (n : ℤ) • a) k)) =
      (aeval y (F c₀) * s ^ n * ∏ k, y ⟨k, c₀ k⟩ ^ (-((e c₀ k : ℤ) + n * a k))) *
        ((∏ c ∈ Finset.univ.erase c₀, aeval y (F c)) *
          ∏ k, y ⟨k, c₀ k⟩ ^ (-((∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ)) k))) := by
    have e1 : ∏ c, aeval y (F c) = aeval y (F c₀) * ∏ c ∈ Finset.univ.erase c₀, aeval y (F c) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ c₀)).symm
    have e2 : ∏ k, y ⟨k, c₀ k⟩ ^ (-(((∑ c, fun k => (e c k : ℤ)) + (n : ℤ) • a) k)) =
        (∏ k, y ⟨k, c₀ k⟩ ^ (-((e c₀ k : ℤ) + n * a k))) *
          ∏ k, y ⟨k, c₀ k⟩ ^ (-((∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ)) k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc₀ k)]
      congr 1
      have e3 : (∑ c, fun k => (e c k : ℤ)) =
          (fun k => (e c₀ k : ℤ)) + ∑ c ∈ Finset.univ.erase c₀, fun k => (e c k : ℤ) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ c₀)).symm
      rw [e3]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2]
    ring
  rw [e']
  exact mul_mem hQ hP

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartLatticePowerSectionStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.chart_lattice_power_section : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (s : Ω), IsArithVar (mCoordIdeal y) d → Birational y → s ∈ chartLatNm y a 1 → ∃ (b : K → ℤ) (c : Ω), c ≠ 0 ∧ ∀ n : ℕ, c * s ^ n ∈ chartLat y (b + (n : ℤ) • a) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.exists_mul_pow_mem_chartLat_of_mem_chartLatNm <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.ExistsSmooth

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.EffN

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_comb {J : Type} [Fintype J] {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j))
    (n : J → ℤ) : IsSmoothHerm (combLine ℓ n) := by
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ∏ j, (ℓ j).h z ^ n j)
    {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  exact contDiffOn_prod (fun j _ => RootFieldNumerics.Ii.contDiffOn_zpow_h (ℓ j) (hℓ j) (n j))

theorem comb_a {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ) :
    (combLine ℓ n).a = ∑ j, n j • (ℓ j).a := rfl

theorem exists_smooth (b : K → ℤ) : ∃ B : HermLine ι, IsSmoothHerm B ∧ B.a = b := by
  apply PositivityTheory.UnitarySelfGeneration.RC.exists_line <;> assumption

theorem smooth_snoc {e : ℕ} {L : Fin e → HermLine ι} {X : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) (j : Fin (e + 1)) :
    IsSmoothHerm ((Fin.snoc L X : Fin (e + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa using hX
  · simpa using hL i

theorem last_lin (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι)) (e : ℕ)
    (hP : IsArithVar P (e + 2)) (L : Fin e → HermLine ι) (A B C : HermLine ι) (m : ℤ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (hC : IsSmoothHerm C)
    (hdeg : C.a = B.a + m • A.a) :
    ptsIntegral P (fun j z => Real.log (((Fin.snoc L C : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) =
      ptsIntegral P (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) +
        m * ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z))
          (fun _ => 1) := by
  classical
  let ℓ : Fin e ⊕ Bool → HermLine ι := Sum.elim L (fun t => if t then A else B)
  have hℓ : ∀ j, IsSmoothHerm (ℓ j) := by
    rintro (i | _ | _) <;> simp [ℓ, hL, hA, hB]
  let n : Fin (e + 1) → Fin e ⊕ Bool → ℤ :=
    Fin.snoc (fun i => Pi.single (Sum.inl i) 1)
      (Pi.single (Sum.inr false) 1 + m • Pi.single (Sum.inr true) 1)
  obtain ⟨hexp, hperm⟩ := GlobalTheory.T.log_integral_multilinear II hII K ι P (e + 1) (Fin e ⊕ Bool) ℓ n hP hℓ
  have h1 := hperm (fun k => combLine ℓ (n k)) (Fin.snoc L C) 1 (fun k => smooth_comb hℓ _)
    (smooth_snoc hL hC) (by
      intro k
      simp only [Equiv.Perm.coe_one, id]
      rw [comb_a]
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp [n, ℓ, Fintype.sum_sum_type, Pi.single_apply, hdeg]
        abel
      · simp [n, ℓ, Fintype.sum_sum_type, Pi.single_apply])
  let w0 : Fin (e + 1) → Fin e ⊕ Bool := Fin.snoc (fun i => Sum.inl i) (Sum.inr false)
  let w1 : Fin (e + 1) → Fin e ⊕ Bool := Fin.snoc (fun i => Sum.inl i) (Sum.inr true)
  have hne : w0 ≠ w1 := by
    intro h
    have := congrFun h (Fin.last e)
    simp [w0, w1] at this
  have hzero : ∀ w : Fin (e + 1) → Fin e ⊕ Bool, w ≠ w0 ∧ w ≠ w1 →
      (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) = 0 := by
    rintro w ⟨hw0, hw1⟩
    apply mul_eq_zero_of_left
    by_contra hprod
    have hf : ∀ k, (n k (w k) : ℝ) ≠ 0 := fun k =>
      Finset.prod_ne_zero_iff.mp hprod k (Finset.mem_univ _)
    have hcs : ∀ i : Fin e, w (Fin.castSucc i) = Sum.inl i := by
      intro i
      have := hf (Fin.castSucc i)
      simp [n, Pi.single_apply] at this
      exact this
    have hl := hf (Fin.last e)
    rcases hw : w (Fin.last e) with i | (_ | _)
    · rw [hw] at hl
      simp [n, Pi.single_apply] at hl
    · exact hw0 (funext fun k => by
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simp [w0, hw]
        · simp [w0, hcs i])
    · exact hw1 (funext fun k => by
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simp [w1, hw]
        · simp [w1, hcs i])
  have e0 : ∀ k, ℓ (w0 k) = (Fin.snoc L B : Fin (e + 1) → HermLine ι) k := by
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [ℓ, w0]
  have e1 : ∀ k, ℓ (w1 k) = (Fin.snoc L A : Fin (e + 1) → HermLine ι) k := by
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [ℓ, w1]
  have p0 : ∏ k, (n k (w0 k) : ℝ) = 1 := by
    rw [Fin.prod_univ_castSucc]
    simp [n, w0]
  have p1 : ∏ k, (n k (w1 k) : ℝ) = m := by
    rw [Fin.prod_univ_castSucc]
    simp [n, w1]
  rw [h1, hexp, Fintype.sum_eq_add w0 w1 hne hzero, p0, p1]
  simp only [e0, e1, one_mul]

end RootFieldNumerics.EffN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.IntersectionSectionLogIntegral

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.intersection_section_log_integral : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  intro hK hEU hDiv II hII K _ ι _ Ω _ y e L A s hV hB hL hA hs hsA hgeo
  have hW : ∀ W : Ideal (MRing ι), IsArithVar W (e + 1) → mCoordIdeal y ≤ W →
      0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    intro W hW hle
    exact GlobalTheory.T.ptsIntegral_log_nonneg hK hEU hDiv II hII K ι W e L hW hL
      (fun j W' hW' hle' => hgeo j W' hW' (le_trans hle hle'))
  obtain ⟨b, c, hc0, hc⟩ := GlobalTheory.T.chart_lattice_power_section K ι Ω y (e + 2) A.a s hV hB hsA
  obtain ⟨B, hBs, hBa⟩ := RootFieldNumerics.EffN.exists_smooth (ι := ι) b
  have key : ∀ n : ℕ, 0 ≤ ptsIntegral (mCoordIdeal y)
      (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
      + (n : ℝ) * ptsIntegral (mCoordIdeal y)
      (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
    intro n
    obtain ⟨C, hCs, hCa⟩ := RootFieldNumerics.EffN.exists_smooth (ι := ι) (b + n • A.a)
    have hCa' : C.a = B.a + (n : ℤ) • A.a := by rw [hCa, hBa, natCast_zsmul]
    have hmem : c * s ^ n ∈ chartLat y C.a 1 := by rw [hCa]; exact hc n
    have h0 := GlobalTheory.T.arith_intersection_section_recursion II hII hDiv K ι Ω y e L C (c * s ^ n) hV hB hL hCs
      (mul_ne_zero hc0 (pow_ne_zero _ hs)) hmem hW
    rw [RootFieldNumerics.EffN.last_lin II hII (mCoordIdeal y) e hV L A B C (n : ℤ) hL hA hBs hCs hCa'] at h0
    simpa using h0
  set PB := ptsIntegral (mCoordIdeal y)
    (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
  set PA := ptsIntegral (mCoordIdeal y)
    (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
  by_contra hneg
  push_neg at hneg
  have hpos : 0 < -PA := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (PB / -PA)
  have h1 := (div_lt_iff₀ hpos).mp hn
  have h2 := key n
  have h3 : (n : ℝ) * -PA = -((n : ℝ) * PA) := by ring
  linarith
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionBound

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem effective_mul_nef_nonneg : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) :=
  @RootFieldNumerics.intersection_section_log_integral

end GlobalTheory.CompanionTheory.Ar.Top
end
end
