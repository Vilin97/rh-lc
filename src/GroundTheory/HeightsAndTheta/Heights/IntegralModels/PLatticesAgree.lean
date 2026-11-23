module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import Mathlib.RingTheory.Localization.FractionRing
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmulMemOfSpanEqTop

section

@[expose] public section

theorem UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top :
    ∀ {A : Type} [inst : CommRing A] [IsDomain A]
    {K : Type} [inst_2 : Field K] [inst_3 : Algebra A K] [IsFractionRing A K] {V : Type} [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module K V] [inst_7 : _root_.Module A V] [IsScalarTower A K V] (M : Submodule A V),
    Submodule.span K (↑M : Set V) = ⊤ → ∀ (v : V), ∃ (d : A), d ≠ (0 : A) ∧ d • v ∈ M := by
  intro A _ _ K _ _ _ V _ _ _ _ M hM v
  have hv : v ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨b, hb, hby⟩ := ihy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hax
    · rw [mul_smul]
      exact M.smul_mem a hby
  | smul k x _ ih =>
    obtain ⟨a, ha, hax⟩ := ih
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap A K q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap A K p / algebraMap A K q) • x) = p • (a • x) := by
      rw [← algebraMap_smul K (a * q), ← algebraMap_smul K a, ← algebraMap_smul K p,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem p hax
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

theorem exists_ne_zero_smul_mem_of_span_eq_top (M : Submodule A V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ d : A, d ≠ 0 ∧ d • v ∈ M :=
  _root_.UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top M hM v

theorem mem_of_forall_mem_localizedIn (hHOI : HeightOneIntersection.Statement)
    [IsNoetherianRing A] [IsIntegrallyClosed A] (M : Submodule A V) [Module.Projective A M]
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V)
    (hv : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → v ∈ localizedIn p.asIdeal M) : v ∈ M := by
  obtain ⟨d, hd, hdv⟩ := exists_ne_zero_smul_mem_of_span_eq_top (K := K) M hM v
  obtain ⟨c, hc⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  set x : M := ⟨d • v, hdv⟩ with hx
  have hdK : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hd

  have hdiv : ∀ y : M, ∃ a : A, c x y = d * a := by
    intro y
    have hq : algebraMap A K (c x y) / algebraMap A K d ∈
        Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
      rw [hHOI A K]
      simp only [Submodule.mem_iInf]
      intro p hp
      obtain ⟨s, hs, hsv⟩ := hv p hp
      refine ⟨s, hs, ?_⟩
      set x' : M := ⟨s • v, hsv⟩
      have hxx : d • x' = s • x := by
        ext; simp only [x', hx, SetLike.val_smul, smul_smul, mul_comm]
      have hcc : d * c x' y = s * c x y := by
        have := congrArg (fun z => c z y) hxx
        simpa [map_smul] using this
      refine Algebra.mem_bot.mpr ⟨c x' y, ?_⟩
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, ← hcc, map_mul,
        mul_div_right_comm, div_self hdK, one_mul]
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hq
    refine ⟨a, IsFractionRing.injective A K ?_⟩
    rw [map_mul, ha, mul_div_cancel₀ _ hdK]
  choose a ha using hdiv
  have hw : (∑ y ∈ (c x).support, a y • (y : V)) ∈ M :=
    M.sum_mem fun y _ => M.smul_mem (a y) y.2
  have hsum : d • v = d • ∑ y ∈ (c x).support, a y • (y : V) := by
    have h1 : ((Finsupp.linearCombination A id (c x) : M) : V) = d • v := by rw [hc x]
    rw [← h1, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Submodule.coe_smul, id, ha y, mul_smul]
  have hvw : v = ∑ y ∈ (c x).support, a y • (y : V) := by
    rw [← algebraMap_smul K d v, ← algebraMap_smul K d (∑ y ∈ (c x).support, a y • (y : V))]
      at hsum
    exact smul_right_injective V hdK hsum
  rw [hvw]
  exact hw

theorem LatticesAgree.proof (hHOI : HeightOneIntersection.Statement) : LatticesAgree.Statement := by
  intro A _ _ _ _ K _ _ _ V _ _ _ _ _ M N _ hMp _ hNp hM hN hMN
  have sub : ∀ (P Q : Submodule A V), Module.Projective A P →
      Submodule.span K (P : Set V) = ⊤ →
      (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
        localizedIn p.asIdeal Q = localizedIn p.asIdeal P) → Q ≤ P := by
    intro P Q hP hPs hQP v hvQ
    exact mem_of_forall_mem_localizedIn (K := K) hHOI P hPs v fun p hp =>
      hQP p hp ▸ ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hvQ⟩
  exact le_antisymm (sub N M hNp hN fun p hp => hMN p hp)
    (sub M N hMp hM fun p hp => (hMN p hp).symm)

end GroundTheory.Heights₂.Heights.Model
end
end
