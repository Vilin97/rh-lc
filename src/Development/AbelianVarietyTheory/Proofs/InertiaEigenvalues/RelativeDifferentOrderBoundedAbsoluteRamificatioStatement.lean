module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNeZeroFiniteLocalZmodPrimePowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntCastTraceEqTraceQuotientOfMemStatement
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
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxIdealExactPowDvdSpanPrime

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem maxIdeal_exact_pow_dvd_span_prime : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsMaximal], ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ∃ (e' : ℕ) (J : Ideal (𝓞 L)), 0 < e' ∧ e' ≤ e ∧ la ⊔ J = ⊤ ∧ Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e' * J := by
  intro L _ _ l e _ la hmax hin hout
  classical
  have hex : ∃ k, ((l : ℕ) : 𝓞 L) ∉ la ^ (k + 1) := ⟨e, hout⟩
  have hspec : ((l : ℕ) : 𝓞 L) ∉ la ^ (Nat.find hex + 1) := Nat.find_spec hex
  have hle : Nat.find hex ≤ e := Nat.find_min' hex hout
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h, zero_add, pow_one] at hspec; exact hspec hin
    · exact h
  have hmem : ((l : ℕ) : 𝓞 L) ∈ la ^ Nat.find hex := by
    have h1 := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [not_not] at h1
    have h4 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rwa [h4] at h1
  have hdvd : la ^ Nat.find hex ∣ Ideal.span {((l : ℕ) : 𝓞 L)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hmem
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨Nat.find hex, J, hpos, hle, ?_, hJ⟩
  by_contra hne
  have hJle : J ≤ la := by
    have h2 := hmax.eq_of_le hne le_sup_left
    calc J ≤ la ⊔ J := le_sup_right
      _ = la := h2.symm
  apply hspec
  have h3 : Ideal.span {((l : ℕ) : 𝓞 L)} ≤ la ^ (Nat.find hex + 1) := by
    rw [hJ, pow_succ]; exact Ideal.mul_mono_right hJle
  exact h3 (Ideal.subset_span (Set.mem_singleton _))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxIdealExactPowDvdSpanPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_span_prime_eq_pow_mul_coprime : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsMaximal], ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ∃ (e' : ℕ) (J : Ideal (𝓞 L)), 0 < e' ∧ e' ≤ e ∧ la ⊔ J = ⊤ ∧ Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e' * J := by
  first | exact @GlobalTheory.maxIdeal_exact_pow_dvd_span_prime | exact GlobalTheory.maxIdeal_exact_pow_dvd_span_prime | (intros; apply GlobalTheory.maxIdeal_exact_pow_dvd_span_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalCharPLocalCard

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quot_pow_maximal_charP_local_card : ∀ (L : Type) [Field L] [NumberField L] (la J : Ideal (𝓞 L)) [la.IsMaximal] (l e b : ℕ), l.Prime → 0 < e → 0 < b → la ⊔ J = ⊤ → Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e * J → CharP (𝓞 L ⧸ la ^ (e * b)) (l ^ b) ∧ Finite (𝓞 L ⧸ la ^ (e * b)) ∧ ∃ π : 𝓞 L ⧸ la ^ (e * b), (∀ x : 𝓞 L ⧸ la ^ (e * b), ¬ IsUnit x ↔ π ∣ x) ∧ Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ (e * b))} = Ideal.span {π ^ e} ∧ Nat.card (𝓞 L ⧸ la ^ (e * b)) = Nat.card ((𝓞 L ⧸ la ^ (e * b)) ⧸ Ideal.span {π}) ^ (b * e) := by
  intro L _ _ la J hmax l e b hl he hb hJ hspan
  have hn0 : e * b ≠ 0 := Nat.mul_ne_zero he.ne' hb.ne'
  set n := e * b with hn
  set q := Ideal.Quotient.mk (la ^ n) with hq
  have hlla : ((l : ℕ) : 𝓞 L) ∈ la := by
    have : ((l:ℕ) : 𝓞 L) ∈ la ^ e * J := by rw [← hspan]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.pow_le_self he.ne' : la ^ e ≤ la) ((Ideal.mul_le_left : la ^ e * J ≤ la ^ e) this)
  have hl0 : ((l : ℕ) : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hla0 : la ≠ ⊥ := fun h => hl0 (by rw [h] at hlla; simpa using hlla)
  have hlatop : la ≠ ⊤ := hmax.ne_top
  have hpowle : ∀ i j : ℕ, la ^ i ≤ la ^ j ↔ j ≤ i := fun i j =>
    ⟨fun h => by
      by_contra hc
      rw [not_le] at hc
      exact absurd h (Ideal.pow_right_strictAnti la hla0 hlatop hc).not_ge,
     fun h => Ideal.pow_le_pow_right h⟩
  have hle : la ^ n ≤ la := Ideal.pow_le_self hn0
  have hnil : ∀ c ∈ la, IsNilpotent (q c) := fun c hc =>
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hc n⟩
  have hunit : ∀ a : 𝓞 L, IsUnit (q a) ↔ a ∉ la := by
    intro a
    constructor
    · intro hu ha
      obtain ⟨d, hd⟩ := hu.exists_right_inv
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective d
      have : a * c - 1 ∈ la ^ n := by
        rw [← Ideal.Quotient.eq]; simpa [hq] using hd
      have h1 : (1 : 𝓞 L) ∈ la := by
        have := la.sub_mem (la.mul_mem_right c ha) (hle this)
        simpa using this
      exact hlatop ((Ideal.eq_top_iff_one _).mpr h1)
    · intro ha
      obtain ⟨c, y, hy, hcy⟩ := hmax.exists_inv ha
      have h1 : q c * q a = 1 - q y := by
        rw [← map_mul, ← map_one q, ← map_sub, ← hcy]; simp
      have : IsUnit (q c * q a) := h1 ▸ (hnil y hy).isUnit_one_sub
      exact isUnit_of_mul_isUnit_right this
  have hmem : ∀ a : 𝓞 L, q a ∈ la.map q ↔ a ∈ la := fun a => Ideal.mem_quotient_iff_mem hle

  obtain ⟨π₀, hπla, hπ2⟩ := SetLike.exists_of_lt ((Ideal.pow_right_strictAnti la hla0 hlatop) (by norm_num : 1 < 2))
  replace hπla : π₀ ∈ la := by simpa using hπla
  change π₀ ∉ la ^ 2 at hπ2
  have hQ : Ideal.span {π₀} ⊔ la ^ 2 = la := by
    have := Ideal.eq_prime_pow_of_succ_lt_of_le (P := la) (I := Ideal.span {π₀} ⊔ la ^ 2) hla0 (i := 1)
      (lt_of_le_of_ne le_sup_right (fun h => hπ2 (h ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π₀))))
      (by rw [pow_one]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hπla) (Ideal.pow_le_self two_ne_zero))
    simpa using this
  have hk : ∀ k, 1 ≤ k → la ≤ Ideal.span {π₀} ⊔ la ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [pow_one]; exact le_sup_right
    | succ k _ ih =>
      calc la = Ideal.span {π₀} ⊔ la ^ 2 := hQ.symm
        _ ≤ Ideal.span {π₀} ⊔ la * (Ideal.span {π₀} ⊔ la ^ k) :=
            sup_le_sup_left (by rw [pow_two]; exact Ideal.mul_mono_right ih) _
        _ = Ideal.span {π₀} ⊔ (la * Ideal.span {π₀} ⊔ la ^ (k + 1)) := by rw [Ideal.mul_sup, pow_succ']
        _ ≤ Ideal.span {π₀} ⊔ la ^ (k + 1) :=
            sup_le le_sup_left (sup_le (le_trans Ideal.mul_le_right le_sup_left) le_sup_right)
  have hm : Ideal.span {q π₀} = la.map q := by
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]; exact (hmem π₀).mpr hπla
    · calc la.map q ≤ (Ideal.span {π₀} ⊔ la ^ n).map q := Ideal.map_mono (hk n (Nat.one_le_iff_ne_zero.mpr hn0))
        _ = Ideal.span {q π₀} := by
            rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hq, Ideal.map_quotient_self, sup_bot_eq]
  have hJtop : J.map q = ⊤ := by
    have : (1 : 𝓞 L) ∈ la ⊔ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp this
    have hz' : q z = 1 - q y := by rw [← map_one q, ← hyz, map_add (f := _)]; ring
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem q hz) (hz' ▸ (hnil y hy).isUnit_one_sub)
  have hlspan : Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ n)} = (la.map q) ^ e := by
    have : ((l : ℕ) : 𝓞 L ⧸ la ^ n) = q (l : 𝓞 L) := (map_natCast q l).symm
    rw [this, ← Set.image_singleton, ← Ideal.map_span, hspan, Ideal.map_mul, Ideal.map_pow, hJtop, Ideal.mul_top]
  refine ⟨⟨fun k => ?_⟩, ?_, q π₀, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    obtain ⟨v, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0.ne' l hl.ne_one
    have hcop : Nat.Coprime l m' := (Nat.Prime.coprime_iff_not_dvd hl).mpr hm'
    have hm'la : ((m' : ℕ) : 𝓞 L) ∉ la := by
      intro h
      obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      have h1 : ((u * l + w * m' : ℤ) : 𝓞 L) = 1 := by rw [huw]; simp
      push_cast at h1
      have : (1 : 𝓞 L) ∈ la := h1 ▸ la.add_mem (la.mul_mem_left _ hlla) (la.mul_mem_left _ h)
      exact hlatop ((Ideal.eq_top_iff_one _).mpr this)
    have hmu : IsUnit ((m' : ℕ) : 𝓞 L ⧸ la ^ n) := by
      rw [← map_natCast q]; exact (hunit _).mpr hm'la
    rw [Nat.cast_mul, Nat.cast_pow, hmu.mul_left_eq_zero, ← Ideal.span_singleton_eq_bot,
      ← Ideal.span_singleton_pow, hlspan, ← pow_mul, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, hq,
      Ideal.mk_ker, hpowle, (Nat.Coprime.pow_left b hcop).dvd_mul_right,
      Nat.pow_dvd_pow_iff_le_right hl.one_lt, hn]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h he, fun h => Nat.mul_le_mul_left e h⟩
  · exact Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero n hla0)
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← Ideal.mem_span_singleton, hm, hmem]
    exact (not_congr (hunit a)).trans not_not
  · rw [← Ideal.span_singleton_pow, hm, hlspan]
  · have hc1 : Nat.card ((𝓞 L ⧸ la ^ n) ⧸ la.map q) = Nat.card (𝓞 L ⧸ la) :=
      Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv
    have hc2 : ∀ I : Ideal (𝓞 L), Nat.card (𝓞 L ⧸ I) = Ideal.absNorm I := fun I => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hm, hc1, hc2, hc2, map_pow, hn, mul_comm e b]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalCharPLocalCardStatement

section

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.quotient_pow_finite_uniformizer_card_eq : ∀ (L : Type) [Field L] [NumberField L] (la J : Ideal (𝓞 L)) [la.IsMaximal] (l e b : ℕ), l.Prime → 0 < e → 0 < b → la ⊔ J = ⊤ → Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e * J → CharP (𝓞 L ⧸ la ^ (e * b)) (l ^ b) ∧ Finite (𝓞 L ⧸ la ^ (e * b)) ∧ ∃ π : 𝓞 L ⧸ la ^ (e * b), (∀ x : 𝓞 L ⧸ la ^ (e * b), ¬ IsUnit x ↔ π ∣ x) ∧ Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ (e * b))} = Ideal.span {π ^ e} ∧ Nat.card (𝓞 L ⧸ la ^ (e * b)) = Nat.card ((𝓞 L ⧸ la ^ (e * b)) ⧸ Ideal.span {π}) ^ (b * e) := by
  first | exact @GlobalTheory.quot_pow_maximal_charP_local_card | exact GlobalTheory.quot_pow_maximal_charP_local_card | (intros; apply GlobalTheory.quot_pow_maximal_charP_local_card <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatio

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.TowerDifferent

theorem not_pow_dvd_differentIdeal_int : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsPrime], la ≠ ⊥ → ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ¬ la ^ (e * e + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  intro L _ _ l e hl la _ hla h1 h2 hD
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : la.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hla
  obtain ⟨e', J, he0, hee, hcop, hfac⟩ := GlobalTheory.T.exists_span_prime_eq_pow_mul_coprime L l e hl la h1 h2
  obtain ⟨hchar, hfin, ϖ, hϖ, hlϖ, hcard⟩ := GlobalTheory.T.quotient_pow_finite_uniformizer_card_eq L la J l e' e' hl he0 he0 hcop hfac
  letI : Algebra (ZMod (l ^ e')) (𝓞 L ⧸ la ^ (e' * e')) := ZMod.algebra _ _
  have hnd : ¬ l ^ e' ∣ e' := fun h => (Nat.lt_pow_self hl.one_lt).not_ge (Nat.le_of_dvd he0 h)
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_trace_ne_zero_finite_local_zmod_prime_pow l e' e' (𝓞 L ⧸ la ^ (e' * e')) ϖ he0 hϖ hlϖ hcard hnd
  obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hIQ : la ^ (e' * e') ⊔ J ^ e' = ⊤ := by
    have h' : IsCoprime la J := Ideal.isCoprime_iff_sup_eq.mpr hcop
    exact Ideal.isCoprime_iff_sup_eq.mp (h'.pow)
  have hmul : la ^ (e' * e') * J ^ e' = Ideal.span {((l ^ e' : ℕ) : 𝓞 L)} := by
    rw [pow_mul, ← mul_pow, ← hfac, Ideal.span_singleton_pow, Nat.cast_pow]
  obtain ⟨i, hi, q, hq, hiq⟩ : ∃ i ∈ la ^ (e' * e'), ∃ q ∈ J ^ e', i + q = 1 := by
    have : (1 : 𝓞 L) ∈ la ^ (e' * e') ⊔ J ^ e' := hIQ ▸ Submodule.mem_top
    exact Submodule.mem_sup.mp this
  have hx : q * c0 ∈ J ^ e' := Ideal.mul_mem_right _ _ hq
  have hxc : Ideal.Quotient.mk (la ^ (e' * e')) (q * c0) = Ideal.Quotient.mk (la ^ (e' * e')) c0 := by
    rw [Ideal.Quotient.eq]
    have : q * c0 - c0 = -(i * c0) := by linear_combination c0 * hiq
    rw [this]; exact neg_mem (Ideal.mul_mem_right _ _ hi)
  have htr := GlobalTheory.T.intCast_trace_eq_trace_quotient_of_mem' L l e' (la ^ (e' * e')) (J ^ e') hIQ hmul (q * c0) hx
  rw [hxc] at htr
  have hnot : Algebra.intTrace ℤ (𝓞 L) (q * c0) ∉ Ideal.span {((l ^ e' : ℕ) : ℤ)} := by
    intro hm
    rw [Algebra.intTrace_eq_trace, Ideal.mem_span_singleton] at hm
    apply hc
    rw [← htr, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hm)]
  have hmap : la ^ (e' * e') * J ^ e' = Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((l ^ e' : ℕ) : ℤ)}) := by
    rw [hmul, Ideal.map_span, Set.image_singleton, map_natCast]
  have := not_dvd_differentIdeal_of_intTrace_not_mem (A := ℤ) (la ^ (e' * e')) (J ^ e') hmap (q * c0) hx hnot
  apply this
  refine dvd_trans (pow_dvd_pow _ ?_) hD
  have := Nat.mul_le_mul hee hee
  omega

theorem differentIdeal_dvd_int (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    differentIdeal (𝓞 K) (𝓞 L) ∣ differentIdeal ℤ (𝓞 L) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 L)]
  exact dvd_mul_right _ _

theorem relDifferent_order_bounded : ∀ (l e : ℕ), l.Prime → ∃ c : ℕ, ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  intro l e hl
  refine ⟨e * e, ?_⟩
  intro K L _ _ _ _ _ p la _ h1 h2 h3
  exact not_pow_dvd_differentIdeal_int L l e hl la.asIdeal la.ne_bot h1 h2 (dvd_trans h3 (differentIdeal_dvd_int K L))

end GlobalTheory.TowerDifferent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatioStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

theorem _root_.GlobalTheory.T.relative_different_order_bounded_absolute_ramification : ∀ (l e : ℕ), l.Prime → ∃ c : ℕ, ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  first | exact @GlobalTheory.TowerDifferent.relDifferent_order_bounded | exact GlobalTheory.TowerDifferent.relDifferent_order_bounded | (intros; apply GlobalTheory.TowerDifferent.relDifferent_order_bounded <;> assumption)
end
end
