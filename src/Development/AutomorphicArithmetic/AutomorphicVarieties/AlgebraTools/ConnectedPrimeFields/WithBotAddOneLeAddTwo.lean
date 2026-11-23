module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CompDim
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
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
public import Mathlib.RingTheory.Regular.Flat
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
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CplFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CutDimCongr
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.TotallySplit
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CmFree

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cmFree :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B]
      [Module.Free A B], ReciprocityTheory.CA.IsCM A → ReciprocityTheory.CA.IsCM B := by
  intro A B _ _ _ _ _ _ _ h
  obtain ⟨hN, n, hdim, rs, hlen, hmem, hreg⟩ := h
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal B))
  refine ⟨IsNoetherianRing.of_finite A B, n, ?_, rs.map (algebraMap A B), by simpa using hlen, ?_,
    hreg.of_faithfullyFlat⟩
  · rw [← hdim]
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := hmem a ha
    rw [← hm] at this
    exact this
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Adjoin

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.adjoin :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra A R] [Module.Finite A R] [FaithfulSMul A R], IsBase A → ∀ f : R,
      ∃ _ : IsLocalRing (Algebra.adjoin A {f}), ReciprocityTheory.CA.IsCM (Algebra.adjoin A {f}) := by
  intro A R _ _ _ _ _ _ _ _ _ hA f
  have hf : IsIntegral A f := Algebra.IsIntegral.isIntegral f
  haveI : IsIntegrallyClosed A := hA.normal
  haveI : Algebra.IsIntegral (Algebra.adjoin A {f}) R := Algebra.IsIntegral.tower_top A
  haveI : IsLocalRing (Algebra.adjoin A {f}) :=
    RingHom.domain_isLocalRing (algebraMap (Algebra.adjoin A {f}) R)
  refine ⟨inferInstance, ?_⟩
  haveI : Module.Free A (Algebra.adjoin A {f}) := .of_basis (Algebra.adjoin.powerBasis' hf).basis
  haveI : Module.Finite A (Algebra.adjoin A {f}) := .of_basis (Algebra.adjoin.powerBasis' hf).basis
  exact cmFree hA.cm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ImportsVariant

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.one :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R], HasBase R → ∀ (f : R) (b c : Ideal R), f ∈ maximalIdeal R →
      (b ⊓ c).radical = (Ideal.span {f}).radical → b ≠ ⊤ → c ≠ ⊤ →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ b) → ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ c) →
      ringKrullDim R ≤ ringKrullDim (R ⧸ (b ⊔ c)) + 2 := by
  intro R _ _ _ hB f b c hf hrad hb hc hdb hdc
  obtain ⟨A, _, _, i, hA, hinj, hfin⟩ := hB
  letI : Algebra A R := i.toAlgebra
  haveI : Module.Finite A R := hfin
  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr hinj
  haveI : IsDomain A := hA.dom
  haveI : IsNoetherianRing A := hA.cm.1
  haveI : IsAdicComplete (maximalIdeal A) A := hA.complete
  by_cases hf0 : f = 0
  · exfalso
    subst hf0
    have hbc : b ⊓ c ≤ ⊥ := by
      intro x hx
      have : x ∈ (b ⊓ c).radical := Ideal.le_radical hx
      rw [hrad, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.radical_eq_iff.mpr (Ideal.isPrime_bot).isRadical] at this
      exact this
    have hprod : b * c = ⊥ := le_bot_iff.mp (le_trans Ideal.mul_le_inf hbc)
    rcases Ideal.mul_eq_bot.mp hprod with h | h
    · subst h
      rw [bot_sup_eq] at hdc
      exact lt_irrefl _ hdc
    · subst h
      rw [sup_bot_eq] at hdb
      exact lt_irrefl _ hdb
  obtain ⟨hloc, hcm⟩ := adjoin hA f
  haveI : IsNoetherianRing (Algebra.adjoin A {f}) := hcm.1
  haveI : Module.Finite A (Algebra.adjoin A {f}) :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom A (Algebra.adjoin A {f}) R).toLinearMap Subtype.val_injective
  haveI : IsAdicComplete (maximalIdeal (Algebra.adjoin A {f})) (Algebra.adjoin A {f}) :=
    cplFinite (A := A) (maximalIdeal _) (maximalIdeal.isMaximal _).ne_top
  haveI : Module.Finite (Algebra.adjoin A {f}) R := Module.Finite.of_restrictScalars_finite A _ R
  let x : Algebra.adjoin A {f} := ⟨f, Algebra.self_mem_adjoin_singleton A f⟩
  have hx0 : x ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hxm : x ∈ maximalIdeal (Algebra.adjoin A {f}) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have : IsUnit f := hu.map (Algebra.adjoin A {f}).val
    exact ((mem_maximalIdeal f).mp hf) this
  have hdim : ringKrullDim (Algebra.adjoin A {f} ⧸ Ideal.ofList [x]) + ↑([x].length) =
      ringKrullDim (Algebra.adjoin A {f}) := by
    have hsp : Ideal.ofList [x] = Ideal.span {x} := by simp [Ideal.ofList]
    rw [hsp]
    apply ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    · exact IsSMulRegular.of_ne_zero hx0
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hxm
  have hmap : Ideal.map (algebraMap (Algebra.adjoin A {f}) R) (Ideal.ofList [x]) = Ideal.span {f} := by
    simp [Ideal.ofList, Ideal.map_span]
    rfl
  have key := cut (A := Algebra.adjoin A {f}) (R := R) hcm [x] b c (by simpa using hxm) hdim (hmap ▸ hrad) hb hc hdb hdc
  simp only [List.length_singleton, Nat.cast_one] at key
  rw [add_assoc] at key
  exact key
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.WithBotAddOneLeAddTwo

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem hyper_dim_mono {R : Type} [CommRing R] {I J : Ideal R}
    (h : PrimeSpectrum.zeroLocus (J : Set R) ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  exact Order.krullDim_le_of_strictMono (Set.inclusion h) (fun _ _ hxy => hxy)

private theorem withBot_le_of_add_two (k : ℕ) (d : WithBot ℕ∞) (h : (k : WithBot ℕ∞) + 2 ≤ d + 2) :
    (k : WithBot ℕ∞) ≤ d := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add, le_bot_iff]; exact_mod_cast WithBot.coe_ne_bot (a := ((k + 2 : ℕ) : ℕ∞)))
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact le_top
    | coe d =>
      have h' : ((k + 2 : ℕ) : WithBot ℕ∞) ≤ ((d + 2 : ℕ) : WithBot ℕ∞) := by
        push_cast; exact h
      have h'' : k + 2 ≤ d + 2 := by exact_mod_cast h'
      have h3 : k ≤ d := by omega
      exact_mod_cast h3

private theorem withBot_add_one_le_add_two (d : WithBot ℕ∞) : d + ((1 : ℕ) : WithBot ℕ∞) ≤ d + 2 := by
  gcongr
  exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)

theorem UpperTheory.V.AlgebraTools.Conn.hyper :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R], CohenType R → ∀ (p : Ideal R) (f : R) (k : ℕ), p.IsPrime →
      f ∈ maximalIdeal R → (k : WithBot ℕ∞) + 2 ≤ ringKrullDim (R ⧸ p) → ConnOn (p ⊔ Ideal.span {f}) k := by
  intro R _ _ _ hC p f k hp hf hk I haI hI
  set a : Ideal R := p ⊔ Ideal.span {f} with ha
  have ham : a ≤ maximalIdeal R :=
    sup_le (le_maximalIdeal hp.ne_top) ((Ideal.span_singleton_le_iff_mem _).2 hf)
  have hcomp : ∀ q ∈ a.minimalPrimes, (k : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) := by
    intro q hq
    have h1 := compDim hC p q {f} hp (by simpa using hq)
    rw [Finset.card_singleton] at h1
    exact withBot_le_of_add_two k _ (hk.trans (h1.trans (withBot_add_one_le_add_two _)))
  have hle : ∀ {J K : Ideal R}, J ≤ K → ringKrullDim (R ⧸ K) ≤ ringKrullDim (R ⧸ J) :=
    fun h => hyper_dim_mono (PrimeSpectrum.zeroLocus_anti_mono_ideal h)
  have hmem : ∀ (q : Ideal R) (hq : q ∈ a.minimalPrimes),
      (⟨q, hq.1.1⟩ : PrimeSpectrum R) ∈
        PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R) := by
    intro q hq
    refine ⟨hq.1.2, fun h => ?_⟩
    have h' : I ≤ q := h
    exact absurd ((hcomp q hq).trans (hle h')) (not_le.2 hI)
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le ham
    exact ⟨_, hmem q hq⟩
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov hx hy
  by_contra hne
  obtain ⟨b0, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal t).1 ht
  obtain ⟨c0, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal t').1 ht'
  have hdisj : ∀ x : PrimeSpectrum R, a ≤ x.asIdeal → b0 ≤ x.asIdeal → c0 ≤ x.asIdeal →
      I ≤ x.asIdeal := by
    intro x h1 h2 h3
    by_contra h4
    exact hne ⟨x, ⟨h1, h4⟩, h2, h3⟩
  have hmin : ∀ q ∈ a.minimalPrimes, b0 ≤ q ∨ c0 ≤ q := fun q hq => hcov (hmem q hq)
  have hb : ∃ q ∈ a.minimalPrimes, a ⊔ b0 ≤ q := by
    obtain ⟨x, ⟨h1, h2⟩, h3⟩ := hx
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := x.asIdeal) h1
    rcases hmin q hq with h | h
    · exact ⟨q, hq, sup_le hq.1.2 h⟩
    · exact absurd (hdisj x h1 h3 (h.trans hqx)) h2
  have hc : ∃ q ∈ a.minimalPrimes, a ⊔ c0 ≤ q := by
    obtain ⟨x, ⟨h1, h2⟩, h3⟩ := hy
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := x.asIdeal) h1
    rcases hmin q hq with h | h
    · exact absurd (hdisj x h1 (h.trans hqx) h3) h2
    · exact ⟨q, hq, sup_le hq.1.2 h⟩
  set b : Ideal R := a ⊔ b0 with hbdef
  set c : Ideal R := a ⊔ c0 with hcdef
  have hpb : p ≤ b := le_sup_of_le_left le_sup_left
  have hpc : p ≤ c := le_sup_of_le_left le_sup_left
  have hbc : ringKrullDim (R ⧸ (b ⊔ c)) < k := by
    refine lt_of_le_of_lt (hyper_dim_mono fun x hx => ?_) hI
    have hx' : b ⊔ c ≤ x.asIdeal := hx
    exact hdisj x ((le_sup_of_le_left le_sup_left).trans hx')
      ((le_sup_of_le_left le_sup_right).trans hx') ((le_sup_of_le_right le_sup_right).trans hx')
  obtain ⟨q1, hq1, hbq⟩ := hb
  obtain ⟨q2, hq2, hcq⟩ := hc
  have hrad : (b ⊓ c).radical = a.radical := by
    refine le_antisymm ?_ (Ideal.radical_mono (le_inf le_sup_left le_sup_left))
    rw [Ideal.radical_le_radical_iff, ← Ideal.sInf_minimalPrimes]
    refine le_sInf fun q hq => ?_
    rcases hmin q hq with h | h
    · exact inf_le_left.trans (sup_le hq.1.2 h)
    · exact inf_le_right.trans (sup_le hq.1.2 h)
  have hdq : ∀ J : Ideal R, p ≤ J →
      ringKrullDim ((R ⧸ p) ⧸ J.map (Ideal.Quotient.mk p)) = ringKrullDim (R ⧸ J) :=
    fun J h => ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE h)
  have hcm : ∀ J : Ideal R, p ≤ J → (J.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = J := by
    intro J h
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 h]
  have hnt : ∀ J : Ideal R, p ≤ J → J ≠ ⊤ → J.map (Ideal.Quotient.mk p) ≠ ⊤ := by
    intro J h hJ h2
    apply hJ
    rw [← hcm J h, h2, Ideal.comap_top]
  haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hamap : a.map (Ideal.Quotient.mk p) = Ideal.span {Ideal.Quotient.mk p f} := by
    rw [ha, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have key := one (hC p hp) (Ideal.Quotient.mk p f) (b.map (Ideal.Quotient.mk p))
    (c.map (Ideal.Quotient.mk p)) ?_ ?_
    (hnt b hpb fun h => hq1.1.1.ne_top (top_le_iff.1 (h ▸ hbq)))
    (hnt c hpc fun h => hq2.1.1.ne_top (top_le_iff.1 (h ▸ hcq))) ?_ ?_
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb)] at key
    exact absurd (withBot_le_of_add_two k _ (hk.trans key)) (not_le.2 hbc)
  · rw [← Ideal.span_singleton_le_iff_mem, ← hamap]
    exact le_maximalIdeal (hnt a le_sup_left fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ ham)))
  · apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← hamap, Ideal.comap_radical, Ideal.comap_radical, Ideal.comap_inf, hcm b hpb, hcm c hpc,
      hcm a le_sup_left, hrad]
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb), hdq _ hpb]
    exact hbc.trans_le ((hcomp q1 hq1).trans (hle hbq))
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb), hdq _ hpc]
    exact hbc.trans_le ((hcomp q2 hq2).trans (hle hcq))
end
end
