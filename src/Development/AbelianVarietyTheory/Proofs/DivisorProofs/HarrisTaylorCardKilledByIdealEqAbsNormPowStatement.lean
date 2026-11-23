module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModule
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKilledByIdealModIntEqAbsNormPow

section

@[expose] public section

open scoped NumberField

namespace GlobalTheory.TorsQuotCount

variable {K : Type} [Field K] [NumberField K] {M : Type} [AddCommGroup M] [Module (𝓞 K) M]

theorem flat_of_free [Module.Free ℤ M] : Module.Flat (𝓞 K) M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : a • x = 0 := hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hI : Ideal.span {a} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using ha0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hN : Ideal.absNorm (Ideal.span {a}) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  have h2 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) • x = 0 := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← ht, mul_smul, hx', smul_zero]
  exact (Submodule.mem_bot _).2 ((smul_eq_zero.1 h2).resolve_left (by exact_mod_cast hN))

theorem finrank_eq [Module.Free ℤ M] [Module.Finite ℤ M] (r : ℕ)
    (hr : Module.finrank ℤ M = r * Module.finrank ℚ K) : Module.finrank (𝓞 K) M = r := by
  haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M
  haveI : Module.Flat (𝓞 K) M := flat_of_free
  have h20 : (2 : 𝓞 K) ≠ 0 := two_ne_zero
  have hI : Ideal.span {(2 : 𝓞 K)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using h20
  haveI : Finite (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have e1 := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(2 : 𝓞 K)})
  haveI : Finite (ℤ ⧸ Ideal.span {((2 : ℕ) : ℤ)}) :=
    Nat.finite_of_card_ne_zero (by rw [Int.card_ideal_quot]; norm_num)
  have e2 := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := ℤ) (N := M) (Ideal.span {((2 : ℕ) : ℤ)})
  rw [Int.card_ideal_quot] at e2
  have hq : Nat.card (𝓞 K ⧸ Ideal.span {(2 : 𝓞 K)}) = 2 ^ Module.finrank ℚ K := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
    have h2 : (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 := by simp
    rw [h2, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    rfl
  have hPQ : (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M).restrictScalars ℤ =
      (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by simp [two_smul]⟩
  have hsame : Nat.card (M ⧸ (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)) =
      Nat.card (M ⧸ (Ideal.span {((2 : ℕ) : ℤ)} • ⊤ : Submodule ℤ M)) := by
    rw [← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {(2 : 𝓞 K)} • ⊤ : Submodule (𝓞 K) M)).toEquiv, hPQ]
  rw [hsame, e2, hq, hr, ← pow_mul] at e1
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h3 := Nat.pow_right_injective (le_refl 2) e1
  have h4 : Module.finrank ℚ K * r = Module.finrank ℚ K * Module.finrank (𝓞 K) M := by
    rw [mul_comm] at h3; exact h3
  exact (Nat.eq_of_mul_eq_mul_left hn h4).symm

theorem card_killed_eq : ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M],
    Module.Free ℤ M → Module.Finite ℤ M → ∀ (r : ℕ), Module.finrank ℤ M = r * Module.finrank ℚ K →
    ∀ (𝔟 : Ideal (𝓞 K)) (c : ℕ), 0 < c → (c : 𝓞 K) ∈ 𝔟 →
    Nat.card {x : M ⧸ (Ideal.span {(c : 𝓞 K)} • (⊤ : Submodule (𝓞 K) M)) // ∀ a ∈ 𝔟, a • x = 0} =
      Ideal.absNorm 𝔟 ^ r := by
  intro K _ _ M _ _ hfree hfin r hr 𝔟 c hc hcb
  haveI : Module.Finite (𝓞 K) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) M
  haveI : Module.Flat (𝓞 K) M := flat_of_free
  have hd := finrank_eq (K := K) (M := M) r hr
  have hc0 : (c : 𝓞 K) ≠ 0 := by exact_mod_cast hc.ne'
  have hspan : Ideal.span {(c : 𝓞 K)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hc0
  have hb : 𝔟 ≠ ⊥ := fun h => hc0 (by rw [h] at hcb; exact (Submodule.mem_bot _).1 hcb)
  haveI : Finite (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hspan
  haveI : Finite (𝓞 K ⧸ 𝔟) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have hX := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) (Ideal.span {(c : 𝓞 K)})
  have hNc : Nat.card (𝓞 K ⧸ Ideal.span {(c : 𝓞 K)}) ≠ 0 := Nat.card_pos.ne'
  set P : Submodule (𝓞 K) M := Ideal.span {(c : 𝓞 K)} • ⊤ with hP
  haveI : Finite (M ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hX]; exact pow_ne_zero _ hNc)
  obtain ⟨b, hbsup⟩ := IsDedekindDomain.exists_sup_span_eq ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb) hspan
  have hcX : ∀ x : M ⧸ P, (c : 𝓞 K) • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  let f : (M ⧸ P) →ₗ[𝓞 K] (M ⧸ P) := b • LinearMap.id
  have hf : ∀ x, f x = b • x := fun x => rfl
  have hmem : ∀ a ∈ 𝔟, ∃ u v : 𝓞 K, a = u * c + v * b := by
    intro a ha
    rw [← hbsup, Submodule.mem_sup] at ha
    obtain ⟨y, hy, z, hz, rfl⟩ := ha
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨u, v, rfl⟩
  have hbmem : b ∈ 𝔟 := hbsup ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  have e1 : {x : M ⧸ P // ∀ a ∈ 𝔟, a • x = 0} ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.1, by rw [LinearMap.mem_ker, hf]; exact x.2 b hbmem⟩
      invFun := fun x => ⟨x.1, fun a ha => by
        obtain ⟨u, v, rfl⟩ := hmem a ha
        have hx : b • (x.1 : M ⧸ P) = 0 := by rw [← hf]; exact x.2
        rw [add_smul, mul_smul, mul_smul, hcX, hx, smul_zero, smul_zero, add_zero]⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card ((M ⧸ P) ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have hker : Nat.card (LinearMap.ker f) = Nat.card ((M ⧸ P) ⧸ LinearMap.range f) := by
    rw [h3] at h1
    have h4 := h1.symm.trans h2
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; exact h4)
  have hPle : P ≤ 𝔟 • ⊤ := Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem 𝔟).2 hcb)
  have hrange : LinearMap.range f = Submodule.map P.mkQ (𝔟 • ⊤) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H m => exact ⟨b • m, Submodule.smul_mem_smul hbmem trivial, by simp [hf]⟩
    · rintro _ ⟨m, hm, rfl⟩
      refine Submodule.smul_induction_on (p := fun m => P.mkQ m ∈ LinearMap.range f) hm ?_ ?_
      · intro a ha n _
        obtain ⟨u, v, rfl⟩ := hmem a ha
        refine ⟨v • P.mkQ n, ?_⟩
        rw [hf, map_smul, add_smul, mul_smul, mul_smul, hcX, smul_zero, zero_add]
        exact smul_comm _ _ _
      · intro x y hx hy
        rw [map_add (f := _)]
        exact add_mem hx hy
  have hQ : Nat.card ((M ⧸ P) ⧸ LinearMap.range f) = Nat.card (M ⧸ (𝔟 • ⊤ : Submodule (𝓞 K) M)) := by
    rw [hrange]
    exact Nat.card_congr (Submodule.quotientQuotientEquivQuotient P (𝔟 • ⊤) hPle).toEquiv
  have hM := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (R := 𝓞 K) (N := M) 𝔟
  rw [Nat.card_congr e1, hker, hQ, hM, hd, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]

end GlobalTheory.TorsQuotCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKilledByIdealModIntEqAbsNormPowStatement

section

@[expose] public section

open scoped NumberField

theorem _root_.GlobalTheory.T.card_killed_by_ideal_mod_int_eq_absNorm_pow : ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M], Module.Free ℤ M → Module.Finite ℤ M → ∀ (r : ℕ), Module.finrank ℤ M = r * Module.finrank ℚ K → ∀ (𝔟 : Ideal (𝓞 K)) (c : ℕ), 0 < c → (c : 𝓞 K) ∈ 𝔟 → Nat.card {x : M ⧸ (Ideal.span {(c : 𝓞 K)} • (⊤ : Submodule (𝓞 K) M)) // ∀ a ∈ 𝔟, a • x = 0} = Ideal.absNorm 𝔟 ^ r := by
  first | (exact @GlobalTheory.TorsQuotCount.card_killed_eq) | (exact GlobalTheory.TorsQuotCount.card_killed_eq) | (intros; apply GlobalTheory.TorsQuotCount.card_killed_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCardKilledByIdealEqAbsNormPow

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HTTorsCount

theorem absNorm_pos_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
    (𝔟 : Ideal (𝓞 K)) (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) :
    0 < Ideal.absNorm 𝔟 ∧ (Ideal.absNorm 𝔟).Coprime p := by
  obtain ⟨β, hβ, z, hz, hsum⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top (x := (1 : 𝓞 K)))
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hpos : 0 < Ideal.absNorm 𝔟 := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    rintro rfl
    rw [Submodule.mem_bot] at hβ
    subst hβ
    rw [zero_add, _root_.mul_comm] at hsum
    have hu : IsUnit (p : 𝓞 K) := isUnit_iff_exists_inv.2 ⟨y, hsum⟩
    have e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [e, Algebra.norm_algebraMap, Int.isUnit_iff_natAbs_eq, Int.natAbs_pow, Int.natAbs_natCast] at hn
    rcases Nat.pow_eq_one.1 hn with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne' h1
  refine ⟨hpos, ?_⟩
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd => ?_))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd hpos
  have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hpos.ne'
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hd
  have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have h1 : Ideal.Quotient.mk 𝔟 y * (p : 𝓞 K ⧸ 𝔟) = 1 := by
    have := congrArg (Ideal.Quotient.mk 𝔟) hsum
    rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk 𝔟 y * (p : 𝓞 K ⧸ 𝔟)) * x := by rw [h1, _root_.one_mul]
      _ = 0 := by rw [_root_.mul_assoc, hpx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.out.one_lt.ne hx

theorem card_killedBy_eq_absNorm_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} = Ideal.absNorm 𝔟 ^ (D.m * D.n) := by
  intro p _ D R _ b N S s o 𝔟 h𝔟 k _ _ t
  obtain ⟨hcpos, hcop⟩ := absNorm_pos_coprime p 𝔟 h𝔟
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, spMap β = t ≫ s := ⟨(Spec.preimage (t ≫ s)).hom, Spec.map_preimage _⟩
  obtain ⟨I, -⟩ := o.geom k t β hβ.symm
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (a : 𝓞 D.F) (x : D.La), a • x = (algebraMap (𝓞 D.F) D.O a) • x := fun _ _ => rfl
  have hcnt := GlobalTheory.T.card_killed_by_ideal_mod_int_eq_absNorm_pow D.F D.La D.freeLa D.finLa (D.m * D.n) D.rankLa 𝔟 (Ideal.absNorm 𝔟) hcpos
    (Ideal.absNorm_mem 𝔟)
  rw [← hcnt]
  set c := Ideal.absNorm 𝔟 with hc
  set P : Submodule (𝓞 D.F) D.La := Ideal.span {(c : 𝓞 D.F)} • (⊤ : Submodule (𝓞 D.F) D.La) with hP
  have hmemP : ∀ x, x ∈ P ↔ ∃ y, x = c • y := by
    intro x
    rw [hP, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, by rw [hsmul, map_natCast, Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, Submodule.mem_top, by rw [hsmul, map_natCast, Nat.cast_smul_eq_nsmul]⟩
  let g : D.La → (Over.mk t ⟶ o.A) := I.ev c
  have hker : ∀ x, g x = 1 ↔ x ∈ P := fun x => by rw [hmemP]; exact I.ker c hcpos hcop x
  have hsub : ∀ x y, g (x - y) = g x * (g y)⁻¹ := fun x y =>
    eq_mul_inv_of_mul_eq (by rw [← I.add, sub_add_cancel])
  have hlin : ∀ (a : 𝓞 D.F) x, g (a • x) = g x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := fun a x => by
    rw [hsmul]; exact I.lin c _ x
  have hmap : 𝔟.map (algebraMap (𝓞 D.F) D.O) = Ideal.span (algebraMap (𝓞 D.F) D.O '' 𝔟) := rfl
  let f : D.La ⧸ P → (Over.mk t ⟶ o.A) := fun z => Quotient.liftOn' z g (fun x y hxy => by
    have h1 : g (x - y) = 1 := (hker _).2 ((Submodule.quotientRel_def P).1 hxy)
    rw [hsub] at h1
    exact mul_inv_eq_one.1 h1)
  have hf : ∀ x, f (Submodule.Quotient.mk x) = g x := fun _ => rfl
  have hkill : ∀ x, (∀ a ∈ 𝔟, a • (Submodule.Quotient.mk x : D.La ⧸ P) = 0) ↔
      GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) (g x) := by
    intro x
    rw [hmap, GlobalTheory.IwLevel.killedBy_span]
    constructor
    · rintro h _ ⟨a, ha, rfl⟩
      rw [GlobalTheory.IwLevel.htAct_act, ← hlin, hker, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact h a ha
    · intro h a ha
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hker, hlin]
      have := h _ ⟨a, ha, rfl⟩
      rwa [GlobalTheory.IwLevel.htAct_act] at this
  have hpow : ∀ (q : Over.mk t ⟶ o.A) (n : ℕ), q ≫ o.act.act (n : D.O) = q ^ n := by
    intro q n
    have h0 : o.act.act 0 = 1 := by
      have := o.act.add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    induction n with
    | zero => rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, o.act.add, o.act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]
  let F : {z : D.La ⧸ P // ∀ a ∈ 𝔟, a • z = 0} →
      {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} :=
    fun z => ⟨f z.1, by
      obtain ⟨z, hz⟩ := z
      induction z using Submodule.Quotient.induction_on with
      | H x => exact (hkill x).1 hz⟩
  refine (Nat.card_eq_of_bijective F ⟨?_, ?_⟩).symm
  · rintro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ h
    have h' : f z₁ = f z₂ := congrArg Subtype.val h
    induction z₁ using Submodule.Quotient.induction_on with
    | H x =>
    induction z₂ using Submodule.Quotient.induction_on with
    | H y =>
    rw [hf, hf] at h'
    apply Subtype.ext
    change Submodule.Quotient.mk x = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, ← hker, hsub, h', mul_inv_cancel]
  · rintro ⟨q, hq⟩
    have hq1 : q ^ c = 1 := by
      rw [← hpow, ← map_natCast (algebraMap (𝓞 D.F) D.O)]
      have := hq _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) (Ideal.absNorm_mem 𝔟))
      rwa [GlobalTheory.IwLevel.htAct_act] at this
    obtain ⟨x, hx⟩ := (I.onto c hcpos hcop q).1 hq1
    refine ⟨⟨Submodule.Quotient.mk x, (hkill x).2 (by change GlobalTheory.IwLevel.KilledBy _ _ (I.ev c x); rw [hx]; exact hq)⟩, Subtype.ext ?_⟩
    exact hx

end GlobalTheory.HTTorsCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCardKilledByIdealEqAbsNormPowStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.harrisTaylor_card_killed_by_ideal_eq_absNorm_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} = Ideal.absNorm 𝔟 ^ (D.m * D.n) := by
  first | (exact @GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow) | (exact GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow) | (intros; apply GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow <;> assumption)
end
end
