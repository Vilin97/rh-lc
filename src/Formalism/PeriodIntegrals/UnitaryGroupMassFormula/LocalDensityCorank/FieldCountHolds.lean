module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.SplitCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramCondIff
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensInert
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CardCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalDensityIntegral
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ResidueFieldCount
import Mathlib.Tactic.Linter.Style
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlbHZeroRight

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

theorem flb_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  exact (L.O_def _).2 isIntegral_algebraMap

theorem flb_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  exact (L.O_def _).2 (((L.O_def x).1 hx).map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F]))

theorem flb_pid {E : Type} [CommRing E] (S : Subring E) (p : E) (hp : p ∈ S)
    (hfac : ∀ x ∈ S, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ S, (∃ w ∈ S, u * w = 1) ∧ x = p ^ k * u) :
    IsPrincipalIdealRing S := by
  classical
  refine ⟨fun I => ?_⟩
  have hget : ∀ x : S, x ∈ I → ∀ (j : ℕ) (u : E), u ∈ S → (∃ w ∈ S, u * w = 1) →
      (x : E) = p ^ j * u → (⟨p, hp⟩ : S) ^ j ∈ I := by
    rintro x hxI j u hu ⟨w, hw, huw⟩ hxe
    have h : (⟨p, hp⟩ : S) ^ j = x * ⟨w, hw⟩ := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_assoc, huw, mul_one]
    rw [h]
    exact I.mul_mem_right _ hxI
  by_cases hI : ∃ x ∈ I, x ≠ 0
  · have hex : ∃ k : ℕ, (⟨p, hp⟩ : S) ^ k ∈ I := by
      obtain ⟨x, hxI, hx0⟩ := hI
      obtain ⟨k, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      exact ⟨k, hget x hxI k u hu huw hxe⟩
    refine ⟨⟨(⟨p, hp⟩ : S) ^ Nat.find hex, ?_⟩⟩
    apply le_antisymm
    · intro x hxI
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      obtain ⟨j, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      have hkj : Nat.find hex ≤ j := Nat.find_min' hex (hget x hxI j u hu huw hxe)
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      refine ⟨(⟨p, hp⟩ : S) ^ (j - Nat.find hex) * ⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_comm, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkj]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact Nat.find_spec hex
  · push Not at hI
    refine ⟨⟨0, ?_⟩⟩
    rw [Submodule.span_singleton_eq_bot.mpr rfl]
    exact (Submodule.eq_bot_iff I).mpr hI

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem flb_h_add_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem flb_h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x : V) (a : E) (y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem flb_h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (x : V) (c : ι → E) (v : ι → V) :
    H.h x (∑ i, c i • v i) = ∑ i, M.L.cj (c i) * H.h x (v i) := by
  have hs := map_sum (AddMonoidHom.mk' (H.h x) (flb_h_add_right H x)) (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => flb_h_smul_right H x (c i) (v i)

theorem flb_h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (y : V) (c : ι → E) (v : ι → V) :
    H.h (∑ i, c i • v i) y = ∑ i, c i * H.h (v i) y := by
  have hs := map_sum (AddMonoidHom.mk' (fun z => H.h z y) (fun a b => H.h_add_left a b y))
    (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => H.h_smul_left (c i) (v i) y

end Herm

end PI.UnitaryGroupMassFormula.CntFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlatBasisOf

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

theorem flb_main {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hnt : Nontrivial E)
    (hden : ∀ x : E, ∃ s ∈ M.L.O, s ≠ 0 ∧ s * x ∈ M.L.O)
    (hpid : IsPrincipalIdealRing M.L.O)
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ) :
      ∃ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) ∧ LinearIndependent E b ∧
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) ∧
        ∃ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) ∧
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1 := by
  classical
  haveI : NoZeroDivisors E := ⟨fun {a b} hab => by
    by_contra hne
    push_neg at hne
    obtain ⟨u, hu⟩ := hE a hne.1
    apply hne.2
    have h2 := congrArg (fun t => (↑u⁻¹ : E) * t) hab
    simp only [mul_zero, ← mul_assoc] at h2
    rwa [← hu, Units.inv_mul, one_mul] at h2⟩
  haveI : IsDomain E := NoZeroDivisors.to_isDomain E
  obtain ⟨hfg, hspan, hdual⟩ := hΛ
  haveI : Module.Finite M.L.O Λ := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors M.L.O Λ := ⟨fun {r x} h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hr' : (r : E) ≠ 0 := fun h0 => hr (Subtype.ext h0)
    obtain ⟨u, hu⟩ := hE _ hr'
    have h1 : (r : E) • (x : V) = 0 := by
      have := congrArg Subtype.val h
      simpa [Submodule.coe_smul, Subring.smul_def] using this
    apply Subtype.ext
    have h2 := congrArg (fun v => (↑u⁻¹ : E) • v) h1
    simp only [smul_zero, smul_smul] at h2
    rw [← hu, Units.inv_mul, one_smul] at h2
    simpa using h2⟩
  haveI : Module.Free M.L.O Λ := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis M.L.O Λ
  let bb : Module.Free.ChooseBasisIndex M.L.O Λ → V := fun i => (B i : V)
  have hexp : ∀ (x : V) (hx : x ∈ Λ), x = ∑ i, ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i := by
    intro x hx
    have h2 := congrArg Subtype.val (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def] at h2
    exact h2.symm
  have hli : LinearIndependent E bb := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose s hsO hs using fun j => hden (g j)
    set t := ∏ j, s j with ht
    have htO : t ∈ M.L.O := Subring.prod_mem _ fun j _ => hsO j
    have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hs j).1
    have htg : ∀ j, t * g j ∈ M.L.O := by
      intro j
      have e : t * g j = (∏ j' ∈ Finset.univ.erase j, s j') * (s j * g j) := by
        rw [ht, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
        ring
      rw [e]
      exact M.L.O.mul_mem (Subring.prod_mem _ fun j' _ => hsO j') (hs j).2
    let g' : Module.Free.ChooseBasisIndex M.L.O Λ → M.L.O := fun j => ⟨t * g j, htg j⟩
    have hsum : ∑ j, g' j • B j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subring.smul_def, Submodule.coe_zero]
      have : ∑ j, (t * g j) • bb j = t • ∑ j, g j • bb j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
      simpa [g', bb, hg] using this
    have h0 := Fintype.linearIndependent_iff.mp B.linearIndependent g' hsum i
    have h0' : t * g i = 0 := congrArg Subtype.val h0
    exact (mul_eq_zero.mp h0').resolve_left ht0
  have hsp : ⊤ ≤ Submodule.span E (Set.range bb) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rw [hexp x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let BE := Basis.mk hli hsp
  have hcard : Module.finrank E V = Fintype.card (Module.Free.ChooseBasisIndex M.L.O Λ) :=
    Module.finrank_eq_card_basis BE
  let eι := Fintype.equivFinOfCardEq hcard.symm
  let b : Fin (Module.finrank E V) → V := fun k => bb (eι.symm k)
  have hbΛ : ∀ k, b k ∈ Λ := fun k => (B (eι.symm k)).2
  have hlib : LinearIndependent E b := hli.comp _ eι.symm.injective
  have hexpb : ∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧
      x = ∑ k, c k • b k := by
    intro x hx
    refine ⟨fun k => ((B.repr ⟨x, hx⟩ (eι.symm k) : M.L.O) : E), fun k => Subtype.property _, ?_⟩
    exact (hexp x hx).trans
      (Equiv.sum_comp eι.symm (fun i => ((B.repr ⟨x, hx⟩ i : M.L.O) : E) • bb i)).symm
  refine ⟨b, hbΛ, hlib, hexpb, ?_⟩
  set G : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E :=
    Matrix.of (fun k l => H.h (b k) (b l)) with hG
  have hdet0 : G.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    set x := ∑ k, v k • b k with hx
    have hxb : ∀ l, H.h x (b l) = 0 := by
      intro l
      rw [hx, flb_h_sum_left]
      have := congrFun hv l
      simpa [Matrix.vecMul, dotProduct, hG] using this
    have hx0 : x = 0 := by
      apply H.nondeg
      intro y
      have hy := BE.sum_repr y
      rw [← hy, flb_h_sum_right]
      apply Finset.sum_eq_zero
      intro i _
      have : BE i = b (eι i) := by simp [BE, b]
      rw [this, hxb, mul_zero]
    apply hv0
    funext k
    exact Fintype.linearIndependent_iff.mp hlib v hx0.symm.symm k
  have hdet : IsUnit G.det := hE _ hdet0
  refine ⟨G⁻¹, ?_, Matrix.nonsing_inv_mul G hdet⟩
  have hQG := Matrix.nonsing_inv_mul G hdet
  intro k m
  set d := ∑ m', G⁻¹ k m' • b m' with hd
  have hdb : ∀ l, H.h d (b l) = if k = l then 1 else 0 := by
    intro l
    rw [hd, flb_h_sum_left]
    have := congrFun (congrFun hQG k) l
    simpa [Matrix.mul_apply, hG, Matrix.one_apply] using this
  have hdΛ : d ∈ Λ := by
    rw [hdual]
    intro y hy
    obtain ⟨c, hcO, rfl⟩ := hexpb y hy
    rw [flb_h_sum_right]
    simp only [hdb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact flb_cj_mem M.L (hcO k)
  obtain ⟨c', hc'O, hc'⟩ := hexpb d hdΛ
  have hz : ∑ m', (G⁻¹ k m' - c' m') • b m' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hd, ← hc', sub_self]
  have := Fintype.linearIndependent_iff.mp hlib _ hz m
  rw [sub_eq_zero.mp this]
  exact hc'O m

theorem flatBasis_of (h1 : FLocO) : FLatBasis := by
  intro F E _ _ _ _ _ _ _ M hF hc hE V _ _ H Λ hΛ
  haveI := hF
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hden0, hfac⟩ := h1 F E M.L hF hc hE ϖ hϖ
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  refine flb_main M hE hnt ?_ (flb_pid M.L.O _ (flb_int_mem M.L ϖ) hfac) V H Λ hΛ
  intro x
  obtain ⟨c, hc0, hcx⟩ := hden0 x
  refine ⟨_, flb_int_mem M.L c, ?_, hcx⟩
  have hcF : (c : F) ≠ 0 := by exact_mod_cast hc0
  exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hcF

end PI.UnitaryGroupMassFormula.CntFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.FieldCountHolds

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

open Formalism.MainNotions.S ValuativeRel PI.UnitaryGroupMassFormula.CntFormula
open Classical

theorem fld_dvd_iff {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (a : 𝒪[F]) :
    (∃ z ∈ L.O, algebraMap F E (a : F) = algebraMap F E (ϖ : F) * z) ↔ ϖ ∣ a := by
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · rintro ⟨z, hz, he⟩
    have hz' : z = algebraMap F E ((a : F) / ϖ) := by
      rw [div_eq_mul_inv, map_mul, he, mul_comm (algebraMap F E (ϖ : F)) z, mul_assoc, ← map_mul,
        mul_inv_cancel₀ hϖ0, map_one, mul_one]
    have hm : (a : F) / ϖ ∈ 𝒪[F] :=
      PI.UnitaryGroupMassFormula.CntFormula.fl_mem_int L (PI.UnitaryGroupMassFormula.CntFormula.fl_inj L) (hz' ▸ hz)
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    show (a : F) = (ϖ : F) * ((a : F) / ϖ)
    field_simp
  · rintro ⟨c, rfl⟩
    exact ⟨algebraMap F E (c : F), PI.UnitaryGroupMassFormula.CntFormula.fl_int_mem L c, by simp [map_mul]⟩

theorem fld_count_core {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) (hl : IsNonarchimedeanLocalField F)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u)
    (k : Type) [Field k] [Fintype k] (r : M.L.O →+* k) (hsurj : Function.Surjective r)
    (hker : ∀ x : M.L.O, r x = 0 ↔ ∃ z ∈ M.L.O, (x : E) = algebraMap F E ϖ * z)
    (hcard : Fintype.card k = Nat.card 𝓀[F] ^ 2)
    (hfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ Nat.card 𝓀[F])
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ)
    (b : Fin (Module.finrank E V) → V) (hbΛ : ∀ k, b k ∈ Λ) (hbind : LinearIndependent E b)
    (hbcrd : ∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k)
    (Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E) (hQO : ∀ k l, Q k l ∈ M.L.O)
    (hQ : Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]) :
    H.dens ϖ Λ (Matrix.diagonal (fun i => algebraMap F E (a i : F))) =
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (-1)
        (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card := by
  have := hl
  set G₀ : Matrix ι ι E := Matrix.diagonal (fun i => algebraMap F E (a i : F)) with hG₀
  have hG1 : ∀ x y, G₀ x y ∈ M.L.O := by
    intro x y
    by_cases h : x = y
    · subst h; rw [hG₀, Matrix.diagonal_apply_eq]; exact fl_int_mem M.L (a x)
    · rw [hG₀, Matrix.diagonal_apply_ne _ h]; exact M.L.O.zero_mem
  have hG2 : ∀ x y, G₀ y x = M.L.cj (G₀ x y) := by
    intro x y
    by_cases h : x = y
    · subst h; rw [hG₀, Matrix.diagonal_apply_eq, M.L.cj.commutes]
    · rw [hG₀, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), map_zero]
  have hR : FC.RedData ϖ k r (Module.finrank E V) b Λ := ⟨hker, hsurj, hbΛ, hbind, hbcrd⟩
  have hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O := fun i j => (hΛ.2.2 (b i)).1 (hbΛ i) (b j) (hbΛ j)
  have hS := FC.card_count hR H hϖ o2 o3 hint (Nat.card 𝓀[F]) hfrob G₀ hG1
  let _ : Fintype 𝓀[F] := Fintype.ofFinite _
  have hqF : Fintype.card 𝓀[F] = Nat.card 𝓀[F] := Nat.card_eq_fintype_card.symm
  let ψ : 𝒪[F] →+* M.L.O := RingHom.codRestrict ((algebraMap F E).comp (𝒪[F]).subtype) M.L.O
    (fun c => FC.algO c)
  let φ0 : 𝒪[F] →+* k := r.comp ψ
  have hker0 : ∀ a ∈ IsLocalRing.maximalIdeal 𝒪[F], φ0 a = 0 := by
    intro a ha
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have h0 : r (ψ ϖ) = 0 := (hker _).2 ⟨1, M.L.O.one_mem, by
      show algebraMap F E (ϖ : F) = _
      rw [mul_one]⟩
    simp only [φ0, RingHom.comp_apply, map_mul, h0, mul_zero]
  let ι0 : 𝓀[F] →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[F]) φ0 hker0
  let _ : Algebra 𝓀[F] k := ι0.toAlgebra
  have hfin : Module.finrank 𝓀[F] k = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := 𝓀[F]) (V := k)
    rw [hcard, ← hqF] at h1
    exact (Nat.pow_right_injective (Fintype.one_lt_card (α := 𝓀[F]))).eq_iff.1 h1.symm
  let QO : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) M.L.O := fun i j => ⟨Q i j, hQO i j⟩
  let GO : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) M.L.O :=
    fun i j => ⟨H.h (b i) (b j), hint i j⟩
  have hQG : QO * GO = 1 := by
    have e1 : QO.map M.L.O.subtype = Q := by ext i j; rfl
    have e2 : GO.map M.L.O.subtype = Matrix.of fun k l => H.h (b k) (b l) := by ext i j; rfl
    apply Matrix.map_injective (f := M.L.O.subtype) Subtype.val_injective
    simp only
    rw [Matrix.map_mul, e1, e2, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPh : IsUnit (FC.Ph r H b hint).det := by
    have h2 : (QO.map r) * (GO.map r) = 1 := by
      rw [← Matrix.map_mul, hQG, Matrix.map_one _ (map_zero r) (map_one r)]
    exact Matrix.isUnit_det_of_left_inverse h2
  have hPhH : ∀ i j, FC.Ph r H b hint j i = FC.Ph r H b hint i j ^ Fintype.card 𝓀[F] := by
    intro i j
    rw [hqF]
    exact hfrob ⟨H.h (b i) (b j), hint i j⟩ ⟨H.h (b j) (b i), hint j i⟩ (H.h_herm (b i) (b j))
  set m := Fintype.card ι
  let e := Fintype.equivFin ι
  let Gm : Matrix (Fin m) (Fin m) k := fun i j => r ⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩
  have hGmH : ∀ i j, Gm j i = Gm i j ^ Fintype.card 𝓀[F] := by
    intro i j
    rw [hqF]
    exact hfrob ⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩ ⟨G₀ (e.symm i) (e.symm j), hG1 _ _⟩
      (hG2 (e.symm j) (e.symm i))

  let d : Fin m → k := fun i => r ⟨algebraMap F E (a (e.symm i) : F), fl_int_mem M.L _⟩
  have hGmd : Gm = Matrix.diagonal d := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      exact congrArg r (Subtype.ext (show G₀ (e.symm i) (e.symm i) = _ from Matrix.diagonal_apply_eq _ _))
    · rw [Matrix.diagonal_apply_ne _ h]
      have hne : e.symm j ≠ e.symm i := fun h' => h (e.symm.injective h').symm
      exact (congrArg r (Subtype.ext (show G₀ (e.symm j) (e.symm i) = 0 from Matrix.diagonal_apply_ne _ hne) :
        (⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩ : M.L.O) = 0)).trans (map_zero r)
  have hd0 : ∀ i, d i = 0 ↔ ϖ ∣ a (e.symm i) := by
    intro i
    rw [hker]
    exact fld_dvd_iff M.L hϖ _
  have hrank : m - Gm.rank = (Finset.univ.filter fun i => ϖ ∣ a i).card := by
    have hc := Fintype.card_subtype_compl (fun i : Fin m => d i ≠ 0)
    rw [Fintype.card_fin] at hc
    rw [hGmd, Matrix.rank_diagonal, ← hc]
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr ((Equiv.subtypeEquiv e.symm fun i => ?_))
    rw [← hd0]
    exact not_not
  have hT : Nat.card {X : ι → Fin (Module.finrank E V) → k // LinearIndependent k X ∧
      ∀ a a', ∑ i, ∑ j, X a' i * FC.Ph r H b hint i j * X a j ^ Nat.card 𝓀[F] = r ⟨G₀ a a', hG1 a a'⟩} =
      Formalism.L2.SG.DensExact.countInert 𝓀[F] k (Module.finrank E V) m (FC.Ph r H b hint) Gm := by
    unfold Formalism.L2.SG.DensExact.countInert
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl _)) fun X => ?_)
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Set.mem_ofPred_eq, hqF]
    refine and_congr (linearIndependent_equiv e.symm).symm ⟨fun h i j => h (e.symm j) (e.symm i), fun h a a' => ?_⟩
    have := h (e a') (e a)
    simpa [Gm] using this
  have hD := density_exact_inert 𝓀[F] k hfin (Module.finrank E V) m (FC.Ph r H b hint) Gm hPh hPhH hGmH
  rw [hrank, hqF] at hD
  unfold Loc.HermSp.dens
  rw [hS, hT, ← hD]
  congr 1
  have hq0 : (Nat.card 𝓀[F] : ℝ) ≠ 0 := by
    rw [← hqF]; exact_mod_cast Fintype.card_ne_zero
  rw [show ((2 * Module.finrank E V * m : ℤ) - (m : ℤ) ^ 2) =
      ((2 * Module.finrank E V * m : ℕ) : ℤ) - ((m ^ 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_sub₀ hq0, zpow_natCast, zpow_natCast]

theorem fieldCount_holds : FieldCount := by
  intro F E _ _ _ _ _ _ _ M hl hc hE V _ _ H Λ hΛ ϖ hϖ ι _ _ a _
  obtain ⟨_, o2, o3⟩ := local_density_integral F E M.L hl hc hE ϖ hϖ
  obtain ⟨rmax, rcard, rfrob⟩ := residue_field_count F E M.L hl hc hE ϖ hϖ
  obtain ⟨b, hb1, hb2, hb3, Q, hQ1, hQ2⟩ := flatBasis_of local_density_integral F E M hl hc hE V H Λ hΛ
  let _ : Field (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := Ideal.Quotient.field _
  have hq : 0 < Nat.card 𝓀[F] := Nat.card_pos
  have : Finite (M.L.O ⧸ Ideal.span {piO M.L ϖ}) :=
    Nat.finite_of_card_ne_zero (by rw [rcard]; positivity)
  let _ : Fintype (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := Fintype.ofFinite _
  refine fld_count_core M hl ϖ hϖ o2 o3 (M.L.O ⧸ Ideal.span {piO M.L ϖ})
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective ?_ ?_ rfrob V H Λ hΛ b hb1 hb2 hb3 Q hQ1 hQ2 ι a
  · intro x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, by rw [← hc]; simp [piO, mul_comm]⟩
    · rintro ⟨z, hz, he⟩
      exact ⟨⟨z, hz⟩, Subtype.ext (by simp [piO, he, mul_comm])⟩
  · rw [Fintype.card_eq_nat_card, rcard]

end PI.UnitaryGroupMassFormula.LocDensCorank
end
end
end
