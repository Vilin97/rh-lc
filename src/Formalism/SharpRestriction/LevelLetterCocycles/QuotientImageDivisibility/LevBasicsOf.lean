module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvAtApply
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Formalism.SharpRestriction.LevelLetterCocycles.NatCastEqZeroOfNotDvd
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.RingTheory.PowerSeries.Binomial
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvROnePow
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasics

section

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def GenUnitsC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (s : ℕ) (u : ℤ_[l]ˣ),
    ((u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) → ((u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) →
      Subgroup.closure (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) = ⊤

section Parts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevBasics (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  inj : Function.Injective (algebraMap O F)
  hp : ((PD.p : ℕ) : F) ≠ 0
  root : ∃ ζ : F, IsPrimitiveRoot ζ (PD.p ^ (s + 1))
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ (ζ : Rs F PD.p s) (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ : Rs F PD.p s, ev ζ (letE a) = 1
  ev_π : ∀ ζ : Rs F PD.p s, ev ζ letπ = (ζ : F) - 1
  ev_ps : ∀ ζ : Rs F PD.p s, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ : Rs F PD.p s, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g (ζ : Rs F PD.p s) x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤

end Parts

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvAtPsIff

section

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Bs

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
  {F : Type} [Field F] [Algebra O F] [Algebra ℤ_[p] O] [IsDomain O] [CharZero O]

theorem evR_bs (s : ℕ) {x : F} (hx : Polynomial.aeval x (Zp (O := O) p (s + 1)) = 0) (ζ : F)
    (hxζ : x = ζ - 1) (z : ℤ_[p]) :
    evR p (s + 1) hlm hx (PowerSeries.binomialSeries O z) =
      ζ ^ (PadicInt.toZModPow (s + 1) z).val := by
  set A := (PadicInt.toZModPow (s + 1) z).val with hA
  have hker : z - (A : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ (s + 1)} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hA,
      ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hker
  have hz : z = (A : ℤ_[p]) + (((p ^ (s + 1) : ℕ)) : ℤ_[p]) * w := by
    push_cast; linear_combination -hw
  have hN : 1 ≤ p ^ (s + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  rw [hz, PowerSeries.binomialSeries_add, PowerSeries.binomialSeries_nat,
    ← Formalism.MainNotions.UnusedSlot80.LG.subst_bs (p ^ (s + 1)) hN w, map_mul, evR_onePow,
    show 1 + x = ζ by rw [hxζ]; ring]
  have h0 : Polynomial.aeval (0 : F) (Zp (O := O) p (s + 1)) = 0 := root_Zp p (s + 1) (by simp)
  have hsub := evR_subst p (s + 1) hlm hx h0 ((1 + PowerSeries.X) ^ (p ^ (s + 1)) - 1)
    (by simp) (evR_Zs p (s + 1) hlm hx) (PowerSeries.binomialSeries O w)
  rw [hsub, evR_eq_cc p (s + 1) hlm h0 rfl, PowerSeries.binomialSeries_constantCoeff, map_one, mul_one]

end Bs

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    [IsDomain O] [CharZero O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F]

theorem evAt_ps (a : ZMod n) (s t : ℕ) (ζ : Rs F PD.p s) :
    ∃ hy : Polynomial.aeval ((ζ : F) ^ (PD.p ^ t) - 1) (Zp (O := O) PD.p (s + 1)) = 0,
      evAt hlm F a s ζ (ps W t) =
        evR PD.p (s + 1) hlm hy (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have hy : Polynomial.aeval ((ζ : F) ^ (PD.p ^ t) - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  refine ⟨hy, ?_⟩
  have hφ := Formalism.MainNotions.UnusedSlot80.LG.phi_pow_X W.φ₀ PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W) t
  have h0 : PowerSeries.constantCoeff ((W.φ₀ ^ t) PowerSeries.X) = 0 := by rw [hφ]; simp
  rw [evAt_apply, Formalism.MainNotions.UnusedSlot80.LG.ps_apply W t a, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst _ h0, hφ]
  refine evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hy _ (by simp) ?_ _
  rw [map_sub, evR_onePow, map_one, add_sub_cancel]

theorem evAt_ps_iff (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [CharZero F] (a : ZMod n) (s t : ℕ)
    (ζ : Rs F PD.p s) : evAt hlm F a s ζ (ps W t) = 0 ↔ t = s := by
  obtain ⟨hy, he⟩ := evAt_ps W hlm F a s t ζ
  rw [he, ev_qp W hlm F hR s hy, add_sub_cancel]
  have hζ : IsPrimitiveRoot (ζ : F) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hp1 : 1 < PD.p := hpF.out.one_lt
  constructor
  · rintro ⟨hne, hpow⟩
    by_contra hts
    rcases Nat.lt_or_gt_of_ne hts with h | h
    ·
      have hprim := hζ.pow_of_dvd (pow_ne_zero t hpF.out.ne_zero)
        (pow_dvd_pow PD.p (by omega : t ≤ s + 1))
      rw [Nat.pow_div (by omega) hpF.out.pos] at hprim
      have hd := hprim.dvd_of_pow_eq_one PD.p hpow
      have h1 := Nat.le_of_dvd hpF.out.pos hd
      have h2 : PD.p ^ 2 ≤ PD.p ^ (s + 1 - t) := Nat.pow_le_pow_right hpF.out.pos (by omega)
      have h3 : PD.p < PD.p ^ 2 := by nlinarith
      omega
    ·
      apply hne
      rw [sub_eq_zero]
      obtain ⟨k, hk⟩ : PD.p ^ (s + 1) ∣ PD.p ^ t := pow_dvd_pow PD.p (by omega)
      rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  · rintro rfl
    have hprim := hζ.pow_of_dvd (pow_ne_zero t hpF.out.ne_zero)
      (pow_dvd_pow PD.p (by omega : t ≤ t + 1))
    rw [Nat.pow_div (by omega) hpF.out.pos, show t + 1 - t = 1 by omega, pow_one] at hprim
    exact ⟨sub_ne_zero.2 (hprim.ne_one hp1), hprim.pow_eq_one⟩

end Main

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasicsOf

section

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Fin

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    [IsDomain O] [CharZero O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F] [Algebra ℤ_[PD.p] O]

theorem evAt_γ (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O)) (a : ZMod n) (s : ℕ)
    (g : W.Gam) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ (W.γA g x) = evAt hlm F a s (powR F PD.p s (redU PD.p s (z g)) ζ) x := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have h0 := (W.γ₀_X g).1
  have h1 : PowerSeries.coeff 1 (W.γ₀ g PowerSeries.X) = algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) := by
    rw [(W.γ₀_X g).2, hz g]
  have hbs := Formalism.MainNotions.UnusedSlot80.LG.aut_eq_bs W.φ₀ (W.γ₀ g) PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W)
    (fun a => W.γ₀_comm g a) h0 (z g : ℤ_[PD.p]) h1
  set A := (PadicInt.toZModPow (s + 1) (z g : ℤ_[PD.p])).val with hA
  have hyA : Polynomial.aeval ((ζ : F) ^ A - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  rw [evAt_apply, evAt_apply]
  have e1 : (W.γA g x) a = W.γ₀ g (x a) := rfl
  have huy : evR PD.p (s + 1) hlm (rs_root F s ζ) (W.γ₀ g PowerSeries.X) = (ζ : F) ^ A - 1 := by
    have e : W.γ₀ g PowerSeries.X = PowerSeries.binomialSeries O (z g : ℤ_[PD.p]) - 1 := by
      rw [← hbs]; ring
    rw [e, map_sub, evR_bs PD.p hlm s (rs_root F s ζ) (ζ : F) rfl, map_one]
  rw [e1, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst (W.γ₀ g) h0,
    evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hyA _ h0 huy]
  exact evR_congr PD.p (s + 1) hlm hyA _ rfl _


omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in
theorem gen_of (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert (redU PD.p s (z W.gam))
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ := by
  obtain ⟨z0, hz0, hv⟩ := hγz
  have hzg : z W.gam = z0 := Units.ext (hZinj (by rw [hz, hz0]))
  have hne : (z0 : ℤ_[PD.p]) - 1 ≠ 0 := by
    intro h; rw [h, PadicInt.valuation_zero] at hv; exact zero_ne_one hv
  have hu1 : (z0 : ℤ_[PD.p]) - 1 ∈ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p])} := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by rw [hv])
    rwa [pow_one] at this
  have hu2 : (z0 : ℤ_[PD.p]) - 1 ∉ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p]) ^ 2} := by
    intro h
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 2).1 h
    rw [hv] at this; omega
  have htop := hGen PD.p hp2 s z0 hu1 hu2

  have hl2 := hpF.out.two_le
  obtain ⟨H, hH⟩ : ∃ H : Subgroup W.Gam, (H : Set W.Gam) = ↑W.DelF := ⟨
    { carrier := ↑W.DelF
      mul_mem' := by
        intro a b ha hb
        simp only [Finset.mem_coe, W.DelF_def] at ha hb ⊢
        obtain ⟨k, hk, hak⟩ := ha
        obtain ⟨k', hk', hbk⟩ := hb
        exact ⟨k * k', Nat.mul_pos hk hk', by
          rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbk, one_pow]⟩
      one_mem' := by
        simp only [Finset.mem_coe, W.DelF_def]
        exact ⟨1, one_pos, one_pow _⟩
      inv_mem' := by
        intro a ha
        simp only [Finset.mem_coe, W.DelF_def] at ha ⊢
        obtain ⟨k, hk, hak⟩ := ha
        exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩ }, rfl⟩
  have memH : ∀ x, x ∈ H ↔ x ∈ W.DelF := fun x => by
    rw [← SetLike.mem_coe, hH, Finset.mem_coe]
  have hHcard : Nat.card H = PD.p - 1 := by
    rw [← hcard, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight memH)
  have hexp : ∀ δ ∈ W.DelF, δ ^ (PD.p - 1) = 1 := by
    intro δ hδ
    have h : (⟨δ, (memH δ).mpr hδ⟩ : H) ^ (PD.p - 1) = 1 := by
      rw [← hHcard]
      exact pow_card_eq_one'
    have h2 := congrArg (fun y : H => (y : W.Gam)) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2

  have hzΔ : ∀ δ : ↥W.DelF, (z δ) ^ (PD.p - 1) = 1 := by
    intro δ
    apply Units.ext
    apply hZinj
    rw [Units.val_pow_eq_pow_val, map_pow, hz, ← Units.val_pow_eq_pow_val, ← map_pow,
      hexp δ δ.2, map_one]
    simp
  let zΔ : ↥W.DelF → DeltaT PD.p := fun δ => ⟨z δ, hzΔ δ⟩
  have hinj : Function.Injective zΔ := by
    intro δ δ' h
    have h1 : z δ = z δ' := congrArg Subtype.val h
    have h2 : W.χΓ δ = W.χΓ δ' := Units.ext (by rw [← hz, ← hz, h1])
    exact Subtype.ext (W.χΓ_inj h2)
  haveI : NeZero (PD.p - 1) := ⟨by omega⟩
  let e : DeltaT PD.p ≃ ↥(rootsOfUnity (PD.p - 1) ℤ_[PD.p]) :=
    Equiv.subtypeEquivRight fun x => (mem_rootsOfUnity (PD.p - 1) x).symm
  haveI : Finite (DeltaT PD.p) := Finite.of_equiv _ e.symm
  have hle : Nat.card (DeltaT PD.p) ≤ Nat.card ↥W.DelF := by
    rw [Nat.card_congr e, Nat.card_eq_finsetCard, hcard]
    exact card_rootsOfUnity ℤ_[PD.p] (PD.p - 1)
  have hsurj := (hinj.bijective_of_nat_card_le hle).2
  rw [eq_top_iff, ← htop]
  apply Subgroup.closure_mono
  intro u hu
  rcases Set.mem_insert_iff.1 hu with rfl | ⟨d, rfl⟩
  · exact Set.mem_insert_iff.2 (Or.inl (by rw [hzg]))
  · obtain ⟨δ, hδ⟩ := hsurj d
    refine Set.mem_insert_of_mem _ ⟨δ, δ.2, ?_⟩
    show redU PD.p s (z δ) = redU PD.p s d.1
    rw [← hδ]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in
theorem gen_of' (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert ((fun g => redU PD.p s (z g)) W.gam)
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ :=
  gen_of W z hz hZinj hγz hcard hp2 hGen s

def levBasics_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [IsAlgClosed F] [CharZero F]
    (hinjF : Function.Injective (algebraMap O F))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hχ : ∀ g : W.Gam, ∃ z : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z : ℤ_[PD.p]) = (W.χΓ g : O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (a : ZMod n) (s : ℕ) :
    LevBasics W a s where
  F := F
  fF := inferInstance
  algOF := inferInstance
  inj := hinjF
  hp := Nat.cast_ne_zero.2 hpF.out.ne_zero
  root := exists_prim _ (pow_pos hpF.out.pos _)
  ev := evAt hlm F a s
  ev_O ζ x := by
    rw [evAt_apply]
    exact (evR PD.p (s + 1) hlm (rs_root F s ζ)).commutes x
  ev_letE ζ := by
    rw [evAt_apply]
    simp [letE]
  ev_π ζ := by
    rw [evAt_apply]
    exact evR_X PD.p (s + 1) hlm (rs_root F s ζ)
  ev_ps ζ := (evAt_ps_iff W hlm F hR a s s ζ).2 rfl
  ev_pt t ht ζ := fun h => ht ((evAt_ps_iff W hlm F hR a s t ζ).1 h)
  σ g := redU PD.p s (Classical.choose (hχ g))
  ev_γ g ζ x := evAt_γ W hlm F (fun g => Classical.choose (hχ g))
    (fun g => Classical.choose_spec (hχ g)) a s g ζ x
  gen := gen_of' W (fun g => Classical.choose (hχ g)) (fun g => Classical.choose_spec (hχ g))
    hZinj hγz hcard hp2 hGen s

end Fin

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end
end
