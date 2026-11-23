module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Polynomial.Div
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorLiftOfIsAdicCompleteStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomPowerSeriesOfRankOneImageStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingletonStatement
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanSingletonClosedOfBoundedTorsion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqOfSubMemStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesRingHomOfIsAdicComplete

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.PowerSeriesEval

theorem mk_eval₂_trunc_coe {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) {K : ℕ} (hK : v ^ K ∈ I) (p : Polynomial W) :
    Ideal.Quotient.mk I ((PowerSeries.trunc K (p : W⟦X⟧)).eval₂ ω v) =
      Ideal.Quotient.mk I (p.eval₂ ω v) := by
  have hdvd : (Polynomial.X : Polynomial W) ^ K ∣ p - PowerSeries.trunc K (p : W⟦X⟧) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  generalize PowerSeries.trunc K (p : W⟦X⟧) = t at hq ⊢
  have hp : p = t + Polynomial.X ^ K * q := by
    rw [← hq]; ring
  rw [Ideal.Quotient.eq, hp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
  have : t.eval₂ ω v - (t.eval₂ ω v + v ^ K * q.eval₂ ω v) = -(v ^ K * q.eval₂ ω v) := by ring
  rw [this]
  exact I.neg_mem (I.mul_mem_right _ hK)

noncomputable def truncEval {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) (K : ℕ) (hK : v ^ (K + 1) ∈ I) : W⟦X⟧ →+* C ⧸ I where
  toFun f := Ideal.Quotient.mk I ((PowerSeries.trunc (K + 1) f).eval₂ ω v)
  map_one' := by simp
  map_mul' f g := by
    rw [← PowerSeries.trunc_trunc_mul_trunc, ← Polynomial.coe_mul, mk_eval₂_trunc_coe ω v I hK,
      Polynomial.eval₂_mul, map_mul]
  map_zero' := by simp
  map_add' f g := by simp [Polynomial.eval₂_add]

theorem truncEval_apply {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) (K : ℕ) (hK : v ^ (K + 1) ∈ I) (f : W⟦X⟧) :
    truncEval ω v I K hK f = Ideal.Quotient.mk I ((PowerSeries.trunc (K + 1) f).eval₂ ω v) := rfl

end GlobalTheory.PowerSeriesEval

open GlobalTheory.PowerSeriesEval in
theorem GlobalTheory.PowerSeriesEval.exists_ringHom_powerSeries :
    ∀ (W : Type) [CommRing W] (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C →
      ∀ (ω : W →+* C) (v : C) (e : ℕ), v ^ e ∈ J →
        ∃ σ : W⟦X⟧ →+* C, (∀ w, σ (PowerSeries.C w) = ω w) ∧ σ X = v := by
  intro W _ C _ J hJ ω v e he

  have hN : v ^ (e + 1) ∈ J := by rw [pow_succ]; exact J.mul_mem_right _ he
  have hK : ∀ n : ℕ, v ^ ((e + 1) * n + 1) ∈ J ^ n := fun n => by
    rw [pow_succ, pow_mul]
    exact (J ^ n).mul_mem_right _ (Ideal.pow_mem_pow hN n)
  let f : (n : ℕ) → W⟦X⟧ →+* C ⧸ J ^ n := fun n => truncEval ω v (J ^ n) ((e + 1) * n) (hK n)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (f n) = f m := by
    intro m n hle
    ext g
    simp only [f, RingHom.comp_apply, truncEval_apply, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [← mk_eval₂_trunc_coe ω v (J ^ m) (hK m),
      PowerSeries.trunc_trunc_of_le _ (Nat.succ_le_succ (Nat.mul_le_mul_left _ hle))]
  refine ⟨IsAdicComplete.liftRingHom J f hf, fun w => ?_, ?_⟩
  · have := IsHausdorff.funext' (R := Unit) J (f := fun _ => IsAdicComplete.liftRingHom J f hf (PowerSeries.C w))
      (g := fun _ => ω w) (fun n _ => by
        rw [IsAdicComplete.mk_liftRingHom]
        simp [f, truncEval_apply])
    exact congrFun this ()
  · have := IsHausdorff.funext' (R := Unit) J (f := fun _ => IsAdicComplete.liftRingHom J f hf X)
      (g := fun _ => v) (fun n _ => by
        rw [IsAdicComplete.mk_liftRingHom]
        simp only [f, truncEval_apply]
        rcases n with _ | n
        · rw [Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
        · rw [PowerSeries.trunc_X_of (Nat.succ_le_succ (Nat.mul_pos (Nat.succ_pos e) (Nat.succ_pos n))),
            Polynomial.eval₂_X])
    exact congrFun this ()
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesRingHomOfIsAdicCompleteStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_powerSeries_ringHom_of_isAdicComplete : ∀ (W : Type) [CommRing W] (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ (ω : W →+* C) (v : C) (e : ℕ), v ^ e ∈ J → ∃ σ : W⟦X⟧ →+* C, (∀ w, σ (PowerSeries.C w) = ω w) ∧ σ X = v := by
  first | exact @GlobalTheory.PowerSeriesEval.exists_ringHom_powerSeries | exact GlobalTheory.PowerSeriesEval.exists_ringHom_powerSeries | (intros; apply GlobalTheory.PowerSeriesEval.exists_ringHom_powerSeries <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanSingletonClosedOfBoundedTorsionStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (d : A) (N : ℕ), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → IsAdicComplete (Ideal.span {(l : A)} ⊔ Ideal.span {d}) A → ∀ x : A, (∀ n : ℕ, ∃ z, x - d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n) → x ∈ Ideal.span {d} := by
  first | exact @GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion | exact GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion | (intros; apply GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinHomOfUniformizerFrame

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem BK.X_pow_eq_sub {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * q := by
  have h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with hi | rfl | hi
    · rw [if_neg hi.ne, sub_zero]; exact bk.dvd_coeff i hi
    · rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg hi.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hi]; exact dvd_zero _
  obtain ⟨q, hq⟩ := h
  refine ⟨(q : bk.S), ?_⟩
  have := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) hq
  simp only [map_sub, map_pow, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    Polynomial.coe_C, map_natCast] at this
  linear_combination -this

theorem isHausdorff_quot {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (P : Obj l R) (d : P.A)
    (hd : P.I = Ideal.span {d}) : IsHausdorff ((JJ P).map (Ideal.Quotient.mk P.I)) (P.A ⧸ P.I) := by
  have hinv := P.inv
  rw [hd] at hinv
  have hnzd : d ∈ nonZeroDivisors P.A := GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' P.A d hinv
  obtain ⟨N, hN⟩ := P.bdd
  have hbdd : ∀ (x : P.A) (m : ℕ), (l : P.A) ^ m * x ∈ Ideal.span {d} →
      (l : P.A) ^ N * x ∈ Ideal.span {d} := by
    intro x m hx
    rw [← hd, ← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
    rw [map_mul, map_pow, map_natCast] at hx ⊢
    exact hN _ ⟨m, hx⟩
  have hc := P.complete
  rw [hd] at hc
  refine ⟨fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.eq_zero_iff_mem, hd]
  refine GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit l P.A d N hnzd hbdd hc x fun n => ?_
  have h1 := hy n
  simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top] at h1
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  rw [Ideal.Quotient.eq, hd, Ideal.mem_span_singleton'] at hyx
  obtain ⟨z, hz⟩ := hyx
  refine ⟨-z, ?_⟩
  have e : x - d * -z = y := by linear_combination hz
  rw [e]
  rw [JJ, hd] at hy
  exact hy

theorem exists_lift_coeff_zero {l : ℕ} [Fact l.Prime] {k B : Type} [CommRing k] [CharP k l] [PerfectRing k l]
    [CommRing B] (f0 : WittVector l k →+* B) (hl : f0 (l : WittVector l k) = 0) :
    ∃ ψ : k →+* B, ∀ w : WittVector l k, ψ (w.coeff 0) = f0 w := by
  have hsurj : Function.Surjective (WittVector.constantCoeff : WittVector l k →+* k) :=
    fun x => ⟨WittVector.teichmuller l x, by simp [WittVector.constantCoeff_apply]⟩
  have hker : ∀ a ∈ RingHom.ker (WittVector.constantCoeff : WittVector l k →+* k), f0 a = 0 := by
    intro a ha
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hl, mul_zero]
  refine ⟨(Ideal.Quotient.lift _ f0 hker).comp (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom,
    fun w => ?_⟩
  have e : (RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0) = Ideal.Quotient.mk _ w := by
    rw [RingEquiv.symm_apply_eq]; rfl
  show Ideal.Quotient.lift _ f0 hker ((RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0)) = _
  rw [e, Ideal.Quotient.lift_mk]

theorem pow_mem_of_eq_sub {A S : Type} [CommRing A] [CommRing S] {I J : Ideal A} (hIJ : I ≤ J) {l : ℕ}
    (hl : (l : A) ∈ J) (τ : S →+* A ⧸ I) {x E q : S} {e : ℕ} {v : A} (hq : x ^ e = E - (l : S) * q)
    (hE : τ E = 0) (hx : τ x = Ideal.Quotient.mk I v) : v ^ e ∈ J := by
  have a2 := congrArg τ hq
  rw [map_pow, map_sub, map_mul, map_natCast, hx, hE] at a2
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (τ q)
  have h1 : Ideal.Quotient.mk I (v ^ e + (l : A) * t) = 0 := by
    rw [map_add (f := _), map_pow, map_mul, map_natCast, ht, a2]
    ring
  have h2 := hIJ (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  have h3 : (l : A) * t ∈ J := Ideal.mul_mem_right _ _ hl
  simpa using J.sub_mem h2 h3

theorem sub_mem_map_of_mk_eq {A : Type} [CommRing A] {I J : Ideal A} (hIJ : I ≤ J) (a : A) (y : A ⧸ I)
    (h : Ideal.Quotient.mk J a = Ideal.Quotient.factor hIJ y) :
    Ideal.Quotient.mk I a - y ∈ J.map (Ideal.Quotient.mk I) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at h
  rw [← map_sub]
  exact Ideal.mem_map_of_mem _ h

theorem quot_comp_eq {W A : Type} [CommRing W] [CommRing A] {I J : Ideal A}
    (hH : IsHausdorff (J.map (Ideal.Quotient.mk I)) (A ⧸ I)) (σ : W⟦X⟧ →+* A) (τ : W⟦X⟧ →+* A ⧸ I)
    {v : A} {e : ℕ} (hve : v ^ e ∈ J) (hσX : σ X = v) (hτX : τ X = Ideal.Quotient.mk I v)
    (hC : ∀ w, Ideal.Quotient.mk I (σ (C w)) = τ (C w)) : (Ideal.Quotient.mk I).comp σ = τ := by
  refine ringHom_ext_of_sep _ _ hC ?_ ?_
  · rw [RingHom.comp_apply, hσX, hτX]
  · intro y hy
    refine hH.haus y fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    obtain ⟨c, hc⟩ := hy (e * n)
    rw [hc, RingHom.comp_apply, hσX, pow_mul, ← map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hve) n)

theorem mem_of_comp_eq {S A : Type} [CommRing S] [CommRing A] {I : Ideal A} (σ : S →+* A)
    (τ : S →+* A ⧸ I) (heq : (Ideal.Quotient.mk I).comp σ = τ) {E : S} (hE : τ E = 0) (a : S)
    (ha : a ∈ Ideal.span {E}) : σ a ∈ I := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.comp_apply, heq, map_mul, hE, mul_zero]

theorem natCast_mem_map_quot {A : Type} [CommRing A] {I J : Ideal A} {l : ℕ} (h : (l : A) ∈ J) :
    (l : A ⧸ I) ∈ J.map (Ideal.Quotient.mk I) := by
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) h
  rwa [map_natCast] at this

theorem exists_hom_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (d v : C.A),
    IsFrame bk C d v → C.D.δ v = 0 → ∃ g : Hom bk.prism C, BK.hf (bk := bk) g X = v := by
  intro l _ K bk P d v hF hδ
  obtain ⟨hd, hv⟩ := hF
  obtain ⟨τ, hτ⟩ : ∃ τ : bk.S →+* P.A ⧸ P.I,
      τ = P.str.comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {bk.E}))) := ⟨_, rfl⟩
  have hτX : τ X = Ideal.Quotient.mk P.I v := by rw [hτ]; exact hv.symm
  have hτE : τ bk.E = 0 := by
    rw [hτ]
    show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) bk.E)) = 0
    rw [Ideal.Quotient.mk_singleton_self, map_zero, map_zero]
  set J : Ideal P.A := JJ P with hJ
  have hIJ : P.I ≤ J := le_sup_right
  have hlJ : (l : P.A) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  obtain ⟨f0, hf0⟩ : ∃ f0 : Wq l bk.a →+* P.A ⧸ J,
      f0 = ((Ideal.Quotient.factor hIJ).comp τ).comp PowerSeries.C := ⟨_, rfl⟩
  have hl0 : f0 (l : Wq l bk.a) = 0 := by
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk J) l]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hlJ
  obtain ⟨ψ, hψ⟩ := exists_lift_coeff_zero f0 hl0
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_wittVector_lift_of_isAdicComplete' l (Fq l bk.a) P.A J hlJ P.complete ψ
  obtain ⟨q, hq⟩ := bk.X_pow_eq_sub
  generalize bk.Ep.natDegree = e at hq
  have hve : v ^ e ∈ J := pow_mem_of_eq_sub hIJ hlJ τ hq hτE hτX
  obtain ⟨σ, hσC, hσX⟩ := GlobalTheory.T.exists_powerSeries_ringHom_of_isAdicComplete (Wq l bk.a) P.A J P.complete ω v _ hve
  have hσδ := GlobalTheory.T.isDeltaRingHom_powerSeries_of_rank_one_image l bk.a P.A P.D J hlJ P.complete.toIsHausdorff σ _ (by rw [hσX]; exact hve)
    (by rw [hσX]; exact hδ)
  have hH := isHausdorff_quot P d hd
  have hlJ' := natCast_mem_map_quot (I := P.I) hlJ
  have hωC : (Ideal.Quotient.mk P.I).comp ω = τ.comp PowerSeries.C := by
    refine GlobalTheory.T.wittVector_ringHom_eq_of_sub_mem' l (Fq l bk.a) (P.A ⧸ P.I) (J.map (Ideal.Quotient.mk P.I)) hlJ' hH _ _ ?_
    intro w
    refine sub_mem_map_of_mk_eq hIJ (ω w) (τ (PowerSeries.C w)) ((hω w).trans ((hψ w).trans ?_))
    rw [hf0]
    simp only [RingHom.comp_apply]
  have heq : (Ideal.Quotient.mk P.I).comp σ = τ :=
    quot_comp_eq hH σ τ hve hσX hτX fun w =>
      (congrArg (Ideal.Quotient.mk P.I) (hσC w)).trans (RingHom.congr_fun hωC w)
  refine ⟨{ f := σ, f_δ := fun a => hσδ a, f_I := mem_of_comp_eq σ τ heq hτE, f_str := ?_ }, hσX⟩
  intro r a h
  have h' : Ideal.Quotient.mk (Ideal.span {bk.E}) a = bk.str r := h
  have h2 := RingHom.congr_fun heq a
  rw [hτ] at h2
  refine h2.trans ?_
  show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) a)) = P.str r
  exact congrArg P.str ((congrArg bk.str.symm h').trans (bk.str.symm_apply_apply r))

end GlobalTheory.BSP
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinHomOfUniformizerFrameStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisinHom_of_uniformizerFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (d v : C.A), IsFrame bk C d v → C.D.δ v = 0 → ∃ g : Hom bk.prism C, BK.hf g X = v := by
  first | exact @GlobalTheory.BSP.exists_hom_of_frame | exact GlobalTheory.BSP.exists_hom_of_frame | (intros; apply GlobalTheory.BSP.exists_hom_of_frame <;> assumption)
end
end
