module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCore
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConst
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstAsm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSEntry

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

namespace SSEn

theorem coe_sum_apply {r : ℕ} {TT : ℝ} {ι : Type} (s : Finset ι) (g : ι → MA.SmQ r TT) (q : MA.Qp r TT) :
    Subtype.val (∑ i ∈ s, g i) q = ∑ i ∈ s, Subtype.val (g i) q := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

theorem ss_entry_apply (P : M.Par) (l : ℕ) (ρ π' : M.Ty P) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 f) q =
      (if M.Up P l π' ρ then ((Real.sqrt (M.Nrm P l π') : ℝ) : ℂ) else 0) * (f : MA.Qp P.r P.TT → ℂ) q := by
  simp only [MA.SS, Matrix.of_apply]
  split_ifs with h
  · rfl
  · rw [zero_mul]
    rfl

end SSEn

open SSEn in
theorem second_shift_entry_holds : SSn.Rep.Core.SSEntry := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hSSF l hl S hS ζ hζ π ρ
  obtain ⟨hpl, hL, hSt, hRel, hQQ⟩ := hA
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hRB := Gauge.GC.radBase_of P Bs hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero

  have hsec : ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e π q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨((he.1 π).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 π
    · simp [Set.indicator_of_notMem hq]
  obtain ⟨Ψ0, hΨ0, hΨr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ hsec
  let Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Ψ0, hΨ0⟩
  have hΨ : (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) = e π ζ := by
    have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
    have h := congrFun hΨr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h

  have hv : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P),
      ((Gauge.GC.trR P Bs e Θ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
        Gauge.rawR P Bs.μsec e (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ := fun Θ σ =>
    Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem P (Gauge.GC.radial_space_smoothness Wp Wq P Bs hpl hk e he Θ σ)
  let q : MA.Qp P.r P.TT := ⟨((c0, ζ) : MA.E P.r), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hw := Gauge.GC.wRc_ne P hζ

  have e1 : Subtype.val (Gauge.GC.trR P Bs e ((d.SS l).1 Ψ) ρ) q =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) := by
    refine (congrFun (hv ((d.SS l).1 Ψ) ρ) q).trans ?_
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec ((((d.SS l).1 Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0
        (NF.muZ P.k P.r Bs.μsec ζ))) = _
    rw [hS Ψ c0 hc0 ζ hζ, hΨ]

  have e2 : Subtype.val (Gauge.GC.trR P Bs e ((d.SS l).1 Ψ) ρ) q =
      ∑ π', Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 (Gauge.GC.trR P Bs e Ψ π')) q := by
    refine (congrArg (fun F : M.Ty P → MA.SmQ P.r P.TT => Subtype.val (F ρ) q) (hSSF l hl Ψ).1).trans ?_
    exact coe_sum_apply _ _ _
  have hterm : ∀ π' : M.Ty P, Subtype.val (Gauge.GC.trR P Bs e Ψ π') q =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (if π' = π then 1 else 0) := by
    intro π'
    rw [congrFun (hv Ψ π') q]
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e π' ζ))
      (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ))) = _
    rw [hΨ, (he.2 ζ hζ).2.1 π' π]
  have e3 : ∑ π', Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 (Gauge.GC.trR P Bs e Ψ π')) q =
      (if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0) * ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) := by
    simp only [ss_entry_apply, hterm]
    rw [Finset.sum_eq_single π (fun π' _ hne => by simp [hne]) (fun h => absurd (Finset.mem_univ π) h)]
    simp
  have h2 : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) *
        (if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0) := by
    rw [← e1, e2, e3, mul_comm]
  exact mul_left_cancel₀ hw h2

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCoreAsm

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core

noncomputable section

theorem theta_gauge_constancy_holds : ThtGaugeConstOfCore := by
  intro hA hPt hTh hE hPR hGL hDU
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ v e hH hk l hl Bw Bw' hBw hBw'
  obtain ⟨hB, hFr, hGa, hQQ⟩ := hH
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v)
    (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' hPl
  obtain ⟨d, hd1, hd2, hd3, hd4⟩ := Formalism.FourierDecayAlt.P.normal_form_actual (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v)
    (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' hPl X
  have hAct : ActHyp (D.parOf S v) (T v).base X d := ⟨hPl, hd1, hd2, hd3, hd4⟩
  obtain ⟨SS, hSS⟩ := hPt (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct l hl
  obtain ⟨Pr, hPr⟩ := hPR (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
  obtain ⟨θ, hθ⟩ := hTh (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct l hl SS hSS Pr hPr
    Bw Bw' hBw hBw'
  have hFrB : Gauge.IsFrameB (D.parOf S v) (T v).base e := hFr
  have hGQ : GQQ (D.parOf S v) (T v).base e := hQQ
  have hSSF := hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct e hFrB hGQ
  refine ⟨θ, fun ζ hζ π ρ hup => ?_⟩
  have hent := hE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct e hFrB hSSF l hl SS hSS ζ hζ π ρ
  rw [if_pos hup] at hent
  obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v ζ hζ
  set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ with hn0
  have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
    unfold PRho.nrmW; rw [hP1, hH1]; simp
  obtain ⟨-, -, hrest⟩ := hPr
  have hpos : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z n0 := by rw [hN0]; norm_num

  have hfix : ∀ τ y, Pr τ n0 (e τ ζ y) = e τ ζ y := by
    intro τ y
    refine ((hrest n0 hpos).2.2.2 τ (e τ ζ y)).2 ?_
    intro Fr hFrm w
    rw [hP1] at hFrm
    exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk ζ hζ τ Fr hFrm w y
  have hfixc : ∀ τ, (Pr τ n0).comp (e τ ζ) = e τ ζ := fun τ => by ext y; exact hfix τ y
  have hsa := (hrest n0 hpos).2.1 ρ
  have hfib : e π ζ ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' ζ :=
    ((hFrB.2 ζ hζ).1 π)
  set B0 : Wq (S.pl v) →L[ℂ] Wp (S.pl v) := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    Bw Bw' n0 (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
    (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ) with hB0
  have key : (Pr ρ n0).comp (SS ζ (e π ζ)) = θ π • (Pr ρ n0).comp B0 :=
    hθ ζ hζ π ρ hup (e π ζ) hfib (hfixc π)

  have hmove : ∀ Y : Wq (S.pl v) →L[ℂ] Wp (S.pl v),
      inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp Y)) = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Y) := by
    intro Y
    have h1 := hsInner_lmul (Pr ρ n0) hsa Y (e ρ ζ)
    simp only [B.hsInner, lmul_apply] at h1
    rw [hfixc ρ] at h1
    exact h1
  have hsm : ∀ (c : ℂ) (A : Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A
    unfold B.hsVec
    ext i
    simp
  calc θ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec B0)
      = θ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp B0)) := by rw [hmove]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (θ π • (Pr ρ n0).comp B0)) := by rw [hsm, inner_smul_right]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp (SS ζ (e π ζ)))) := by rw [key]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (SS ζ (e π ζ))) := hmove _
    _ = _ := hent

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepPolyFinish

section

@[expose] public section

open Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

theorem pf_conj_eval' (q : ℂ[X]) (x : ℝ) :
    (q.map (starRingEnd ℂ)).eval (x : ℂ) = starRingEnd ℂ (q.eval (x : ℂ)) := by
  rw [Polynomial.eval_map]
  have hx : (x : ℂ) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  conv_lhs => rw [hx]
  exact Polynomial.eval₂_at_apply _ _

theorem pf_id (q : ℂ[X]) (n : ℕ) (a C : ℝ)
    (h : ∀ x : ℝ, a < x → Complex.normSq (q.eval (x : ℂ)) = C * (x - a) ^ (2 * n)) :
    q * q.map (starRingEnd ℂ) = Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n) := by
  have hroots : Set.Infinite {z : ℂ | IsRoot (q * q.map (starRingEnd ℂ) -
      Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n)) z} := by
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((a + 1 + m : ℝ) : ℂ)) ?_ ?_
    · intro s t hst
      have := Complex.ofReal_injective hst
      exact_mod_cast (by linarith : (s : ℝ) = t)
    · intro m
      simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      have hx : a < a + 1 + (m : ℝ) := by have := m.cast_nonneg (α := ℝ); linarith
      rw [pf_conj_eval', Complex.mul_conj, h _ hx]
      push_cast
      ring
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ hroots)

theorem polynomial_finish_holds : PolyFinish := by
  intro q n a C h
  have hid := pf_id q n a C h
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  have hqb : q.map (starRingEnd ℂ) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]
  have hC : (C : ℂ) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.C_0, zero_mul] at hid
    exact mul_ne_zero hq hqb hid
  have hroot : ∀ b ∈ q.roots, b = (a : ℂ) := by
    intro b hb
    have hb0 : q.eval b = 0 := (Polynomial.mem_roots hq).1 hb
    have := congrArg (Polynomial.eval b) hid
    simp only [eval_mul, hb0, zero_mul, eval_C, eval_pow, eval_sub, eval_X] at this
    have h2 := (mul_eq_zero.1 this.symm).resolve_left hC
    exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h2).1
  have hcard : Multiset.card q.roots = q.natDegree := by
    first
      | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits q)).symm
      | exact IsAlgClosed.card_roots_eq_natDegree
  have hrep : q.roots = Multiset.replicate q.natDegree (a : ℂ) := by
    rw [← hcard]; exact Multiset.eq_replicate.2 ⟨rfl, hroot⟩
  have hform : q = Polynomial.C q.leadingCoeff * (X - Polynomial.C (a : ℂ)) ^ q.natDegree := by
    conv_lhs => rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    rw [hrep, Multiset.map_replicate, Multiset.prod_replicate]
  have hdeg : q.natDegree = n := by
    have h1 := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hq hqb, Polynomial.natDegree_map_eq_of_injective (RingHom.injective _),
      Polynomial.natDegree_C_mul hC, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at h1
    omega
  exact ⟨q.leadingCoeff, by rw [← hdeg]; exact hform⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstAsmS

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

theorem theta_constancy_assembly_scalar : ThConstOfCutS := by
  intro hPR hMC hLN hPF
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw'
  have main : ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) := by
    intro π ρ hup
    obtain ⟨n, q, hq⟩ := hPR Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    obtain ⟨c₁, c₂, hc⟩ := hMC Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    have hGG : ∀ ζ ∈ Gauge.GC.Ann P, (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) ≠ 0 := by
      intro ζ hζ
      have : (0 : ℝ) < Complex.normSq ζ - P.TT := by
        have := hζ; simp only [Gauge.GC.Ann, Set.mem_ofPred_eq] at this; linarith
      exact pow_ne_zero _ (by exact_mod_cast this.ne')
    by_cases hc2 : c₂ = 0
    · refine ⟨0, fun ζ hζ Xf hXf hfix => ?_⟩
      have hB0 := (hc ζ hζ Xf hXf hfix).2
      rw [hc2, zero_mul, sq_eq_zero_iff, norm_eq_zero] at hB0
      have hB0' := tc_hsVec_eq_zero hB0
      have h1 := hq ζ hζ Xf hXf hfix
      rw [hB0', smul_zero] at h1
      rw [zero_smul]
      exact (smul_eq_zero.1 h1).resolve_left (hGG ζ hζ)
    ·
      have hTT : 0 ≤ P.TT := by
        have := hAct.1.1
        exact mul_nonneg this.T_pos.le this.T'_pos.le
      have hmod : ∀ x : ℝ, 0 < x → Complex.normSq (q.eval (x : ℂ)) = (c₁ / c₂) * (x - 0) ^ (2 * (2 * n)) := by
        intro x hx
        have hxx : 0 ≤ x ^ 2 + P.TT := by positivity
        set ζ : ℂ := ((Real.sqrt (x ^ 2 + P.TT) : ℝ) : ℂ) with hζdef
        have hnz : Complex.normSq ζ = x ^ 2 + P.TT := by
          rw [hζdef, Complex.normSq_ofReal, ← sq, Real.sq_sqrt hxx]
        have hζ : ζ ∈ Gauge.GC.Ann P := by
          show P.TT < Complex.normSq ζ
          rw [hnz]; nlinarith
        have hgg : Complex.normSq ζ - P.TT = x ^ 2 := by rw [hnz]; ring
        have hsq : Real.sqrt (Complex.normSq ζ - P.TT) = x := by rw [hgg, Real.sqrt_sq hx.le]
        obtain ⟨Xf, hXf, hfix, hne⟩ := hLN Wp Wq P Bs hAct.1 hk Pr hPr π ζ hζ
        obtain ⟨hS1, hB1⟩ := hc ζ hζ Xf hXf hfix
        have h1 := congrArg (fun w => ‖B.hsVec w‖ ^ 2) (hq ζ hζ Xf hXf hfix)
        simp only [tc_hsVec_smul, norm_smul, mul_pow] at h1
        rw [hS1, hB1, hsq, hgg] at h1
        have hX : 0 < ‖B.hsVec Xf‖ ^ 2 := by
          have : B.hsVec Xf ≠ 0 := fun h0 => hne (tc_hsVec_eq_zero h0)
          positivity
        have hnq : ‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 = Complex.normSq (q.eval (x : ℂ)) := by
          rw [Complex.normSq_eq_norm_sq]
        have hng : ‖((x ^ 2 : ℝ) : ℂ) ^ n‖ ^ 2 = (x - 0) ^ (2 * (2 * n)) := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2), ← pow_mul,
            ← pow_mul, sub_zero]
          ring_nf
        rw [hng] at h1
        have h2 : (‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 * c₂ - (x - 0) ^ (2 * (2 * n)) * c₁) * ‖B.hsVec Xf‖ ^ 2 = 0 := by
          linear_combination (-1 : ℝ) * h1
        have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hX.ne')
        rw [← hnq, div_mul_eq_mul_div, eq_div_iff hc2]
        linarith [h3]
      obtain ⟨c, hcq⟩ := hPF q (2 * n) 0 (c₁ / c₂) hmod
      refine ⟨c, fun ζ hζ Xf hXf hfix => ?_⟩
      have h1 := hq ζ hζ Xf hXf hfix
      have hpos : 0 ≤ Complex.normSq ζ - P.TT := by
        have := hζ; simp only [Gauge.GC.Ann, Set.mem_ofPred_eq] at this; linarith
      have hev : q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) =
          c * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) := by
        rw [hcq]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
          Complex.ofReal_zero, sub_zero]
        rw [pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt hpos]
      rw [hev, mul_comm, mul_smul] at h1
      exact smul_right_injective _ (hGG ζ hζ) h1
  classical
  refine ⟨fun π => if h : ∃ ρ, M.Up P l π ρ then (main π h.choose h.choose_spec).choose else 0, ?_⟩
  intro ζ hζ π ρ hup Xf hXf hfix
  have hex : ∃ ρ, M.Up P l π ρ := ⟨ρ, hup⟩
  have hρ : hex.choose = ρ := tc_up_unique hex.choose_spec hup
  simp only [dif_pos hex]
  have := (main π hex.choose hex.choose_spec).choose_spec ζ hζ Xf hXf hfix
  subst hρ
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepTop

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem thConst_of_open (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : Core.ThConst := by
  rcases hPoly with h | h
  · exact Core.TC.theta_constancy_assembly h hMC hLN Core.TC.polynomial_finish_holds
  · exact Core.TC.theta_constancy_assembly_scalar h hMC hLN Core.TC.polynomial_finish_holds

theorem ssnRep_of_open (hPE : PRho.PRhoExists) (hTF : ThtFacts) (hMC : Core.TC.ModConst)
    (hLN : Core.TC.LineNonzero) (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  second_shift_representation_assembly hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds hTF datum_unit_norm_holds
    (Core.theta_gauge_constancy_holds Formalism.FourierDecayAlt.P.CutMP.JA.quadratic_second_shift_form Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_pointwise_holds
      (thConst_of_open hMC hLN hPoly) Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_entry_holds hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds
      datum_unit_norm_holds)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end
end
