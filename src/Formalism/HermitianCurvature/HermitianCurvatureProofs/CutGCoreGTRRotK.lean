module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRCentre
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRMatFrom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRMatFrom
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRSec
import Mathlib.Analysis.Calculus.Deriv.Prod

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRFinFrom

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RRFin

theorem hasDerivAt_rotExp (m : ℂ) :
    HasDerivAt (fun φ : ℝ => Complex.exp (m * (φ : ℂ) * Complex.I)) (m * Complex.I) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul m).mul_const Complex.I).cexp
  simpa using h

end RRFin

open RRMat RRFin in
theorem rotation_finite_from_matrix : GTRRFinFrom := by
  intro hC hS hW Wp Wq _ _ _ _ _ _ P Bs hpl hk2 hsec e he hc n hn Rt s hRt ρ Φ
  have hB := SSTr.radBase P Bs hpl
  have hTT0 : 0 ≤ P.TT := by
    rw [← SSTr.tz_eq P Bs hpl]; exact mul_nonneg hB.2.2.2.1.le hB.2.2.2.2.1.le
  set E : M.Ty P → (Wq →L[ℂ] Wp) := fun σ => e σ 0 with hEdef
  have heE : ∀ σ ζ, e σ ζ = E σ := fun σ ζ => hc σ ζ 0
  have hid : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => w) (Ann P) := contDiff_id.contDiffOn
  have hstar : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => star w) (Ann P) :=
    by
      have h : (fun w : ℂ => star w) = ⇑Complex.conjCLE := by funext w; simp
      rw [h]; exact Complex.conjCLE.contDiff.contDiffOn
  apply Subtype.ext
  funext q
  simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, SetLike.val_smul, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [dzQ_apply P hTT0, dzbQ_apply P hTT0, fnZ_val P hid, fnZ_val P hstar]
  have hcq : q.1.1 ∈ OmX P.r := q.2.1
  have hζq : P.TT < Complex.normSq q.1.2 := q.2.2

  have hsm : ContDiffOn ℝ MA.sm (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) :=
    (trR P Bs e Φ ρ).2
  have hdiff : DifferentiableAt ℝ (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 :=
    (hsm.differentiableOn (by simp [MA.sm])).differentiableAt ((MA.Qset_open P.r P.TT).mem_nhds q.2)
  have hWa := hW P.r (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 hdiff

  have hfibq : ∀ φ : ℝ, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
      (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by
    intro φ
    have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ.1 Φ.2
    have hx : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
      ⟨hcq, by rw [normSq_rot]; exact ann_tz P Bs hpl hζq⟩
    have h2 := hm.2.1 _ hx
    simp only [NF.radR, Set.indicator_of_mem hx] at h2
    exact h2
  have hGy : ∀ φ : ℝ, inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ))) =
      Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) * inner ℂ (B.hsVec (E ρ)) (B.hsVec
        ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))))) := by
    intro φ
    have hζe : P.TT < Complex.normSq (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by rw [normSq_rot]; exact hζq
    have hexp := (he.2 _ hζe).2.2 _ (hfibq φ)
    simp only [heE] at hexp
    have hM : ∀ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E σ))) =
        if ρ = σ then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0 := fun σ => hn φ ρ σ
    rw [rot_eqv hS P Bs hpl hsec Φ q.1.1 hcq q.1.2 hζq φ]
    conv_lhs => rw [hexp]
    rw [rotA_sum, SSTr.hsVec_sum, inner_sum]
    simp only [VLem.hsV_smul, inner_smul_right, hM, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

  have hD : ((q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1 (q := q.1) ⟨hcq, ann_tz P Bs hpl hζq⟩
  have hG := hasDerivAt_pair hC P Bs Φ _ hD (E ρ) 1
  simp only [one_mul] at hG
  have hE := hasDerivAt_rotExp (-(n ρ : ℂ))
  have hprod := (hE.mul hG).const_mul ((wR P.k P.TT q.1.2 : ℝ) : ℂ)
  have hpt : ∀ φ : ℝ, MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) (q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I) *
        inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
          (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ)))) := by
    intro φ
    have hmem : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E P.r) ∈ MA.Qset P.r P.TT :=
      ⟨hcq, by rw [normSq_rot]; exact hζq⟩
    unfold MA.ext
    rw [dite_eq_left hmem, SSTr.trR_apply P Bs hpl hk2 e he]
    simp only [rawR]
    rw [wR_rot, heE, hGy φ, ← mul_assoc (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I)), ← Complex.exp_add]
    have h0 : -(n ρ : ℂ) * (φ : ℂ) * Complex.I + (n ρ : ℂ) * (φ : ℂ) * Complex.I = 0 := by ring
    rw [h0, Complex.exp_zero, one_mul]
  have hF := hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall hpt)
  have heq := hWa.unique hF

  have hsum := hRt Φ _ hD
  simp only at hsum
  have hG0 := hGy 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hG0 heq
  rw [SSTr.trR_apply P Bs hpl hk2 e he, SSTr.trR_apply P Bs hpl hk2 e he]
  simp only [rawR]
  rw [hG0] at heq
  rw [heE, hsum, VLem.hsV_add, inner_add_right, VLem.hsV_smul, inner_smul_right]
  push_cast
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination -heq

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRODE

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_ode_holds : GTRRODE := by
  intro ι _ _ Mf Bm h0 hadd hper hd hoff
  have hderiv : ∀ (φ : ℝ) (i j : ι), HasDerivAt (fun x => Mf x i j) (Bm i i * Mf φ i j) φ := by
    intro φ i j
    have hg0 := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hd i k).mul_const (Mf φ k j))
    have ef : (∑ k : ι, fun (y : ℝ) => Mf y i k * Mf φ k j) = fun h : ℝ => ∑ k, Mf h i k * Mf φ k j := by
      funext h
      rw [Finset.sum_apply]
    rw [ef] at hg0
    have hsum : ∑ k, Bm i k * Mf φ k j = Bm i i * Mf φ i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hoff i k (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum] at hg0
    have h2 := HasDerivAt.comp_sub_const φ φ (by rw [sub_self]; exact hg0)
    have e : (fun x => Mf x i j) = fun x : ℝ => ∑ k, Mf (x - φ) i k * Mf φ k j := by
      funext x
      rw [← Matrix.mul_apply, ← hadd, sub_add_cancel]
    rw [e]
    exact h2
  have hsol : ∀ (i j : ι) (x : ℝ), Mf x i j = Complex.exp (Bm i i * x) * (if i = j then 1 else 0) := by
    intro i j x
    have hf : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y) * Mf y i j) 0 y := by
      intro y
      have he : HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y)) (Complex.exp (-Bm i i * y) * (-Bm i i * 1)) y :=
        (((hasDerivAt_id y).ofReal_comp).const_mul (-Bm i i)).cexp
      have hm := he.mul (hderiv y i j)
      have h3 : Complex.exp (-Bm i i * ↑y) * (-Bm i i * 1) * Mf y i j + Complex.exp (-Bm i i * ↑y) * (Bm i i * Mf y i j) = 0 := by
        ring
      rw [h3] at hm
      exact hm
    have hc := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt) (fun y => (hf y).deriv) x 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0, Matrix.one_apply] at hc
    rw [← hc, ← mul_assoc, ← Complex.exp_add]
    simp
  have hn : ∀ i, ∃ n : ℤ, Bm i i = n * Complex.I := by
    intro i
    have h1 := hsol i i (2 * Real.pi)
    rw [hper] at h1
    simp only [Matrix.one_apply_eq, if_true, mul_one] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1.symm
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  choose n hn using hn
  refine ⟨n, fun φ i j => ?_⟩
  rw [hsol]
  split_ifs with h
  · subst h
    rw [hn]
    ring_nf
  · simp

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRWirt

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rot_alg (ζ D1 DI : ℂ) : -(ζ.im : ℂ) * D1 + (ζ.re : ℂ) * DI =
    Complex.I * (ζ * ((1 / 2 : ℂ) * (D1 + -Complex.I * DI)) - star ζ * ((1 / 2 : ℂ) * (D1 + Complex.I * DI))) := by
  have hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hs : star ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hz +
    ((Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hs + ((ζ.re : ℂ) * DI - (ζ.im : ℂ) * D1) * Complex.I_sq

theorem rotation_wirtinger_holds : GTRRWirt := by
  intro r u x hu
  have h1 : HasDerivAt (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I))
      (Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I) * (1 * Complex.I)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp
  have h2 : HasDerivAt (fun φ : ℝ => x.2 * Complex.exp ((φ : ℂ) * Complex.I)) (x.2 * Complex.I) 0 := by
    have h3 := h1.const_mul x.2
    simpa using h3
  have hγ : HasDerivAt (fun φ : ℝ => ((x.1, x.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E r))
      ((0 : Fin r → ℂ), x.2 * Complex.I) 0 := by
    first
    | exact (hasDerivAt_const (0 : ℝ) x.1).prodMk h2
    | exact (hasDerivAt_const (0 : ℝ) x.1).prod h2
  have hx : x = ((x.1, x.2 * Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I)) : MA.E r) := by simp
  have hc := hu.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hx
  have hdir1 : MA.dirE (M.vz (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vz]
  have hdir2 : MA.dirE (M.vzb (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vzb]
  have hw1 : MA.wirt M.vz u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      -Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir1]
    simp [M.vz]
  have hw2 : MA.wirt M.vzb u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir2]
    simp [M.vzb]
  have key : Complex.I * (x.2 * MA.wirt M.vz u x - star x.2 * MA.wirt M.vzb u x) =
      fderiv ℝ u x ((0 : Fin r → ℂ), x.2 * Complex.I) := by
    rw [hw1, hw2, ← rot_alg]
    have hv : ((0 : Fin r → ℂ), x.2 * Complex.I) = x.2.re • ((0 : Fin r → ℂ), Complex.I) +
        (-x.2.im) • ((0 : Fin r → ℂ), (1 : ℂ)) := by
      refine Prod.ext (by simp) ?_
      simp only [Prod.smul_snd, Prod.snd_add, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp
    rw [hv, map_add (f := _), map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [key]
  exact hc

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotK

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_K_invariance_holds : GTRRotK :=
  gTRRotK_of_mat_fin_centre_sec_ode_wirt rotation_matrix_form_holds rotation_finite_from_matrix rotation_centre_condition rotation_section_holds rotation_ode_holds rotation_wirtinger_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end
