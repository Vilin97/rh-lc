module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.GlobalTheory
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.FockMonomialRight
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CollapseExponent
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Monomial
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyBlock
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.TestBoundOfRhoAndNormSets
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyBlock
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyLabel
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.TestBoundOfRhoAndNormSets

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MlabNotMemYset

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section

variable {K : Type} [Field K]

theorem linMap_eq_sum {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (Y : MvPolynomial σ K) :
    T Y = ∑ ζ ∈ Y.support, Y.coeff ζ • T (monomial ζ 1) := by
  conv_lhs => rw [Y.as_sum]

  rw [map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]

end

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem Good.dg {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (f : D.EM → K) :
    D.Good p (Formalism.MainNotions.PlaneGram.dg f Z) := fun ζ hζ => hZ ζ (support_dg_subset f Z hζ)

theorem mlab_notMem_Yset (j : Fin D.J) (m : Fin D.r) (t : D.Tau) : D.mlab t ∉ D.Yset j m := by
  rw [mem_Yset]
  rintro (⟨m', h⟩ | ⟨b, -, h⟩ | ⟨m', -, h⟩) <;> simp [mb, mw, mlab, mtp] at h

end TwistData

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem cge_Pj_monomial (hD : DVRHyp v p) (D : TwistData K) (hr : 1 ≤ D.r)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (ζ : D.EM) (hζ : D.GoodE p ζ) :
    cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (monomial ζ 1)) := by
  intro ζ'
  by_cases h : ζ' ∈ (Pj (monomial ζ 1)).support
  · have hb : D.SameBlockAlt ζ ζ' := hP1 ζ ζ' h
    have h1 := D.blk_fact hD hr hζ hb
    exact vge_mono v (by linarith) (hP2 ζ hζ ζ')
  · rw [notMem_support_iff.mp h]; exact vge_zero v _

theorem good_Pj (D : TwistData K)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    {Y : MvPolynomial (D.ML × Fin D.r) K} (hY : D.Good p Y) : D.Good p (Pj Y) := by
  rw [linMap_eq_sum Pj Y]
  refine TwistData.Good.sum D _ _ fun ζ hζ => TwistData.Good.smul D ?_ _
  intro ζ' hζ'
  exact TwistData.GoodE.good_exponent_same_block D (hY ζ hζ) (hP1 ζ ζ' hζ')

theorem omega_clauses (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hPj : (∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))) ∧
      (∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1))) ∧
      (∀ Z (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) (Pj Z)) ∧
      (∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1)) ∧
      (∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ) Z, vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) θ (Pj Z)))
    (gp gm : D.EM → K) (hgp : ∀ ζ, 0 ≤ v (gp ζ)) (hgm : ∀ ζ, 0 ≤ v (gm ζ))
    (hcost : ∀ S : Finset D.ML, (∀ t, D.mlab t ∉ S) → ∀ (θ : ℝ) (Z : MvPolynomial (D.ML × Fin D.r) K),
        vala D.msg S θ Z → vala D.msg S (θ - 12 * D.c) (dg gp Z) ∧ vala D.msg S (θ - 12 * D.c) (dg gm Z)) :
    ((⌈D.Dm p C0 + D.kapD p / 2⌉₊ : ℕ) : ℝ) ≤ D.Dm p C0 + D.kapD p / 2 + 1 ∧
    (∀ Z, Integral v Z → D.Good p Z →
      Integral v (((p : K) ^ ⌈D.Dm p C0 + D.kapD p / 2⌉₊) • dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → D.Good p (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (i : Fin (D.nch j)),
      vala D.msg (D.chainSet j i) (D.th j i - D.sl j i - 12 * D.c) (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
      vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) (θ - 24 * D.c) (dg gm (Pj (dg gp Z)))) := by
  obtain ⟨hP1, hP2, hP3, -, hP5⟩ := hPj
  have hp : 2 ≤ p := two_le_p hD
  have hr : 1 ≤ D.r := hV.1
  have hJ : 1 ≤ D.J := hV.2.1
  have hkap := D.kapD_ge_one hp hr hJ
  have hDm := D.Dm_nonneg hp hr h1
  have hpos : 0 ≤ D.Dm p C0 + D.kapD p / 2 := by linarith
  refine ⟨(Nat.ceil_lt_add_one hpos).le, ?_, ?_, ?_, ?_⟩
  · intro Z hZi hZg
    rw [← cge_zero_iff_Integral]
    have hY : cge v 0 (dg gp Z) := by
      have := cge_dg v (a := 0) (b := 0) (f := gp) (fun ζ => (vge_zero_iff v _).mpr (hgp ζ))
        ((cge_zero_iff_Integral v Z).mpr hZi)
      simpa using this
    have hYg : D.Good p (dg gp Z) := TwistData.Good.dg D hZg gp
    have hPY : cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (dg gp Z)) := by
      rw [linMap_eq_sum Pj (dg gp Z)]
      refine cge_sum v _ _ fun ζ hζ => ?_
      have := cge_smul v (hY ζ) (cge_Pj_monomial hD D hr Pj hP1 hP2 ζ (hYg ζ hζ))
      simpa using this
    have hG : cge v (-(D.Dm p C0 + D.kapD p / 2)) (dg gm (Pj (dg gp Z))) := by
      have := cge_dg v (a := 0) (f := gm) (fun ζ => (vge_zero_iff v _).mpr (hgm ζ)) hPY
      simpa using this
    have := cge_smul v (vge_p_pow hD ⌈D.Dm p C0 + D.kapD p / 2⌉₊) hG
    refine cge_mono v ?_ this
    have := Nat.le_ceil (D.Dm p C0 + D.kapD p / 2)
    linarith
  · intro Z hZg
    exact TwistData.Good.dg D (good_Pj D Pj hP1 (TwistData.Good.dg D hZg gp)) gm
  · intro Z _ j i
    exact (hcost (D.chainSet j i) (D.mlab_notMem_chainSet j i) _ _ (hP3 (dg gp Z) j i)).2
  · intro Z _ j m θ _ hZ
    have a1 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) θ Z hZ).1
    have a2 := hP5 j m _ _ a1
    have a3 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) _ _ a2).2
    exact vala_mono (by linarith) a3

end Main

end Formalism.MainNotions.PlaneGram
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.OmegaValue

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem omega_value (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gp gm : D.EM → K) (hgp0 : ∀ ζ, 0 ≤ v (gp ζ))
    (happ : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gp ζ - D.gaP p gam ζ) ∧
        ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZi : Integral v Z) (hZg : D.Good p Z) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (dg gp Z))) - D.abelian₂ p F Z) := by
  have key : ∀ W, D.abelian₂ p F W = fock F (dg D.ga (D.ph p W)) := fun W => by
    simp only [TwistData.abelian₂, gaAct_eq_dg]
  have hLsum : ∀ (s : Finset D.EM) (f : D.EM → MvPolynomial (D.ML × Fin D.r) K),
      D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i) := by
    intro s f

    simp only [key, map_sum, fock_sum_right]
  have hLsmul : ∀ (c : K) (W : MvPolynomial (D.ML × Fin D.r) K), D.abelian₂ p F (c • W) = c * D.abelian₂ p F W := by
    intro c W
    simp only [key, map_smul, fock_smul_right]
  have hmon : ∀ (g : D.EM → K) (ζ : D.EM), dg g (monomial ζ (1 : K)) = g ζ • monomial ζ (1 : K) := by
    intro g ζ
    rw [dg_monomial, MvPolynomial.smul_monomial, smul_eq_mul]
  have hZ : Z = ∑ ζ ∈ Z.support, Z.coeff ζ • monomial ζ (1 : K) := by
    conv_lhs => rw [Z.as_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hp2 : 2 ≤ p := by have := hD.five_le; omega
  have hr1 : 1 ≤ D.r := hV.1
  have hkap : 0 ≤ D.kapD p := by
    unfold TwistData.kapD kap
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (lg_nonneg' hp2 hr1 _)
  have hDm : 0 ≤ D.Dm p C0 := TwistData.Dm_nonneg (D := D) hp2 hr1 h1

  rw [hZ, map_sum (dg gp), map_sum Pj, map_sum (dg gm), hLsum, hLsum, ← Finset.sum_sub_distrib]
  simp only [map_smul, hLsmul]
  apply vge_sum'
  intro ζ hζ
  rw [← mul_sub]
  have hgood : D.GoodE p ζ := hZg ζ hζ
  have hlow : D.LabLowE p ζ := hgood.1
  have h1' : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) =
      gp ζ * D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) := by
    rw [hmon, map_smul, map_smul, hLsmul]
  have h2' : D.abelian₂ p F (dg gm (monomial ζ (1 : K))) = gm ζ * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [hmon, hLsmul]
  have hexp : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) - D.abelian₂ p F (monomial ζ (1 : K)) =
      gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K)))) +
        (gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [h1', h2']
    ring
  rw [hexp]
  have hval := TwistData.value_monomial (D := D) hD h1 hV hH hE hF hF0 hdig Pj hP1 hP2 hP4 gm
    (fun ζ h => (happ ζ h).2) hgood
  have hZζ : vge v 0 (Z.coeff ζ) := (vge_zero_iff v _).mpr (hZi ζ)
  have hgp' : vge v 0 (gp ζ) := (vge_zero_iff v _).mpr (hgp0 ζ)
  have t1 : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K))))) := by
    have := vge_mul' v hgp' hval
    simpa using this
  have hgaP : v (D.gaP p gam ζ) = 0 := TwistData.v_gaP (D := D) hV hdig hlow
  have hg0 : D.gaP p gam ζ ≠ 0 := by
    intro h
    rw [h] at hgaP
    simp at hgaP
  have hgaP' : vge v 0 (D.gaP p gam ζ) := (vge_zero_iff v _).mpr (le_of_eq hgaP.symm)
  have hc1 : vge v (D.c : ℝ) (gp ζ - D.gaP p gam ζ) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gp ζ - D.gaP p gam ζ)).mpr (by exact_mod_cast (happ ζ hlow).1)
    simpa using this
  have hc2 : vge v (D.c : ℝ) (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gm ζ - (D.gaP p gam ζ)⁻¹)).mpr (by exact_mod_cast (happ ζ hlow).2)
    simpa using this
  have hgm' : vge v 0 (gm ζ) := by
    have h3 : gm ζ = (gm ζ - (D.gaP p gam ζ)⁻¹) + (D.gaP p gam ζ)⁻¹ := by ring
    rw [h3]
    refine vge_add' v (vge_mono' v (by positivity) hc2) ?_
    rw [vge_zero_iff v, AddValuation.map_inv, hgaP, neg_zero]
  have hsplit : gp ζ * gm ζ - 1 =
      (gp ζ - D.gaP p gam ζ) * gm ζ + D.gaP p gam ζ * (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    rw [mul_sub (D.gaP p gam ζ), mul_inv_cancel₀ hg0]
    ring
  have t2 : vge v (D.c : ℝ) (gp ζ * gm ζ - 1) := by
    rw [hsplit]
    refine vge_add' v ?_ ?_
    · simpa using vge_mul' v hc1 hgm'
    · simpa using vge_mul' v hgaP' hc2
  have hΛ := TwistData.vge_Lam_monomial (D := D) hD hV hF0 hgood
  have t3 := vge_mul' v t2 hΛ
  have t3' : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      ((gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K))) := vge_mono' v (by linarith) t3
  simpa using vge_mul' v hZζ (vge_add' v t1 t3')

theorem stepDEF_of (h1 : 1 ≤ C0) (hDIG : DIG K v p) (hG : StepG K v p) (hP : StepP K v p C0)
    (hE : StepE K v p) : StepDEF K v p C0 := by
  intro hD D hV hH _ F hF hF0
  have hF0' := (exists_of_vBB_zero v F hF0).2
  obtain ⟨Pj, hP1, hP2, hP3, hP4, hP5⟩ := hP hD D hV
  obtain ⟨cst, gam, hdig⟩ := D.digOK_exists hDIG hD hV.2.2.1
  obtain ⟨gp, gm, hgp, hgm, happ, hcost⟩ := hG hD D hV cst gam hdig
  obtain ⟨hN, hI, hGd, hch, hY⟩ :=
    omega_clauses hD h1 D hV Pj ⟨hP1, hP2, hP3, hP4, hP5⟩ gp gm hgp hgm hcost
  refine ⟨(dg gm).comp (Pj.comp (dg gp)), ⌈D.Dm p C0 + D.kapD p / 2⌉₊, hN, hI, hGd, hch, hY, ?_⟩
  intro Z hZi hZg
  exact omega_value hD h1 D hV hH hE hF hF0' hdig Pj hP1 hP2 hP4 gp gm hgp happ Z hZi hZg

end Formalism.MainNotions.PlaneGram
end
end
end
