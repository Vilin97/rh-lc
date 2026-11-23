module

public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TouchCOfMem
public import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom
import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd
import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TMemLaurentFiltration
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne

-- Source module: Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ValuationGeOfLeAddOne

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

section Gen

variable {σ R : Type*} [CommRing R]

theorem X_mul_mono (v : σ) (mo : σ →₀ ℕ) (c : R) : X v * monomial mo c = monomial (mo + Finsupp.single v 1) c := by
  rw [X, monomial_mul, one_mul, add_comm]

theorem pderiv_add_single (w : σ) (L : σ →₀ ℕ) (c : R) :
    pderiv w (monomial (L + Finsupp.single w 1) c) = monomial L (c * ((L w : R) + 1)) := by
  rw [pderiv_monomial, add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  push_cast
  rfl

theorem pderiv_mono_zero (w : σ) (L : σ →₀ ℕ) (c : R) (h : L w = 0) : pderiv w (monomial L c) = 0 := by
  rw [pderiv_monomial, h, Nat.cast_zero, mul_zero, map_zero]

theorem exists_add_single (w : σ) (L : σ →₀ ℕ) (h : L w ≠ 0) : ∃ L', L = L' + Finsupp.single w 1 := ⟨L - Finsupp.single w 1,
  (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))).symm⟩

end Gen

section PolS

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

theorem multideg_add_single (mo : ι × Fin n →₀ ℕ) (x0 : ι) (a : Fin n) (i : ι) :
    multideg (mo + Finsupp.single (x0, a) 1) i = multideg mo i + if i = x0 then 1 else 0 := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : i = x0
  · subst h
    simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, h, Ne.symm h]

theorem mem_Pol' {d : ι → ℕ} {F : MvPolynomial (ι × Fin n) R} :
    F ∈ Pol R n d ↔ ∀ m ∈ F.support, ∀ i, multideg m i = d i := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    exact h hm
  · intro h m hm
    exact h m hm

theorem mono_mem_Pol {d : ι → ℕ} (m : ι × Fin n →₀ ℕ) (c : R) (h : ∀ i, multideg m i = d i) :
    monomial m c ∈ Pol R n d := by
  rw [mem_Pol']
  intro m' hm'
  have h1 := support_monomial_subset hm'
  rw [Finset.mem_singleton] at h1
  rw [h1]
  exact h

theorem Pol_pderiv {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d' x0 = d x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : pderiv (x0, a) H ∈ Pol R n d := by
  rw [mem_Pol'] at hH

  rw [H.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  by_cases hz : m (x0, a) = 0
  · rw [pderiv_mono_zero _ _ _ hz]
    exact Submodule.zero_mem _
  · obtain ⟨m', rfl⟩ := exists_add_single _ m hz
    rw [pderiv_add_single]
    apply mono_mem_Pol
    intro i
    have hi := hH _ hm i
    rw [multideg_add_single] at hi
    by_cases hix : i = x0
    · subst hix
      simp at hi
      omega
    · simp [hix] at hi
      rw [hi, h1 i hix]

theorem Pol_X_mul {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d x0 = d' x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : X (x0, a) * H ∈ Pol R n d := by
  rw [mem_Pol'] at hH
  rw [H.as_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [X_mul_mono]
  apply mono_mem_Pol
  intro i
  rw [multideg_add_single, hH m hm i]
  by_cases hix : i = x0
  · subst hix
    simp
    omega
  · simp [hix]
    exact h1 i hix

end PolS

theorem valuation_ge_of_le_add_one {x y : WithTop ℤ} {t t' : ℝ} (h : x ≤ y + ((1 : ℤ) : WithTop ℤ)) (hx : geZ x t') (ht : t + 1 ≤ t') :
    geZ y t := by
  intro k hk
  rw [hk] at h
  have h' : x ≤ ((k + 1 : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_add]
    exact h
  induction x using WithTop.recTopCoe with
  | top => simp at h'
  | coe k'' =>
    have h2 := hx k'' rfl
    have h3 : (k'' : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast WithTop.coe_le_coe.mp h'
    linarith

section ValOp

variable {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

end ValOp

end Formalism.MainNotions.PairMembershipBlocks
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.XXgZeroP

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
  [NeZero r] (Dt : SignedChainData p O r J)

theorem twoPow_pos (j : ZMod J) (m : Fin r) : 0 < Dt.P j m := pow_pos (Nat.Prime.pos Fact.out) _

theorem XXg_zeroP (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) :
    XXg Dt d th thL 0 := by
  refine ⟨Submodule.zero_mem _, fun rho j i => ?_, fun j mm _ => ?_⟩
  · rw [Fdig_zero, valS_zero_eq_top]; exact geZ_top _
  · rw [valS_zero_eq_top]; exact geZ_top _

private theorem touchC_of_liftVar_mem_chainML (x0 : TL J Dt.nL r) (a : Fin r) (j : ZMod J) (i : Fin (Dt.nch j))
    (h : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i) : touchC Dt x0 j i := by
  obtain ⟨j', y⟩ := x0
  obtain ⟨z, hz, hzz⟩ := h
  rcases y with l | m <;> rcases z with l' | m'
  · simp only [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
    injection hzz with h1 h2
    subst h1
    cases h2
    exact Or.inl ⟨l', rfl, hz⟩
  · simp [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
  · simp [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
  · simp only [Formalism.MainNotions.PlaneGramData.SignedChainData.levToML, Formalism.MainNotions.PlaneGramData.SignedChainData.liftVar] at hzz
    injection hzz with h1 h2
    subst h1 h2
    exact Or.inr ⟨m', rfl⟩

theorem plDer' (x0 : TL J Dt.nL r) (a : Fin r) (d d' : TL J Dt.nL r → ℕ) (h0 : d' x0 = d x0 + 1)
    (h1 : ∀ i, i ≠ x0 → d' i = d i) (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ)
    (t1 : ∀ j i, th j i ≤ th' j i)
    (t2 : ∀ j i, touchC Dt x0 j i → Dt.trueLet.vec x0 = true → th j i + 1 ≤ th' j i)
    (t3 : ∀ j m, thL j m ≤ thL' j m)
    (t4 : ∀ j m, x0 ∈ Dt.TSet j m → Dt.trueLet.vec x0 = true → thL j m + 1 ≤ thL' j m)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hH : XXg Dt d' th' thL' H) :
    XXg Dt d th thL (pderiv (x0, a) H) := by
  obtain ⟨hP, hC, hT⟩ := hH
  refine ⟨Pol_pderiv x0 a h0 h1 hP, fun rho j i => ?_, fun j m hm => ?_⟩
  · obtain ⟨c1, c2, c3, rho1, rho2, hc2, hF⟩ := Fdig_der_ex Dt (twoPow_pos Dt) (x0, a) rho
    rw [hF]
    have e1 : geZ (valS Dt.modelLet (Dt.chainML j i) (c1 • Dt.Fdig rho1 H)) (th j i) :=
      geZ_anti (t1 j i) (geZ_mono (valS_smul_ge _ _ _ _) (hC rho1 j i))
    have e2 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c2 • (X (Dt.liftVar (x0, a)) * pderiv (Dt.liftVar (x0, a)) (Dt.Fdig rho1 H)))) (th j i) := by
      by_cases hc : c2 = 0
      · rw [hc, zero_smul, valS_zero_eq_top]
        exact geZ_top _
      have hv : Dt.trueLet.vec x0 = true := hc2 hc
      refine geZ_mono (valS_smul_ge _ _ _ _) (geZ_mono (valS_X_mul_of _ _ _ _ ?_) ?_)
      · intro _
        rw [modelLet_vec]
        exact hv
      by_cases hs : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i
      · exact valuation_ge_of_le_add_one (valS_pderiv _ _ _ _) (hC rho1 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hs) hv)
      · exact geZ_anti (t1 j i)
          (geZ_mono (valS_pderiv_of _ _ _ _ (fun h => absurd h hs)) (hC rho1 j i))
    have e3 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c3 • pderiv (Dt.liftVar (x0, a)) (Dt.Fdig rho2 H))) (th j i) := by
      refine geZ_mono (valS_smul_ge _ _ _ _) ?_
      by_cases hb : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i ∧ Dt.trueLet.vec x0 = true
      · exact valuation_ge_of_le_add_one (valS_pderiv _ _ _ _) (hC rho2 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hb.1) hb.2)
      · refine geZ_anti (t1 j i) (geZ_mono (valS_pderiv_of _ _ _ _ ?_) (hC rho2 j i))
        intro hs
        rw [modelLet_vec]
        by_contra hc
        exact hb ⟨hs, by simpa using hc⟩
    exact geZ_mono (flt_valS_add _ _ _ _) (geZ_min (geZ_mono (flt_valS_add _ _ _ _) (geZ_min e1 e2)) e3)
  · by_cases hb : x0 ∈ Dt.TSet j m ∧ Dt.trueLet.vec x0 = true
    · exact valuation_ge_of_le_add_one (valS_pderiv _ _ H (x0, a)) (hT j m hm) (t4 j m hb.1 hb.2)
    · refine geZ_anti (t3 j m) (geZ_mono (valS_pderiv_of _ _ H (x0, a) ?_) (hT j m hm))
      intro hs
      by_contra hc
      exact hb ⟨hs, by simpa using hc⟩

theorem plMul' (x0 : TL J Dt.nL r) (a : Fin r) (d d' : TL J Dt.nL r → ℕ) (h0 : d x0 = d' x0 + 1)
    (h1 : ∀ i, i ≠ x0 → d' i = d i) (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ)
    (t1 : ∀ j i, th j i ≤ th' j i)
    (t2 : ∀ j i, touchC Dt x0 j i → Dt.trueLet.vec x0 = false → th j i + 1 ≤ th' j i)
    (t3 : ∀ j m, thL j m ≤ thL' j m)
    (t4 : ∀ j m, x0 ∈ Dt.TSet j m → Dt.trueLet.vec x0 = false → thL j m + 1 ≤ thL' j m)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hH : XXg Dt d' th' thL' H) :
    XXg Dt d th thL (X (x0, a) * H) := by
  obtain ⟨hP, hC, hT⟩ := hH
  refine ⟨Pol_X_mul x0 a h0 h1 hP, fun rho j i => ?_, fun j m hm => ?_⟩
  · obtain ⟨c1, c2, rho1, rho2, hF⟩ := Fdig_mul_ex Dt (twoPow_pos Dt) (x0, a) rho
    rw [hF]
    have e1 : geZ (valS Dt.modelLet (Dt.chainML j i) (c1 • Dt.Fdig rho1 H)) (th j i) :=
      geZ_anti (t1 j i) (geZ_mono (valS_smul_ge _ _ _ _) (hC rho1 j i))
    have e2 : geZ (valS Dt.modelLet (Dt.chainML j i)
        (c2 • (X (Dt.liftVar (x0, a)) * Dt.Fdig rho2 H))) (th j i) := by
      refine geZ_mono (valS_smul_ge _ _ _ _) ?_
      by_cases hb : (Dt.liftVar (x0, a)).1 ∈ Dt.chainML j i ∧ Dt.trueLet.vec x0 = false
      · exact valuation_ge_of_le_add_one (valS_X_mul _ _ _ _) (hC rho2 j i) (t2 j i (touchC_of_liftVar_mem_chainML Dt x0 a j i hb.1) hb.2)
      · refine geZ_anti (t1 j i) (geZ_mono (valS_X_mul_of _ _ _ _ ?_) (hC rho2 j i))
        intro hs
        rw [modelLet_vec]
        by_contra hc
        exact hb ⟨hs, by simpa using hc⟩
    exact geZ_mono (flt_valS_add _ _ _ _) (geZ_min e1 e2)
  · by_cases hb : x0 ∈ Dt.TSet j m ∧ Dt.trueLet.vec x0 = false
    · exact valuation_ge_of_le_add_one (valS_X_mul _ _ H (x0, a)) (hT j m hm) (t4 j m hb.1 hb.2)
    · refine geZ_anti (t3 j m) (geZ_mono (valS_X_mul_of _ _ H (x0, a) ?_) (hT j m hm))
      intro hs
      by_contra hc
      exact hb ⟨hs, by simpa using hc⟩

end Formalism.MainNotions.PairMembershipBlocks

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem plDer : PlDer := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD H hH
  exact plDer' Dt x0 a d (Function.update d x0 (d x0 + 1)) (by simp)
    (fun i hi => by simp [Function.update_of_ne hi]) th th' thL thL' hD.1
    (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH

theorem plMul : PlMul := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD hd H hH
  exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) (by simp; omega)
    (fun i hi => by simp [Function.update_of_ne hi]) th th' thL thL' hD.1
    (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH

theorem plEul : PlEul := by
  intro p _ O _ _ _ r J _ _ Dt x0 a d th th' thL thL' hD H hH
  rcases Nat.eq_zero_or_pos (d x0) with hz | hpos
  · have hvars : (x0, a) ∉ H.vars := by
      intro hv
      obtain ⟨m, hm, hma⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 hv
      have hdeg := (mem_Pol'.1 hH.1) m hm x0
      rw [hz] at hdeg
      have hle : m (x0, a) ≤ multideg m x0 :=
        Finset.single_le_sum (f := fun c => m (x0, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      rw [hdeg] at hle
      exact (Finsupp.mem_support_iff.1 hma) (by omega)
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hvars, mul_zero]
    exact XXg_zeroP Dt d th thL
  · have e0 : d x0 = Function.update d x0 (d x0 - 1) x0 + 1 := by simp; omega
    have e1 : ∀ i, i ≠ x0 → Function.update d x0 (d x0 - 1) i = d i :=
      fun i hi => by simp [Function.update_of_ne hi]
    have e1' : ∀ i, i ≠ x0 → d i = Function.update d x0 (d x0 - 1) i :=
      fun i hi => (e1 i hi).symm
    cases hv : Dt.trueLet.vec x0
    · have hD1 := plDer' Dt x0 a (Function.update d x0 (d x0 - 1)) d e0 e1' th' th' thL' thL'
        (fun _ _ => le_rfl) (fun _ _ _ hf => by simp [hv] at hf) (fun _ _ => le_rfl)
        (fun _ _ _ hf => by simp [hv] at hf) H hH
      exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) e0 e1 th th' thL thL' hD.1
        (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) _ hD1
    · have hD1 := plDer' Dt x0 a (Function.update d x0 (d x0 - 1)) d e0 e1' th th' thL thL' hD.1
        (fun j i h _ => hD.2.1 j i h) hD.2.2.1 (fun j m h _ => hD.2.2.2 j m h) H hH
      exact plMul' Dt x0 a d (Function.update d x0 (d x0 - 1)) e0 e1 th th thL thL
        (fun _ _ => le_rfl) (fun _ _ _ hf => by simp [hv] at hf) (fun _ _ => le_rfl)
        (fun _ _ _ hf => by simp [hv] at hf) _ hD1

end Formalism.MainNotions.PairMembershipBlocks
end
end
end
