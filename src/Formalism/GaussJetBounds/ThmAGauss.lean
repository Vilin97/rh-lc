module

public import Formalism.GaussJetBounds.StatementP
public import Formalism.GaussJetBounds.GaussJetProofs.FJEval
public import Formalism.GaussJetBounds.GaussJetProofs.Labels
public import Formalism.GaussJetBounds.FrameJetEval
public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffEvenDerivativeEqZero
public import Formalism.GaussJetBounds.GaussJetProofs.GField
public import Formalism.GaussJetBounds.StatementM
public import Formalism.GaussJetBounds.GaussJetProofs.FrameA
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.GaussJetBounds.GaussJetProofs.Transfer

-- Source module: Formalism.GaussJetBounds.GaussJetProofs.Generic

section

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem generic_mono_det {R : Type*} [CommRing R] [Nontrivial R] {d N0 n : ℕ} (z : Fin N0)
    (t : Fin n → ZMod d) (L : Fin n → ℕ) (γ : Fin n → Fin N0) (hγ : Function.Injective γ)
    (hL : ∀ i, L i ≠ 0) (hinj : Function.Injective fun i => (t i, L i)) :
    (Matrix.of fun (r c : Fin n) =>
      (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)).det ≠ 0 := by
  classical
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, (Matrix.of fun (r c : Fin n) =>
        (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)) (σ i) i)
        = MvPolynomial.monomial (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) 1 := by
    intro σ
    rw [MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [MvPolynomial.X_pow_eq_monomial]
  have hval : ∀ (f : Fin n → ZMod d) (g : Fin n → ℕ) (i : Fin n),
      (∑ j, Finsupp.single (f j, z, γ j) (g j)) (f i, z, γ i) = g i := by
    intro f g i
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)
    · simp
  have hval2 : ∀ (i : Fin n) (u : ZMod d),
      (∑ j, Finsupp.single (t j, z, γ j) (L j)) (u, z, γ i) = if t i = u then L i else 0 := by
    intro i u
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · rw [Finsupp.single_apply]
      by_cases h : t i = u
      · simp [h]
      · rw [if_neg, if_neg h]
        intro h'
        exact h (Prod.ext_iff.mp h').1
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)
    · simp
  have key : ∀ σ : Equiv.Perm (Fin n),
      (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) = ∑ i, Finsupp.single (t i, z, γ i) (L i) → σ = 1 := by
    intro σ h
    ext i
    have h1 : (∑ j, Finsupp.single (t (σ j), z, γ j) (L (σ j))) (t (σ i), z, γ i)
        = (∑ j, Finsupp.single (t j, z, γ j) (L j)) (t (σ i), z, γ i) := by rw [h]
    rw [hval (fun j => t (σ j)) (fun j => L (σ j)) i, hval2] at h1
    by_cases ht : t i = t (σ i)
    · rw [if_pos ht] at h1
      have : σ i = i := hinj (Prod.ext ht.symm h1)
      simp [this]
    · rw [if_neg ht] at h1
      exact absurd h1 (hL (σ i))
  intro hdet
  have hc := congrArg (AddMonoidAlgebra.coeff · (∑ i, Finsupp.single (t i, z, γ i) (L i))) hdet
  rw [Matrix.det_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))] at hc
  · rw [hprod] at hc
    simp at hc
  · intro σ _ hσ
    rw [hprod, Units.smul_def, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_neg]
    · simp
    · exact fun h => hσ (key σ h)
  · simp

theorem generic_minor_norm {K : Type u} [NormedField K] {l d N0 n : ℕ} (hl : l.Prime)
    (Y : ZMod d × Fin N0 × Fin N0 → K) (hY : IsGeneric l Y) (s : ZMod d) (z : Fin N0)
    (t : Fin n → ZMod d) (L : Fin n → ℕ) (e : Fin n → Fin N0) (he : Function.Injective e)
    (hn : n ≤ N0) (hts : ∀ i, t i ≠ s) (hL : ∀ i, L i ≠ 0)
    (hinj : Function.Injective fun i => (t i, L i)) :
    ‖(Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det‖ = 1 := by
  classical
  haveI : Fact (1 < l) := ⟨hl.one_lt⟩
  set P : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℤ := (Matrix.of fun (i i' : Fin n) =>
    ∑ a, MvPolynomial.X (t i, z, a) ^ (L i) * MvPolynomial.X (s, e i', a)).det with hP
  have hev : MvPolynomial.aeval Y P
      = (Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det := by
    rw [hP, AlgHom.map_det]
    congr 1
    ext i i'
    simp
  rw [← hev]
  refine hY P ?_
  intro h0
  have hmap : MvPolynomial.map (Int.castRingHom (ZMod l)) P = (Matrix.of fun (i i' : Fin n) =>
      ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i)
        * MvPolynomial.X (s, e i', a)).det := by
    rw [hP, RingHom.map_det]
    congr 1
    ext i i'
    simp
  rw [hmap] at h0
  let f : ZMod d × Fin N0 × Fin N0 → MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l) :=
    fun v => if v.1 = s then (if v.2.1 = v.2.2 then 1 else 0) else MvPolynomial.X v
  have h1 := congrArg (MvPolynomial.bind₁ f) h0
  rw [map_zero, AlgHom.map_det] at h1
  have h2 : (MvPolynomial.bind₁ f).mapMatrix (Matrix.of fun (i i' : Fin n) =>
      ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i)
        * MvPolynomial.X (s, e i', a))
      = Matrix.of fun (r c : Fin n) =>
        (MvPolynomial.X (t r, z, e c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L r) := by
    ext i i'

    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, map_pow,
    MvPolynomial.bind₁_X_right, f, if_neg (hts i), if_true]
    rw [Finset.sum_eq_single (e i')]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · simp
  rw [h2] at h1
  exact generic_mono_det z t L e he hL hinj h1

theorem generic_norm_one {K : Type u} [NormedField K] {σ : Type} {l : ℕ} (hl : l.Prime)
    (Y : σ → K) (hY : IsGeneric l Y) (y : σ) : ‖Y y‖ = 1 := by
  haveI : Fact (1 < l) := ⟨hl.one_lt⟩
  have h := hY (MvPolynomial.X y) (by
    rw [MvPolynomial.map_X]
    exact MvPolynomial.X_ne_zero y)
  simpa using h

theorem theorem_A_generic : ThmAGeneric.{u} := by
  intro K _ _ _ l d N0 N1 _ hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I Y hY nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab hJ m hm
  classical
  have hYn : ∀ y, ‖Y y‖ = 1 := generic_norm_one hl Y hY
  have hxg : ∀ y, ‖genFrame TT l m Y y‖ ≤ 1 := by
    intro y
    simp only [genFrame]
    split_ifs <;> simp [norm_pow, hYn]
  have hw : ∀ s (i : Fin (J s)), (lab s i).1 ∈ TT ∧ Odd (lab s i).2 ∧
      s = (lab s i).1 + (((lab s i).2 : ℤ) : ZMod d) := by
    intro s i
    have := (hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hxg0 : ∀ s0 ∈ TT, ∀ a, genFrame TT l m Y (s0, ⟨0, h0⟩, a) = Y (s0, ⟨0, h0⟩, a) ^ l ^ m := by
    intro s0 hs0 a
    simp [genFrame, hs0]
  let E : (s : ZMod d) → Fin (J s) → ℕ := fun s i => ((m : ℤ) + (lab s i).2).toNat
  let lam : (s : ZMod d) → Fin (J s) → Fin N0 → K := fun s i a => Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ E s i
  have hlam1 : ∀ s i a, ‖lam s i a‖ ≤ 1 := by
    intro s i a
    simp [lam, norm_pow, hYn]
  have hpos : ∀ s i a, 0 < (lab s i).2 →
      lam s i a = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ (lab s i).2.toNat := by
    intro s i a hj
    rw [hxg0 _ (hw s i).1, ← pow_mul, ← pow_add]
    simp only [lam, E]
    congr 2
    omega
  have hneg : ∀ s i a, (lab s i).2 < 0 →
      lam s i a ^ l ^ (-(lab s i).2).toNat = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) := by
    intro s i a hj
    have hmm := hm s i
    rw [hxg0 _ (hw s i).1]
    simp only [lam, E]
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  let e : (s : ZMod d) → Fin (J s) → Fin N0 := fun s i =>
    ⟨i + (if s ∈ TT then 1 else 0), by
      have h := hJ s
      have hi := i.isLt
      split_ifs at h ⊢ <;> omega⟩
  have he_inj : ∀ s, Function.Injective (e s) := by
    intro s i i' h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [e] at h'
    omega
  have he0 : ∀ s i, ¬(s ∈ TT ∧ ((e s i : Fin N0) : ℕ) = 0) := by
    intro s i h
    obtain ⟨hs, hz0⟩ := h
    simp [e, hs] at hz0
  have hdet : ∀ s, ‖(Matrix.of fun (i i' : Fin (J s)) =>
      ∑ a : Fin N0, lam s i a * genFrame TT l m Y (s, e s i', a)).det‖ = 1 := by
    intro s
    have hx : ∀ i' a, genFrame TT l m Y (s, e s i', a) = Y (s, e s i', a) := by
      intro i' a
      simp only [genFrame]
      rw [if_neg (he0 s i')]
    simp only [hx]
    have hts : ∀ i, (lab s i).1 ≠ s := by
      intro i h
      obtain ⟨_, hodd, hss⟩ := hw s i
      rw [h] at hss
      have hx0 : (((lab s i).2 : ℤ) : ZMod d) = 0 := by simpa using hss
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
      have hev : Even ((d : ℕ) : ℤ) := (Int.even_coe_nat d).mpr he
      obtain ⟨k, hk⟩ := hdvd
      have : Even (lab s i).2 := by
        rw [hk]
        exact hev.mul_right k
      exact (Int.not_even_iff_odd.mpr hodd) this
    have hLn : ∀ i, l ^ E s i ≠ 0 := fun i => pow_ne_zero _ hl.ne_zero
    have hinj' : Function.Injective fun i => ((lab s i).1, l ^ E s i) := by
      intro i i' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨ha1, ha2⟩ := h
      have hE := Nat.pow_right_injective hl.two_le ha2
      simp only [E] at hE
      have hm1 := hm s i
      have hm2 := hm s i'
      have ho1 := (hw s i).2.1
      have ho2 := (hw s i').2.1
      have hn1 : (lab s i).2 ≠ 0 := fun h => by rw [h] at ho1; exact absurd ho1 (by decide)
      have hn2 : (lab s i').2 ≠ 0 := fun h => by rw [h] at ho2; exact absurd ho2 (by decide)
      have hj : (lab s i).2 = (lab s i').2 := by omega
      exact hinj s (Prod.ext ha1 hj)
    have hn : J s ≤ N0 := by
      have h := hJ s
      split_ifs at h <;> omega
    exact generic_minor_norm hl Y hY s ⟨0, h0⟩ (fun i => (lab s i).1) (fun i => l ^ E s i) (e s)
      (he_inj s) hn hts hLn hinj'
  exact theorem_A_frame K l d N0 N1 hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I
    (genFrame TT l m Y) hxg nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab lam hlam1 hpos hneg e he_inj he0 hdet

end Formalism.DworkPowerSeriesWeights
end
end
end

-- Source module: Formalism.GaussJetBounds.GaussJetProofs.ThmAGaussOf

section

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem thmAGauss_of (hT : TransferB) (hF : FrameJetEval) (hL : LabelsExist) (hG : GaussPow) :
    ThmAGauss := by
  intro l _ d N0 N1 _ hl3 hd hde K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize a ha hsa hthr n
  have hlp : l.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists l (ZMod d × Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnl : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have h := norm_intCast_padicComplex l (l : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    rw [h]
    exact Padic.norm_p_lt_one
  have hN0 : 0 < N0 := by
    have h0 : 0 ≤ Real.logb l a :=
      Real.logb_nonneg (by exact_mod_cast hlp.one_lt) (by exact_mod_cast ha)
    have h1 : (0 : ℝ) < N0 := by linarith
    exact_mod_cast h1
  have hnu1a : ∀ s, nu1 s ≤ a := fun s => le_trans (by
    rw [hnu1, hsize]
    calc colN s = ∑ _c : Fin (colN s), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ => hp1 s c) (hsa s)
  obtain ⟨J, lab, m, hinj, hlab, hJ, hm⟩ := hL l d N0 hlp.two_le TT nu1 size a ha hnu1a hsa hthr
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hT ℂ_[l] K φ hφ l d N0 N1 K0 ζ be
  obtain ⟨hg0', hg'⟩ := hT3 g hg0 hg
  have hA := theorem_A_generic.{0} K l d N0 N1 hlp hl3 hd hde (hnl ▸ hl1) hN0 (K0.map φ) (hT1 hK0)
    (φ ζ) (hζ.map_of_injective φ.injective) _ (hT2 hbe) _ hg0' hg' _ (hT4 U hU) (φ ε)
    (by rcases hε with rfl | rfl <;> simp) TT colN p hp hp1 I Y hgen nu1 nu2 size hnu1 hnu2 hsize
    a ha hsa J lab hinj hlab hJ m hm
  rw [← hF ℂ_[l] K φ d N0 N1 g U ε be hg0 (asmS_cc_be hbe.2.2.1) colN p hp I (genFrame TT l m Y),
    hnl] at hA
  refine le_trans ?_ hA
  have hk : genFrame TT l m Y =
      fun y => Y y ^ (if y.1 ∈ TT ∧ y.2.1.val = 0 then l ^ m else 1) := by
    funext y
    unfold genFrame
    split_ifs <;> simp
  rw [hk]
  refine hG ℂ_[l] K φ _ Y hgauss _ (fun y => ?_) _ n
  split_ifs
  · exact pow_ne_zero _ hlp.ne_zero
  · exact one_ne_zero

end Formalism.DworkPowerSeriesWeights
end
end
end

-- Source module: Formalism.GaussJetBounds.ThmAGauss

section

@[expose] public section

namespace Formalism.DworkPowerSeriesWeights

theorem thmAGauss : ThmAGauss :=
  thmAGauss_of admissibleTransfer frame_jet_evaluation labelsExist_statement gauss_sum_powers

end Formalism.DworkPowerSeriesWeights
end
end
