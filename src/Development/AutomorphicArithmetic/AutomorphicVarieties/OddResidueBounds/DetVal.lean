module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Chcard
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.SumCharMulQuotientMatrixEqCharEvalMul
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsIntHigherStickelbergerDenomSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.GroupRingCharEvalStickelbergerYNeZeroOfParity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUpper
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.LinearIndependentCharactersOnQuotientReps

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.linearIndependent_characters_on_quotientReps :
    ∀ {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ), c * c = 1 → LinearIndependent Ω (fun χ : Ch Ω c ε => fun i : Qc c => ((χ.1 (rep i) : Ωˣ) : Ω)) := by
  intro Ω _ Γ _ c ε h2
  classical
  have hw : LinearIndependent Ω (fun χ : Ch Ω c ε => fun g : Γ => ((χ.1 g : Ωˣ) : Ω)) := by
    have := (linearIndependent_monoidHom Γ Ω).comp
      (fun χ : Ch Ω c ε => (Units.coeHom Ω).comp χ.1) (by
        intro χ ψ h
        apply Subtype.ext
        ext g
        exact congrArg (fun f : Γ →* Ω => f g) h)
    exact this
  rw [linearIndependent_iff'] at hw ⊢
  intro s a hs
  apply hw s a
  funext g
  have hg := (mk_eq_mk h2 (rep (Qc.mk c g)) g).mp (mk_rep _)
  have hi := congrFun hs (Qc.mk c g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
  generalize rep (Qc.mk c g) = r at hg hi
  rcases hg with rfl | rfl
  · exact hi
  · calc ∑ χ ∈ s, a χ * ((χ.1 (c * r) : Ωˣ) : Ω)
        = ∑ χ ∈ s, (ε : Ω) * (a χ * ((χ.1 r : Ωˣ) : Ω)) :=
          Finset.sum_congr rfl (fun χ _ => by rw [map_mul, Units.val_mul, χ.2]; ring)
      _ = (ε : Ω) * ∑ χ ∈ s, a χ * ((χ.1 r : Ωˣ) : Ω) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hi, mul_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detprod

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.det_mul_quotientByOrderTwo_eq_prod_charEval :
    ∀ {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] [HasEnoughRootsOfUnity Ω (Monoid.exponent Γ)] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z : MonoidAlgebra A Γ, algebraMap A Ω (detR c ε z) = ∏ χ : Ch Ω c ε, ev A χ.1 z := by
  intro A _ Ω _ _ Γ _ _ _ c ε hc hc1 hε z
  classical
  have hcard := card_signedInvolutionChar_eq_card_involutionQuotient (Ω := Ω) c ε hc hc1 hε
  let e : Ch Ω c ε ≃ Qc c := Fintype.equivOfCardEq hcard
  let P : Matrix (Qc c) (Qc c) Ω := Matrix.of fun k i => ((e.symm k).1 (rep i) : Ω)
  let M : Matrix (Qc c) (Qc c) Ω := (algebraMap A Ω).mapMatrix (mat c ε z)
  let d : Qc c → Ω := fun k => ev A (e.symm k).1 z
  have hPM : P * M = Matrix.diagonal d * P := by
    ext k j
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    simp only [P, M, d, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact sum_char_mul_quotientMatrix_eq_charEval_mul c ε hc hc1 (e.symm k) z j
  have hind : LinearIndependent Ω (fun k => P k) :=
    (linearIndependent_characters_on_quotientReps (Ω := Ω) c ε hc).comp e.symm e.symm.injective
  have hP : IsUnit P := Matrix.linearIndependent_rows_iff_isUnit.mp hind
  have hdet : P.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det P |>.mp hP).ne_zero
  have h2 : P.det * M.det = (∏ k, d k) * P.det := by
    rw [← Matrix.det_mul, hPM, Matrix.det_mul, Matrix.det_diagonal]
  have h3 : M.det = ∏ k, d k := by
    have := h2
    rw [mul_comm ((∏ k, d k))] at this
    exact mul_left_cancel₀ hdet this
  have h4 : algebraMap A Ω (detR c ε z) = M.det := by
    unfold detR
    rw [RingHom.map_det]
  rw [h4, h3]
  exact Equiv.prod_comp e.symm (fun χ => ev A χ.1 z)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.NormCharEvalHigherStickelbergerLe

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.norm_charEval_higherStickelberger_le :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* ℂˣ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ N → 1 ≤ k → ‖ev ℚ χ (yEl k a ha π)‖ ≤ (sizeY N a k : ℝ) := by
  intro N _ Γ _ π χ a ha k hN hk
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      have h' := (Nat.coprime_zero_left N).mp ha
      omega
    · exact h
  rw [groupRingCharEval_stickelbergerY_eq_euler_mul_genBernoulli π χ a ha k hN]
  set d := dirOf π χ
  have hd : ∀ x, ‖d x‖ ≤ 1 := fun x => DirichletCharacter.norm_le_one d x
  have hB := b_upper k (⇑d) (by omega) hd
  have h1 : ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖ ≤ 2 * (a : ℝ) ^ k := by
    calc ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖
        ≤ ‖(1 : ℂ)‖ + ‖(a : ℂ) ^ k * d (a : ZMod N)‖ := norm_sub_le _ _
      _ ≤ 1 + (a : ℝ) ^ k * 1 := by
          rw [norm_one, norm_mul, norm_pow, Complex.norm_natCast]
          gcongr
          exact hd _
      _ ≤ 2 * (a : ℝ) ^ k := by
          have : (1 : ℝ) ≤ (a : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast ha1)
          linarith
  have hpi : (4 : ℝ) ≤ (2 * Real.pi) ^ k := by
    calc (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      _ = (2 * Real.pi) ^ 1 := (pow_one _).symm
      _ ≤ (2 * Real.pi) ^ k := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hk
  have h2 : ‖genB k ⇑d‖ ≤ (N : ℝ) ^ k * k.factorial := by
    calc ‖genB k ⇑d‖ ≤ 4 * (N : ℝ) ^ k * k.factorial / (2 * Real.pi) ^ k := hB
      _ ≤ (N : ℝ) ^ k * k.factorial := by
        rw [div_le_iff₀ (by positivity)]
        have : 0 ≤ (N : ℝ) ^ k * k.factorial := by positivity
        nlinarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [norm_mul, norm_div, norm_neg, Complex.norm_natCast]
  calc ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖ * (‖genB k ⇑d‖ / k)
      ≤ 2 * (a : ℝ) ^ k * ((N : ℝ) ^ k * k.factorial) := by
        apply mul_le_mul h1 _ (by positivity) (by positivity)
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg (genB k ⇑d)]
    _ = (sizeY N a k : ℝ) := by
        rw [sizeY]
        push_cast
        ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detint

section

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.higherStickelberger_det_exists_int_bounded :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] [Finite Γ] (π : (ZMod N)ˣ →* Γ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ a → 2 ≤ k → π (-1) ≠ 1 → ∃ X : ℤ, X ≠ 0 ∧ X.natAbs ≤ bdX N a k ^ (Nat.card Γ / 2) ∧ (X : ℚ) = (denY N k : ℚ) ^ (Nat.card Γ / 2) * detR (π (-1)) ((-1) ^ k) (yEl k a ha π) := by
  intro N _ Γ _ _ π a ha k h2a hk hc
  have hN : 2 ≤ N := by
    by_contra h
    have h0 := NeZero.ne N
    obtain rfl : N = 1 := by omega
    exact hc (by rw [Subsingleton.elim (-1 : (ZMod 1)ˣ) 1, map_one])
  have hcc : π (-1) * π (-1) = 1 := by rw [← map_mul]; simp
  have hε : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  haveI : NeZero (Monoid.exponent Γ : ℂ) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨z, hz⟩ := exists_int_higherStickelbergerDenom_smul π a ha k (by omega)
  have hX : ((detR (π (-1)) ((-1) ^ k) z : ℤ) : ℚ) =
      (denY N k : ℚ) ^ (Nat.card Γ / 2) * detR (π (-1)) ((-1) ^ k) (yEl k a ha π) := by
    rw [← detR_coefMap, hz, detR_smul, card_Qc' hcc hc]
  have hp := det_mul_quotientByOrderTwo_eq_prod_charEval (A := ℚ) (Ω := ℂ) (π (-1)) ((-1) ^ k) hcc hc hε (yEl k a ha π)
  have hD : (0 : ℚ) < denY N k := by exact_mod_cast denY_pos (by omega) (by omega)
  refine ⟨_, ?_, ?_, hX⟩
  · have : algebraMap ℚ ℂ (detR (π (-1)) ((-1) ^ k) (yEl k a ha π)) ≠ 0 := by
      rw [hp]
      exact Finset.prod_ne_zero_iff.2 fun χ _ => groupRingCharEval_stickelbergerY_ne_zero_of_parity π χ.1 a ha k hN h2a hk (by simpa using χ.2)
    intro h
    rw [h, Int.cast_zero, eq_comm, mul_eq_zero] at hX
    rcases hX with h | h
    · exact (pow_pos hD _).ne' h
    · exact this (by rw [h, map_zero])
  · have h1 : ‖algebraMap ℚ ℂ (detR (π (-1)) ((-1) ^ k) (yEl k a ha π))‖ ≤ (sizeY N a k : ℝ) ^ (Nat.card Γ / 2) := by
      rw [hp, norm_prod, ← card_Qc' hcc hc, ← card_signedInvolutionChar_eq_card_involutionQuotient (Ω := ℂ) _ _ hcc hc hε, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun χ _ => norm_charEval_higherStickelberger_le π χ.1 a ha k hN (by omega)
    have h2 : (((detR (π (-1)) ((-1) ^ k) z).natAbs : ℕ) : ℝ) = ‖algebraMap ℚ ℂ ((detR (π (-1)) ((-1) ^ k) z : ℤ) : ℚ)‖ := by
      rw [map_intCast, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
    have h3 : (((detR (π (-1)) ((-1) ^ k) z).natAbs : ℕ) : ℝ) ≤ ((bdX N a k ^ (Nat.card Γ / 2) : ℕ) : ℝ) := by
      rw [h2, hX, map_mul, norm_mul, map_pow, norm_pow, map_natCast, Complex.norm_natCast, bdX]
      push_cast
      rw [mul_pow]
      gcongr
    exact_mod_cast h3
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.DetVal

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem int_dvd_pow (l : ℕ) [hl : Fact l.Prime] (X : ℤ) (hX : X ≠ 0) :
    ∃ r : ℕ, l ^ r ≤ X.natAbs ∧ (X : ℤ_[l]) ∣ (l : ℤ_[l]) ^ r := by
  obtain ⟨e, n', hn', he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hX) l hl.out.one_lt.ne'
  have hn0 : n' ≠ 0 := by
    rintro rfl
    exact hn' (dvd_zero l)
  refine ⟨e, ?_, ?_⟩
  · rw [he]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0)
  · have hu : IsUnit ((n' : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hn' ?_)
      exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd _).mp h
    rw [Int.cast_natCast] at hu
    have h1 : (X : ℤ_[l]) ∣ ((X.natAbs : ℤ) : ℤ_[l]) :=
      map_dvd (Int.castRingHom ℤ_[l]) (Int.dvd_natAbs.mpr dvd_rfl)
    refine h1.trans ?_
    rw [he]
    push_cast
    exact hu.mul_right_dvd.mpr dvd_rfl

theorem UpperTheory.V.Odd.detVal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Function.Surjective φ → φ (-1) ≠ 1 → 1 ≤ e → 1 < a → ∀ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) ∧ detR (φ (-1)) ((-1) ^ (e + 1)) z ∣ (l : ℤ_[l]) ^ r := by
  intro l _ Γ _ _ N _ φ e a ha hs hφ he ha1 z hz
  obtain ⟨X, hX0, hXb, hXe⟩ := higherStickelberger_det_exists_int_bounded φ a ha (e + 1) ha1 (by omega) hφ
  obtain ⟨r, hr1, hr2⟩ := int_dvd_pow l X hX0
  refine ⟨r, ?_, ?_⟩
  · have h1 : ((l : ℝ) ^ r) ≤ (bdX N a (e + 1) : ℝ) ^ (Nat.card Γ / 2) := by
      exact_mod_cast hr1.trans hXb
    have hl0 : (0 : ℝ) < (l : ℝ) ^ r := by
      have := (Fact.out : l.Prime).pos
      positivity
    have h2 := Real.log_le_log hl0 h1
    rw [Real.log_pow, Real.log_pow] at h2
    have h3 : ((Nat.card Γ / 2 : ℕ) : ℝ) ≤ (Nat.card Γ : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    calc (r : ℝ) * Real.log l ≤ ((Nat.card Γ / 2 : ℕ) : ℝ) * Real.log (bdX N a (e + 1)) := h2
      _ ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) :=
        mul_le_mul_of_nonneg_right h3 (Real.log_natCast_nonneg _)
  · refine dvd_trans ?_ hr2
    have hmap : MonoidAlgebra.mapRingHom Γ PadicInt.Coe.ringHom z =
        MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) (yEl (e + 1) a ha φ) := by
      ext g
      have h := hz g
      simp
      exact h
    have hd := congrArg (detR (φ (-1)) ((-1) ^ (e + 1))) hmap
    rw [detR_map, detR_map] at hd
    have hq := congrArg (Rat.castHom ℚ_[l]) hXe
    rw [map_mul, map_pow, ← hd] at hq
    have hX'' : (X : ℤ_[l]) =
        (denY N (e + 1) : ℤ_[l]) ^ (Nat.card Γ / 2) * detR (φ (-1)) ((-1) ^ (e + 1)) z := by
      apply PadicInt.ext
      push_cast
      simp at hq
      exact hq
    rw [hX'']
    exact dvd_mul_left _ _
end
end
