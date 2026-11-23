module

public import Development.AutomorphicArithmetic.CharacterBoxes.PairGood
public import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
public import Development.AutomorphicArithmetic.MeanSquareBounds.IndUnique
public import Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
public import Development.AutomorphicArithmetic.MeanSquareBounds.Kappa4Loglog
public import Development.AutomorphicArithmetic.MeanSquareBounds.PairShare
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.MeanSquareBounds.IndDrop

section

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem ind_drop :
    ∀ (N₀ q M : ℕ) (ξ : DirichletCharacter ℂ N₀) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 0 < N₀ → q.Prime → q ≠ 2 → ¬ q ∣ N₀ → M ≠ 0 →
      Ind χ (fun n => ξ n * J q n) M → Ind χ (fun n => ξ n * J q n) (N₀ * q) := by
  intro N₀ q M ξ N _ χ hN₀ hq hq2 hqN₀ hM hχ
  obtain ⟨hχp, hind⟩ := hχ
  haveI : NeZero N₀ := ⟨hN₀.ne'⟩
  haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hqf : ¬ q ∣ ξ.conductor := fun h => hqN₀ (h.trans ξ.conductor_dvd_level)
  obtain ⟨ψ, hψ, -, hψeq⟩ :=
    twist_prim ξ.conductor q ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq hq2 hqf
  have hprim : ∀ n : ℕ, n.Coprime N₀ → ξ n = ξ.primitiveCharacter n := by
    intro n hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter
      ξ.conductor_dvd_level (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    rw [Int.cast_natCast, Int.cast_natCast] at h
    exact h
  have heq := ind_unique N (ξ.conductor * q) (M * N₀ * q) χ ψ
    (mul_ne_zero (mul_ne_zero hM hN₀.ne') hq.ne_zero) hχp hψ (fun n hn => by
      rw [hind n (Nat.Coprime.coprime_dvd_right (Dvd.intro (N₀ * q) (by ring)) hn), hψeq]
      dsimp only
      rw [hprim n (Nat.Coprime.coprime_dvd_right (Dvd.intro (M * q) (by ring)) hn)])
  obtain ⟨hN, hχψ⟩ := Sigma.mk.inj_iff.1 heq
  subst hN
  have hc : χ = ψ := eq_of_heq hχψ
  subst hc
  refine ⟨hχp, fun n hn => ?_⟩
  rw [hψeq]
  dsimp only
  rw [hprim n (Nat.Coprime.coprime_dvd_right (dvd_mul_right N₀ q) hn)]

end QH
end
end

-- Source module: Development.AutomorphicArithmetic.MeanSquareBounds.RowsOfMem

section

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem rows_of_mem :
    ∀ (z z' : ℝ) (q d : ℕ), 0 < z → 2 * z ≤ z' → q ∈ primePairSetFirst z → d ∈ primeSetTwoBounds z z' q → Rows z z' q d := by
  intro z z' q d hz hzz hq hd
  have hhalf : ∀ t : ℝ, Real.exp t ^ (1 / 2 : ℝ) = Real.exp (t / 2) := by
    intro t
    rw [← Real.exp_mul]
    congr 1
    ring
  simp only [primePairSetFirst, PPset, primeSetTwoBounds, mem_filter, mem_Icc, hhalf] at hq hd
  obtain ⟨⟨_, hq2⟩, hqp, hqm, hqg⟩ := hq
  obtain ⟨⟨_, hd2⟩, hdp, hdm, hdv, hdg⟩ := hd
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hdp.pos
  have hqle : (q : ℝ) ≤ Real.exp z := (Nat.le_floor_iff (Real.exp_pos z).le).1 hq2
  have hdle : (d : ℝ) ≤ Real.exp z' := (Nat.le_floor_iff (Real.exp_pos z').le).1 hd2
  refine ⟨hqp, by omega, (Real.lt_log_iff_exp_lt hq0).2 hqg, (Real.log_le_iff_le_exp hq0).2 hqle,
    hdp, hdm, (Real.lt_log_iff_exp_lt hd0).2 hdg, (Real.log_le_iff_le_exp hd0).2 hdle, ?_, ?_⟩
  · have h1 : Real.exp z ≤ Real.exp (z' / 2) := Real.exp_le_exp.2 (by linarith)
    have h2 : (q : ℝ) < d := lt_of_le_of_lt (hqle.trans h1) hdg
    exact_mod_cast h2
  · intro p hp hp2 hpz
    apply Nat.mod_eq_zero_of_dvd
    refine Dvd.dvd.trans ?_ hdv
    unfold oddM
    rcases hpz with h | h
    · refine Dvd.dvd.mul_left ?_ _
      refine Finset.dvd_prod_of_mem (fun p : ℕ => p) ?_
      rw [mem_filter, mem_Icc]
      have h2 := hp.two_le
      exact ⟨⟨by omega, Nat.le_floor h⟩, hp⟩
    · rw [h]
      exact Dvd.intro _ rfl

end QH
end
end

-- Source module: Development.AutomorphicArithmetic.MeanSquareBounds.PairExists

section

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem pair_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K : ℝ) (N₀ : ℕ), 0 < ε → ε < 1 / 52 → 0 < τ → 1 ≤ K → 0 < N₀ → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ X z' : ℝ, X ≤ Y ^ K → Y ^ (ε / 5) * Real.log Y ^ 2 ≤ z' → z' ≤ K ^ 2 * (Y ^ (ε / 5) * Real.log Y ^ 2) →
      ∃ q d : ℕ, Rows (Y ^ (ε / 5)) z' q d ∧ N₀ < q ∧ GoodQ N₀ C τ Y X (Y ^ (ε / 5)) q ∧ GoodD N₀ C τ Y X (Y ^ (ε / 5)) z' q d := by
  obtain ⟨C, hC, H⟩ := pair_share
  refine ⟨C, hC, fun ε τ K N₀ hε hε' hτ hK hN => ?_⟩
  obtain ⟨Y₁, H1⟩ := H ε τ K (1 / 2) N₀ hε hε' hτ hK (by norm_num) hN
  have hev : ∀ᶠ Y : ℝ in Filter.atTop, (2 * N₀ : ℝ) ≤ Y ^ (ε / 5) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 5)).eventually_ge_atTop _
  obtain ⟨Y₂, H2⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max Y₁ Y₂) (Real.exp 2), fun Y hY X z' hX hz1 hz2 => ?_⟩
  have hY1 : Y₁ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hY2 : Y₂ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hY3 : Real.exp 2 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos 2) hY3
  have hlog : 2 ≤ Real.log Y := (Real.le_log_iff_exp_le hY0).2 hY3
  have hz : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  have hl2 : 2 ≤ Real.log Y ^ 2 := by nlinarith
  have hzz : 2 * Y ^ (ε / 5) ≤ z' := by nlinarith
  obtain ⟨G₁, hG₁, hp1, hc1, H3⟩ := H1 Y hY1 X z' hX hz1 hz2
  have hne1 : G₁.Nonempty := by
    rw [← Finset.card_pos]
    have h0 : (0 : ℝ) < (primePairSetFirst (Y ^ (ε / 5))).card := by exact_mod_cast hp1
    have h1 : (0 : ℝ) < G₁.card := by linarith
    exact_mod_cast h1
  obtain ⟨q, hq⟩ := hne1
  obtain ⟨hgq, G₂, hG₂, hp2, hc2, H4⟩ := H3 q hq
  have hne2 : G₂.Nonempty := by
    rw [← Finset.card_pos]
    have h0 : (0 : ℝ) < (primeSetTwoBounds (Y ^ (ε / 5)) z' q).card := by exact_mod_cast hp2
    have h1 : (0 : ℝ) < G₂.card := by linarith
    exact_mod_cast h1
  obtain ⟨d, hd⟩ := hne2
  have hR := rows_of_mem _ z' q d hz hzz (hG₁ hq) (hG₂ hd)
  refine ⟨q, d, hR, ?_, hgq, H4 d hd⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hR.q_prime.pos
  have h1 := hR.q_gt
  have h2 := Real.log_le_sub_one_of_pos hq0
  have h3 := H2 Y hY2
  have h4 : (N₀ : ℝ) < q := by linarith
  exact_mod_cast h4

end QH
end
end

-- Source module: Development.AutomorphicArithmetic.MeanSquareBounds.pairEx

section

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem pairEx_lift {N L : ℕ} [NeZero L] (h : N ∣ L) (ξ : DirichletCharacter ℂ N) (n : ℕ) (hn : n.Coprime L) :
    DirichletCharacter.changeLevel h ξ (n : ZMod L) = ξ (n : ZMod N) := by
  have ha : IsCoprime (n : ℤ) (L : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  have key := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ h ha
  simpa using key

private theorem pairEx_box (M : ℕ) (hM : 0 < M) (C τ Y X z z' : ℝ) (q d : ℕ) (hR : Rows z z' q d) (hq : 8 * M < q)
    (hQ : GoodQ (8 * M) C τ Y X z q) (hD : GoodD (8 * M) C τ Y X z z' q d)
    (f : ℕ → ℂ) (ξ : DirichletCharacter ℂ (8 * M)) (hf : ∀ n : ℕ, n.Coprime (8 * M) → ξ (n : ZMod (8 * M)) = f n)
    (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hI : Formalism.HC.An.Induces χ (UpperTheory.Top.tw f q d i j) (2 * M * q * d)) :
    Box (8 * M * Real.exp z * Real.exp z' ^ (j : ℕ)) C τ Y X χ := by
  have hq2 : q ≠ 2 := by
    intro h2
    have hm := hR.q_mod
    rw [h2] at hm
    norm_num at hm
  have hqN : ¬ q ∣ 8 * M := by
    intro hd
    have hle := Nat.le_of_dvd (by omega) hd
    omega
  have h8 : ∀ n : ℕ, n.Coprime (2 * M * q * d) → n.Coprime (8 * M) := by
    intro n hn
    have h2 : n.Coprime 2 := Nat.Coprime.coprime_dvd_right ⟨M * q * d, by ring⟩ hn
    have hM' : n.Coprime M := Nat.Coprime.coprime_dvd_right ⟨2 * q * d, by ring⟩ hn
    have h8' : n.Coprime 8 := by simpa using Nat.Coprime.pow_right 3 h2
    exact Nat.Coprime.mul_right h8' hM'
  have hlev : 2 * M * q * d ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hM) hR.q_prime.pos) hR.d_prime.pos).ne'
  obtain ⟨hprim, hval⟩ := hI
  fin_cases j
  · fin_cases i
    · simp at hij
    · have hInd : Ind χ (fun n ↦ ξ n * J q n) (2 * M * q * d) := by
        refine ⟨hprim, fun n hn => ?_⟩
        rw [hval n hn]
        simp [UpperTheory.Top.tw, J, hf n (h8 n hn)]
      have hInd' := ind_drop (8 * M) q (2 * M * q * d) ξ N χ (by omega) hR.q_prime hq2 hqN hlev hInd
      have hB := hQ ξ N χ hInd'
      refine (congrArg (fun Q => Box Q C τ Y X χ) ?_).mpr hB
      simp
  · have hInd : Ind χ (fun n ↦ ξ n * J q n ^ (i : ℕ) * J d n) (8 * M * q * d) := by
      refine ⟨hprim, fun n hn => ?_⟩
      have hn' : n.Coprime (2 * M * q * d) := Nat.Coprime.coprime_dvd_right ⟨4, by ring⟩ hn
      rw [hval n hn']
      simp [UpperTheory.Top.tw, J, hf n (h8 n hn')]
    have hB := hD ξ (i : ℕ) (Nat.lt_succ_iff.mp i.isLt) N χ hInd
    refine (congrArg (fun Q => Box Q C τ Y X χ) ?_).mpr hB
    simp [Real.exp_add, mul_assoc]

private theorem pairEx_g {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h : χ ≠ 1) (y : ℝ) :
    Formalism.HC.An.gChi χ y = Gchi χ y := by
  unfold Formalism.HC.An.gChi
  rw [if_neg h]
  unfold Formalism.HC.An.sumLamChi Gchi
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hfl : 0 < ⌊y⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)
  have hy1 : 1 ≤ y := Nat.floor_pos.mp hfl
  have hny : (n : ℝ) ≤ y := le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
  have hnn : 0 ≤ y / n - 1 := by
    rw [sub_nonneg, le_div_iff₀ (by linarith)]
    linarith
  rw [max_eq_left hnn]

private theorem log_exp_product_bounds (M : ℕ) (hM : 0 < M) (ε Y : ℝ) (hε : 0 < ε)
    (hY : Real.exp (1 + Real.log (8 * M)) ≤ Y) (j : ℕ) (hj : j ≤ 1) :
    Y ^ (ε / 6) ≤ Real.log (8 * M * Real.exp (Y ^ (ε / 5)) * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2) ^ j) ∧
    Real.log (8 * M * Real.exp (Y ^ (ε / 5)) * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2) ^ j)
      ≤ 3 * Y ^ (ε / 5) * Real.log Y ^ 2 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM8 : (1 : ℝ) ≤ 8 * M := by linarith
  have hlog8 : 0 ≤ Real.log (8 * M) := Real.log_nonneg hM8
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_exp (by linarith)) hY
  have hYpos : 0 < Y := by linarith
  have hL : 1 + Real.log (8 * M) ≤ Real.log Y := (Real.le_log_iff_exp_le hYpos).mpr hY
  have hw1 : 1 ≤ Y ^ (ε / 5) := Real.one_le_rpow hY1 (by linarith)
  have h65 : Y ^ (ε / 6) ≤ Y ^ (ε / 5) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  set w := Y ^ (ε / 5) with hw
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hwL : L ^ 2 ≤ w * L ^ 2 := by nlinarith
  have hlogQ : Real.log (8 * M * Real.exp w * Real.exp (w * L ^ 2) ^ j)
      = Real.log (8 * M) + w + j * (w * L ^ 2) := by
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
      Real.log_mul (ne_of_gt (by linarith)) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hj' : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hz0 : 0 ≤ w * L ^ 2 := by positivity
  rw [hlogQ]
  constructor
  · nlinarith
  · have a1 : w ≤ w * L ^ 2 := by nlinarith
    have a2 : (j : ℝ) * (w * L ^ 2) ≤ w * L ^ 2 := by nlinarith
    linarith

theorem pairEx :
    UpperTheory.Top.PairEx := by
  intro M hM eps A heps heps' hA
  obtain ⟨C, hC, hpair⟩ := pair_exists
  obtain ⟨Y₀, hY₀⟩ := hpair eps (eps / 2) A (8 * M) heps heps' (by linarith) hA (by omega)
  obtain ⟨Y₁, hY₁⟩ := kappa4 eps 3 heps heps' (by norm_num)
  refine ⟨max (max Y₀ Y₁) (Real.exp (1 + Real.log (8 * M))), fun Y hY => ?_⟩
  have hYa : Y₀ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hYb : Y₁ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYc : Real.exp (1 + Real.log (8 * M)) ≤ Y := le_trans (le_max_right _ _) hY
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog8 : 0 ≤ Real.log (8 * M) := Real.log_nonneg (by linarith)
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_exp (by linarith)) hYc
  have hz0 : 0 ≤ Y ^ (eps / 5) * Real.log Y ^ 2 := by
    have := Real.log_nonneg hY1
    positivity
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  obtain ⟨q, d, hR, hq, hQ, hD⟩ := hY₀ Y hYa (Y ^ A) (Y ^ (eps / 5) * Real.log Y ^ 2) le_rfl le_rfl
    (le_mul_of_one_le_left hz0 hA2)
  have hq2 : q ≠ 2 := by
    intro h2
    have hm := hR.q_mod
    rw [h2] at hm
    norm_num at hm
  haveI : NeZero (8 * M) := ⟨by omega⟩
  have hM8 : M ∣ 8 * M := Dvd.intro_left 8 rfl
  refine ⟨q, d, ?_, ?_, ?_, ?_⟩
  · refine ⟨hR.q_prime, hR.q_mod, hR.q_gt, hR.q_le, hR.d_prime, hR.d_mod, hR.d_gt, hR.d_le, ?_, ?_⟩
    · exact Nat.dvd_of_mod_eq_zero (hR.d_class q hR.q_prime hq2 (Or.inr rfl))
    · intro p hp hp2 hpl
      exact Nat.dvd_of_mod_eq_zero (hR.d_class p hp hp2 (Or.inl hpl))
  · have hqM : ¬ q ∣ M := fun h => by
      have := Nat.le_of_dvd hM h
      omega
    have hdM : ¬ d ∣ M := fun h => by
      have := Nat.le_of_dvd hM h
      have := hR.q_lt_d
      omega
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hR.q_prime).mpr hqM).symm
      ((Nat.Prime.coprime_iff_not_dvd hR.d_prime).mpr hdM).symm
  · intro ξ i j hij N _ χ hI y hy1 hy2
    have hB := pairEx_box M hM C (eps / 2) Y (Y ^ A) (Y ^ (eps / 5)) (Y ^ (eps / 5) * Real.log Y ^ 2) q d
      hR hq hQ hD (fun a ↦ ξ a) (DirichletCharacter.changeLevel hM8 ξ)
      (fun n hn => pairEx_lift hM8 ξ n hn) i j hij N χ hI
    obtain ⟨hgood, _, hG⟩ := hB
    have hne : χ ≠ 1 := hgood.1
    constructor
    · rw [pairEx_g χ hne]
      exact hG y ⟨hy1, hy2⟩
    · obtain ⟨hk1, hk2⟩ := log_exp_product_bounds M hM eps Y heps hYc (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
      have hk := hY₁ Y hYb _ N χ hk1 hk2 hgood
      have hlog : Real.log Y ≤ Real.log y := Real.log_le_log (by linarith) hy1
      exact le_trans hk (by linarith)
  · intro ρ hρ hρN i j hij N _ χ hI
    have hB := pairEx_box M hM C (eps / 2) Y (Y ^ A) (Y ^ (eps / 5)) (Y ^ (eps / 5) * Real.log Y ^ 2) q d
      hR hq hQ hD ρ.val (DirichletCharacter.changeLevel hρN ρ.χ)
      (fun n hn => pairEx_lift hρN ρ.χ n hn) i j hij N χ hI
    exact hB.1.2.2

end QH
end
end
