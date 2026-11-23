module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElements

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), 1 ≤ M → NormOne H.d M p → (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) ∧ p % M = 1 % M := by
  intro R H M p _ h
  obtain ⟨π, hN, hB, hA⟩ := h
  have h' : GlobalTheory.Mem.An.NormOne H.d M p := ⟨π.1, π.2, hN, hB, hA⟩
  exact ⟨(GlobalTheory.Mem.An.normOne_iff_host R H M p).1 h',
    (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd H.d M p (by have := H.hyp.2.2.2.1; omega) h').1⟩

end GlobalTheory.EX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModEqOneOfNorm

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem.LevelChoice

theorem mod_eq_one_of_norm {E : Type} [Field E] [NumberField E] (c : E →+* E) (π : 𝓞 E) (p m : ℕ) (hm : 1 < m)
    (hn : (π : E) * c (π : E) = (p : E)) (hc : π - 1 ∈ Ideal.span {((m : ℕ) : 𝓞 E)}) : p % m = 1 := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hc
  have hπ : (π : E) = 1 + (a : E) * (m : E) := by
    have h := congrArg (fun x : 𝓞 E => (x : E)) ha
    simp only [map_mul, map_natCast, map_sub, map_one] at h
    change (a : E) * (m : E) = (π : E) - 1 at h
    rw [h]; ring
  have hai : IsIntegral ℤ (a : E) := a.2
  have hci : IsIntegral ℤ (c (a : E)) := hai.map c.toIntAlgHom
  have hmi : IsIntegral ℤ ((m : ℕ) : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hx : algebraMap ℚ E (((p : ℚ) - 1) / m) = (a : E) + c a + (m : E) * ((a : E) * c a) := by
    rw [map_div₀, map_sub, map_natCast, map_natCast, map_one, ← hn, hπ, map_add (f := _), map_one, map_mul, map_natCast]
    field_simp
    ring
  have hxi : IsIntegral ℤ (algebraMap ℚ E (((p : ℚ) - 1) / m)) := by
    rw [hx]
    exact (hai.add hci).add (hmi.mul (hai.mul hci))
  have hqi : IsIntegral ℤ (((p : ℚ) - 1) / m) :=
    (isIntegral_algebraMap_iff ).1 hxi
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hqi
  have hk' : ((p : ℚ) - 1) = (k : ℚ) * m := by
    have : (k : ℚ) = ((p : ℚ) - 1) / m := by simpa using hk
    rw [this]; field_simp
  have hz : (p : ℤ) = 1 + (m : ℤ) * k := by
    have : ((p : ℤ) : ℚ) = ((1 + (m : ℤ) * k : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h1 : ((p % m : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, hz, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hm)
  exact_mod_cast h1

theorem exists_levCh : ∀ (P : PreCh) (du : P.Word → ℕ) (Ds Ga : ℝ), (∀ u, 0 < du u) → 0 < Ds → 1 < Ga → (∀ u, ∃ (π : 𝓞 P.H.E) (p : ℕ), p.Prime ∧ p ≠ P.H.pde ∧ p ≠ P.H.pde' ∧ (π : P.H.E) ∈ P.H.K ∧ (π : P.H.E) * P.H.conj (π : P.H.E) = (p : P.H.E) ∧ π - 1 ∈ Ideal.span {((P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 : ℕ) : 𝓞 P.H.E)} ∧ (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ (1 + 1 / ((P.R.f : ℝ) * P.R.k)) * ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ L : LevCh P, L.duStar = du ∧ L.Dstar = Ds ∧ L.GamP = Ga := by
  intro P du Ds Ga hdu hDs hGa h
  choose π p hp h1 h2 hK hN hc hlo hhi using h
  have hq8 : P.H.q % 8 = 3 := P.H.hyp.2.2.1
  have hd16 : P.H.d % 16 = 7 := P.H.hyp.2.2.2.1
  have hn : 0 < P.H.QS := P.H.QS_pos
  have hm : 1 < P.H.QS * P.H.q * P.H.d := by
    have hq : 0 < P.H.q := by omega
    have hd : 0 < P.H.d := by omega
    have h1 : P.H.q ≤ P.H.QS * P.H.q := Nat.le_mul_of_pos_left _ hn
    have h2 : P.H.QS * P.H.q ≤ P.H.QS * P.H.q * P.H.d := Nat.le_mul_of_pos_right _ hd
    omega
  have hcond : ∀ u, p u % (P.H.QS * P.H.q * P.H.d) = 1 := fun u => by
    refine mod_eq_one_of_norm (P.H.conj : P.H.E →+* P.H.E) (π u) (p u) _ hm (hN u) ?_
    refine Ideal.span_singleton_le_span_singleton.2 ?_ (hc u)
    exact Nat.cast_dvd_cast (Dvd.intro _ rfl)
  exact ⟨{ T := p, T_prime := hp, T_cond := hcond, piT := π, piT_K := hK, piT_norm := hN, piT_cong := hc,
           T_ne_pde := fun u => ⟨h1 u, h2 u⟩, duStar := du, duStar_pos := hdu, Dstar := Ds, Dstar_pos := hDs,
           GamP := Ga, one_lt_gammaP := hGa, T_win := fun u => ⟨hlo u, hhi u⟩ }, rfl, rfl, rfl⟩

end GlobalTheory.Mem.LevelChoice
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem exists_levCh_of_levelPrime : LevelPrime → ∀ (eps cs : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → 0 < cs → Std C → ∃ x0 : ℝ, ∀ (cD ch : ℝ) (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (du : P.Word → ℕ) (Ds : ℝ), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → (∀ u, 0 < du u) → 0 < Ds → (∀ u, cs * P.R.m * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ Lv : LevCh P, Lv.duStar = du ∧ Lv.Dstar = Ds ∧ Lv.GamP = GamS C s P.R := by
  intro hLP eps cs C he he' hcs hC
  obtain ⟨x1, h1⟩ := hLP eps cs he he' hcs
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 41 1 he one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  refine ⟨max (max x1 x2) (max x3 (max 2 ((1 / cs) ^ 4))), ?_⟩
  intro cD ch s P q1 a b c du Ds hs hx hOK hdu hDs hwin
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4, hx5⟩ := hx
  obtain ⟨-, -, hb, -⟩ := h2 s hs hx2
  obtain ⟨-, -, hr, hkr, -, -, hL1, -, -, -, -, -, -, -, -, hm, -⟩ := h3 s P.R hs hx3 hOK.rank
  have hx0 : 0 < s.x := by linarith
  have hxone : 1 ≤ s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hb0 : 0 < s.b := Real.exp_pos _
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hm2 : (2 : ℝ) ≤ P.R.m := by exact_mod_cast P.R.two_le_m
  have hmf : (P.R.m : ℝ) ≤ P.R.f := by exact_mod_cast P.R.m_le_f
  have hGam : 1 < GamS C s P.R := by
    unfold GamS
    rw [Real.one_lt_exp_iff]
    have : (0 : ℝ) < P.R.f := by linarith
    have : (0 : ℝ) < P.R.m := by linarith
    have : 0 < C.CGam := by linarith
    have : 0 < s.L := by linarith
    positivity

  have hk : (P.R.k : ℝ) ≤ s.x ^ 5 := by
    have : (P.R.k : ℝ) ≤ P.R.r := by exact_mod_cast hkr
    have e : s.x ^ (5 : ℝ) = s.x ^ 5 := by exact_mod_cast Real.rpow_natCast s.x 5
    exact this.trans (hr.trans_eq e)
  have hb41 : s.x ^ 41 ≤ s.b := by
    have e : s.x ^ (41 : ℝ) = s.x ^ 41 := by exact_mod_cast Real.rpow_natCast s.x 41
    rw [e, Real.rpow_one] at hb
    exact (le_mul_of_one_le_right (by positivity) hX1).trans hb
  have hk8 : 2 * (P.R.k : ℝ) ^ 8 ≤ s.b := by
    have h8 : (P.R.k : ℝ) ^ 8 ≤ (s.x ^ 5) ^ 8 := pow_le_pow_left₀ (by positivity) hk 8
    calc 2 * (P.R.k : ℝ) ^ 8 ≤ s.x * (s.x ^ 5) ^ 8 := mul_le_mul hx4 h8 (by positivity) hx0.le
      _ = s.x ^ 41 := by ring
      _ ≤ s.b := hb41
  have hg : ∀ i, (P.H.g i : ℝ) ≤ s.b ^ 9 := fun i => by
    calc (P.H.g i : ℝ) ≤ 2 * ((P.R.k : ℝ) * s.b) ^ 8 := (hOK.val.2.2.2.2.1 i).2
      _ = (2 * (P.R.k : ℝ) ^ 8) * s.b ^ 8 := by ring
      _ ≤ s.b * s.b ^ 8 := mul_le_mul_of_nonneg_right hk8 (by positivity)
      _ = s.b ^ 9 := by ring

  have hcm : 1 ≤ cs * P.R.m := by
    have a1 : 1 / cs ≤ s.x ^ ((1 : ℝ) / 4) := by
      have a0 : ((1 / cs) ^ 4) ^ ((1 : ℝ) / 4) ≤ s.x ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hx5 (by norm_num)
      have e : ((1 / cs) ^ 4) ^ ((1 : ℝ) / 4) = 1 / cs := by
        have := Real.pow_rpow_inv_natCast (x := 1 / cs) (n := 4) (by positivity) (by norm_num)
        simpa using this
      rwa [e] at a0
    have a2 : s.x ^ ((1 : ℝ) / 4) ≤ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) :=
      Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    have a3 : 1 / cs ≤ P.R.m := a1.trans (a2.trans hm)
    rw [div_le_iff₀ hcs] at a3
    linarith
  have hXL : s.X' ≤ Real.exp (cs * P.R.m * s.L) := by
    unfold Scale.X'
    refine Real.exp_le_exp.2 ?_
    have a1 : s.x ^ (s.eps / 3) ≤ s.L :=
      Real.rpow_le_rpow_of_exponent_le hxone (by rw [hs]; linarith)
    exact a1.trans (le_mul_of_one_le_left (by linarith) hcm)
  have hp : (P.H.pde : ℝ) < s.X' := by
    rcases hOK.lev _ P.H.pde_level.1 with ⟨i, hi⟩ | h
    · exact absurd hi (P.H.pde_ne_g i).1
    · exact h
  have hp' : (P.H.pde' : ℝ) < s.X' := by
    rcases hOK.lev _ P.H.pde_level.2 with ⟨i, hi⟩ | h
    · exact absurd hi (P.H.pde_ne_g i).2
    · exact h
  refine GlobalTheory.Mem.LevelChoice.exists_levCh P du Ds _ hdu hDs hGam fun u => ?_
  have hT0 : 0 < (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)) := by
    have : (0 : ℝ) < du u := by exact_mod_cast hdu u
    have : 0 < GamS C s P.R := by linarith
    positivity
  obtain ⟨T, hT, hlo, hhi, hN⟩ := h1 s P.R P.H.condN P.H.d (P.H.g 0) (P.H.g 1) _ hs hx1 hOK.rank hOK.val.modRow
    (P.H.g_prime 0).one_le (P.H.g_prime 1).one_le (hg 0) (hg 1) hT0 (hwin u)
  have hXT : s.X' ≤ T :=
    hXL.trans (((Real.le_log_iff_exp_le hT0).1 (hwin u)).trans hlo)
  have hM : 1 ≤ P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 := by
    have hn : 0 < P.H.QS := P.H.QS_pos
    have hq : 0 < P.H.q := P.H.hyp.1.pos
    have hd : 0 < P.H.d := P.H.hyp.2.1.pos
    have h0 := (P.H.g_prime 0).pos
    have h1 := (P.H.g_prime 1).pos
    exact Nat.succ_le_of_lt (by positivity)
  obtain ⟨⟨π, hK, hπ, hc⟩, -⟩ := GlobalTheory.EX.normOne_host P.R P.H _ T hM hN
  refine ⟨π, T, hT, ?_, ?_, hK, hπ, hc, hlo, hhi⟩
  · rintro rfl; linarith
  · rintro rfl; linarith

end GlobalTheory.EX.OB
end
end
