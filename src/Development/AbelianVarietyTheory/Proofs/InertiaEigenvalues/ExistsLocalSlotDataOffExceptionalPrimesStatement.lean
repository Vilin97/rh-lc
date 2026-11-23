module

public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorPrimesLtSpecialPrimeThresholdEventuallyStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpSlotConditionsAtLetterStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowJumpsAndCloudInWindowsAlongFamilyStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShiftedJumpUpperBoundLeTwistBoundStatement
public import Formalism.PadicSubsetSums.StableGradedCounts.TOPSgLe
public import Formalism.PadicSubsetSums.CentralIdempotents.ResidueAvoidanceOfPrimes
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSizeBoundsAlongFamily

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Proof.baseSize_bounds_along_family

open Formalism.BasicNotions

theorem baseSize_bounds {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) :
    ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes L,
      2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ L.sc.b := by
  intro W0 hW
  have hls : Formalism.MainNotions.TwistedPlaces.lStar L = LevelStarExponents.lStar L := rfl
  have hl0 : 0 < LevelStarExponents.lStar L := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_pos L
  have hgt : L.sc.b' < LevelStarExponents.lStar L := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_gt L P
  have hleb : LevelStarExponents.lStar L ≤ L.sc.b := hls ▸ Formalism.MainNotions.TwistedPlaces.lStar_le_b L
  have hw := Formalism.MainNotions.TwistedPlaces.w''_le_b' L
  have hb'0 := Formalism.MainNotions.TwistedPlaces.b'_pos L
  have hx := L.sc.one_lt_alt
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx.le
  have hfl0 : (0 : ℝ) ≤ ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (div_nonneg hb'0.le (by linarith))
  have hfl1 : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _

  have h3 : 3 * LevelStarExponents.lStar L ≤ L.sc.b := by
    have hp2 := Formalism.MainNotions.TwistedPlaces.lStar_part2 L
    rw [hls] at hp2
    have hk := Formalism.MainNotions.TwistedPlaces.m_le_k D
    have hm := Formalism.MainNotions.TwistedPlaces.m_ge_one D
    have hn := Formalism.MainNotions.TwistedPlaces.n_ge_one D
    have ht : (7 : ℝ) ≤ D.R.t := by
      have := Formalism.MainNotions.TwistedPlaces.t_ge D; have := Formalism.MainNotions.TwistedPlaces.k_le_r D; have := Formalism.MainNotions.TwistedPlaces.k_ge_five D; linarith
    have hS := L.Sc_pos
    have hLg := Formalism.MainNotions.TwistedPlaces.Lg_nonneg L
    have hn2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by nlinarith
    have hA : 3 * (D.R.m : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by
      have e1 : (3 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by nlinarith
      have e2 : (D.R.m : ℝ) * 3 ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
        mul_le_mul hk e1 (by norm_num) (by linarith)
      linarith
    have : LevelStarExponents.lStar L * (3 * (D.R.m : ℝ)) ≤ D.R.m * L.sc.b :=
      le_trans (mul_le_mul_of_nonneg_left hA hl0.le) hp2
    nlinarith

  have hη := L.etaSz_pos
  have hm := Formalism.MainNotions.TwistedPlaces.m_ge_one D
  have hq : 0 ≤ L.sc.b / LevelStarExponents.lStar L := div_nonneg (by linarith) hl0.le
  have hlow : 2 * (L.sc.b / LevelStarExponents.lStar L) + (D.R.t : ℝ) / 2 + 3 ≤ L.sc.w'' D.R.n := by
    have h1 := P.h0_ge.1
    have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη.le hm
    have h3' := P.mteta
    have ht : (0 : ℝ) ≤ D.R.t := by positivity
    have h4 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
      have : (1 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
      nlinarith
    have h7 : 12 * L.sc.b / LevelStarExponents.lStar L = 12 * (L.sc.b / LevelStarExponents.lStar L) := by ring
    linarith
  rcases hW with rfl | rfl | ⟨t, rfl⟩
  · exact ⟨le_trans hlow (by linarith), le_rfl⟩
  · exact ⟨hlow, by linarith⟩
  · have h1 := L.bT_ge t
    have h2 := Formalism.MainNotions.TwistedPlaces.bT_le_two_mul_b' L P t
    exact ⟨by linarith, by linarith⟩

theorem main : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x), ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
    2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ (Fm.L x a).sc.b := by
  intro eps Fm x hx a W0 hW
  exact baseSize_bounds (Fm.L x a) (Fm.params x hx a) W0 hW

end GlobalTheory.Proof.baseSize_bounds_along_family
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParametersBaseSizeBoundsAlongFamilyStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.baseSize_bounds_along_family : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x), ∀ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
    2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤ W0 ∧ W0 ≤ (Fm.L x a).sc.b := by
  first | exact @GlobalTheory.Proof.baseSize_bounds_along_family.main | exact GlobalTheory.Proof.baseSize_bounds_along_family.main | (intros; apply GlobalTheory.Proof.baseSize_bounds_along_family.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimeThresholdNumericsAlongFamily

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory

theorem lStar_numerics_at_record : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).R.t : ℝ) ≤ (Fm.L x a).etaSz ∧ 0 < (Fm.L x a).etaSz ∧ 0 ≤ (Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a) ∧
    0 ≤ (Fm.L x a).Sc ∧ 1 < LevelStarExponents.lStar (Fm.L x a) ∧
    2 * (Fm.L x a).etaSz + (Fm.D x a).R.t + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < LevelStarExponents.lStar (Fm.L x a) ∧
    ((Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3) * LevelStarExponents.lStar (Fm.L x a) ≤
      2 * (Fm.L x a).sc.b * (LevelStarExponents.lStar (Fm.L x a) - 1) := by
  intro eps Fm x hx a
  have P := Fm.params x hx a
  set L := Fm.L x a with hLdef
  have e : Formalism.MainNotions.TwistedPlaces.lStar L = LevelStarExponents.lStar L := rfl
  have hls := Formalism.MainNotions.TwistedPlaces.lStar_pos L
  have h7 := Formalism.MainNotions.TwistedPlaces.seven_lt_lStar L P
  have hmD := Formalism.MainNotions.TwistedPlaces.lStar_mul_Den L
  have hDen := Formalism.MainNotions.TwistedPlaces.Den_ge L
  have hDp := Formalism.MainNotions.TwistedPlaces.Den_pos L
  rw [e] at hls h7 hmD
  have h1 := P.lstar1
  have h2 := P.lstar2
  have hb := Formalism.MainNotions.TwistedPlaces.one_le_b L
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht := Formalism.MainNotions.TwistedPlaces.t_ge_one (Fm.D x a)
  have hk := Formalism.MainNotions.TwistedPlaces.k_ge_five (Fm.D x a)
  have hmk := Formalism.MainNotions.TwistedPlaces.m_le_k (Fm.D x a)
  have hm1 := Formalism.MainNotions.TwistedPlaces.m_ge_one (Fm.D x a)
  have hn := Formalism.MainNotions.TwistedPlaces.n_ge_one (Fm.D x a)
  have hL1 := Formalism.MainNotions.TwistedPlaces.L_ge_one L
  have hbl : 0 ≤ L.sc.b / LevelStarExponents.lStar L := div_nonneg (by linarith) hls.le
  have h8 : 8 * L.sc.b / LevelStarExponents.lStar L = 8 * (L.sc.b / LevelStarExponents.lStar L) := by ring
  rw [h8] at h2

  have hDen2 : 2 * ((Fm.D x a).R.m : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.Den L := by
    unfold Formalism.MainNotions.TwistedPlaces.Den
    have hn2 : (1 : ℝ) ≤ ((Fm.D x a).R.n : ℝ) ^ 2 := by nlinarith
    have hLg0 : (0 : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
    have h0 : (0 : ℝ) ≤ ((Fm.D x a).R.n : ℝ) * ((Fm.D x a).R.t : ℝ) ^ 2 *
        (((Fm.D x a).R.N (Fm.D x a).R.m : ℝ) + (Fm.D x a).R.t) * Formalism.MainNotions.TwistedPlaces.large₂ L ^ 2 := by positivity
    have hA : (2 : ℝ) ≤ L.Sc + (Fm.D x a).R.t + Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
    have hB : (1 : ℝ) ≤ ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2 := by nlinarith
    have : 2 * ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2 ≤
        ((Fm.D x a).R.k : ℝ) * ((Fm.D x a).R.n : ℝ) ^ 2 * (L.Sc + (Fm.D x a).R.t + Formalism.MainNotions.TwistedPlaces.large₂ L) := by
      nlinarith
    nlinarith
  have hlb : 2 * LevelStarExponents.lStar L ≤ L.sc.b := by nlinarith
  have hb' := Formalism.MainNotions.TwistedPlaces.b'_pos L
  have hq : L.sc.b / LevelStarExponents.lStar L * LevelStarExponents.lStar L = L.sc.b := div_mul_cancel₀ _ hls.ne'
  refine ⟨P.t_le_eta, he, hbl, hS.le, by linarith, h2, ?_⟩
  nlinarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimeThresholdNumericsAlongFamilyStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.specialPrimeThreshold_numerics_along_family : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).R.t : ℝ) ≤ (Fm.L x a).etaSz ∧ 0 < (Fm.L x a).etaSz ∧ 0 ≤ (Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a) ∧
    0 ≤ (Fm.L x a).Sc ∧ 1 < LevelStarExponents.lStar (Fm.L x a) ∧
    2 * (Fm.L x a).etaSz + (Fm.D x a).R.t + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < LevelStarExponents.lStar (Fm.L x a) ∧
    ((Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3) * LevelStarExponents.lStar (Fm.L x a) ≤
      2 * (Fm.L x a).sc.b * (LevelStarExponents.lStar (Fm.L x a) - 1) := by
  first | exact @GlobalTheory.lStar_numerics_at_record | exact GlobalTheory.lStar_numerics_at_record | (intros; apply GlobalTheory.lStar_numerics_at_record <;> assumption)
end
end

-- Source module: Formalism.PadicSubsetSums.StableGradedCounts.TOPSgRange

section

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.TOP

theorem geomRatioBound : SgRange := by
  intro ℓ s b H hH h1 h2 h3
  have hs0 : (0 : ℝ) < s - 1 := by linarith
  have hlt : s - 1 < (ℓ : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hspos : (0 : ℝ) < s := by linarith
  have step1 : H / ((ℓ : ℝ) - 1) ≤ H / (s - 1) := by
    rw [div_le_div_iff₀ hl0 hs0]
    nlinarith [mul_le_mul_of_nonneg_left hlt.le hH]
  have step2 : H / (s - 1) ≤ 2 * b / s := by
    rw [div_le_div_iff₀ hs0 hspos]
    linarith
  exact step1.trans step2

end Formalism.IrreducibleCountingLemmas.TOP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimes

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.LocalPositionData

theorem position_data_exist : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.conductorPrimes_lt_specialPrimeThreshold_eventually Fm
  refine ⟨x0, fun x hx hx1 a _ l hl hlS => ?_⟩
  obtain ⟨hqS, hdS, hsS⟩ := hx0 x hx hx1 a
  obtain ⟨htη, hη, hB, hSc, hls1, hls2, hH⟩ := GlobalTheory.T.specialPrimeThreshold_numerics_along_family Fm x hx1 a
  have ht1 : 1 ≤ (Fm.D x a).R.t := by
    have := (Fm.D x a).R.rank_add_five_le; omega
  have htR : (0 : ℝ) ≤ (Fm.D x a).R.t := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_, fun h => absurd (hsS l h) (not_lt.2 hlS.le)⟩, ?_⟩
  · have : (7 : ℝ) < l := by linarith
    exact_mod_cast (show 5 ≤ l by exact_mod_cast (show (5 : ℝ) ≤ l by linarith))
  · have : ((Fm.D x a).R.t : ℝ) + 1 < l := by linarith
    exact_mod_cast this
  · intro h; rw [h] at hlS; linarith
  · intro h; rw [h] at hlS; linarith
  intro hexc j hj1 hjm n _ up τ
  have hfinL : ∀ c, (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.lowJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin (Fm.D x a).R.m => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) - ((Fm.D x a).hc (τ c)).b i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.lowT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  have hfinC : ∀ c, (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.cloudJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin ((Fm.D x a).R.k - 1) => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) + ((Fm.D x a).hc (τ c)).v i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.cloudT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  set Fl : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)) with hFl
  set Fc : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)) with hFc
  have hdat : ∀ c, ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
      (∀ z ∈ Fl c, |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
        2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
          |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
      (∀ z ∈ Fc c, W0 ≤ (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
        (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
          W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1) := by
    intro c
    obtain ⟨hlo, W0, hW0, hcl⟩ := GlobalTheory.T.lowJumps_and_cloud_in_windows_along_family Fm x hx1 a j hj1 hjm (up c) (τ c)
    refine ⟨W0, hW0, fun z hz => hlo z ((GlobalTheory.PositionData.mem_intPts (hfinL c) z).1 hz),
      fun z hz => hcl z ((GlobalTheory.PositionData.mem_intPts (hfinC c) z).1 hz)⟩
  set hh : ZMod n → ℕ := fun c => GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) with hhh
  have hhle : ∀ c, (hh c : ℝ) ≤ (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 := by
    intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, hW2⟩ := GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0
    have := GlobalTheory.T.shiftedJumpUpperBound_le_twist_bound (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 ht1 htη hB hSc hlo hcl hW1
    show ((GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) : ℕ) : ℝ) ≤ _
    linarith
  have hsg : ∀ c, (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) ≤ 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) := by
    intro c
    have hl2 : 2 ≤ l := hl.two_le
    set W := (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 with hW
    have hW0 : 0 ≤ W := le_trans (Nat.cast_nonneg _) (hhle c)
    have h1 := Formalism.IrreducibleCountingLemmas.TOP.carryFloorLeGeom n l hh ⌊W⌋₊ hl2 (fun c' => Nat.le_floor (hhle c')) c
    have h2 : ((⌊W⌋₊ : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ W / ((l : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right (Nat.floor_le hW0)
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      linarith
    have h3 := Formalism.IrreducibleCountingLemmas.TOP.geomRatioBound l (LevelStarExponents.lStar (Fm.L x a)) (Fm.L x a).sc.b W hW0 hls1 hlS hH
    have h4 : (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) = (Formalism.IrreducibleCountingLemmas.TOP.sg n l hh c : ℝ) := rfl
    rw [h4, ← mul_div_assoc]
    linarith
  refine ⟨hh, fun c => GlobalTheory.PositionData.wS (up c) (Fl c) (Fc c), fun c => GlobalTheory.PositionData.etaS (Fm.D x a).R.t (Fl c),
    up, fun c => GlobalTheory.PositionData.US (up c) (Fl c) (Fc c), ?_, ?_⟩
  · intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, -⟩ := GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0
    have hex : ∀ m : ℤ, W0 + (-(Fm.L x a).etaSz - 2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) - 3) ≤ (m : ℝ) →
        (m : ℝ) ≤ W0 + ((Fm.L x a).Sc + (Fm.L x a).etaSz + (Fm.L x a).etaSz +
          2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) + 4) → ¬ (l : ℤ) ∣ m :=
      fun m h1 h2 hd => hexc ⟨hl, hlS, W0, hW0, m, ⟨h1, h2⟩, hd⟩
    have hσP : Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus
      apply Int.le_floor.mpr
      rw [mul_div_assoc]; exact hsg c
    have hT1 : 2 * (Fm.L x a).etaSz + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < (l : ℝ) := by linarith
    exact GlobalTheory.T.jump_position_conditions_at_letter l (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a)) (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c)
      ht1 htη hB hSc hlo hcl hW1 hex (hsg c) hσP hT1
  · intro c b
    rw [GlobalTheory.PositionData.count_US]
    have hm : b ∈ Fl c ∪ Fc c ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c) := by
      rw [Finset.mem_union, GlobalTheory.PositionData.mem_intPts (hfinL c), GlobalTheory.PositionData.mem_intPts (hfinC c)]
      unfold AdmissibleParameterJ.JW
      rw [Set.mem_union]; tauto
    rw [← hm]
    split_ifs <;> simp_all

end GlobalTheory.LocalPositionData
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.exists_localPositionData_off_exceptional_primes : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  first | exact @GlobalTheory.LocalPositionData.position_data_exist | exact GlobalTheory.LocalPositionData.position_data_exist | (intros; apply GlobalTheory.LocalPositionData.position_data_exist <;> assumption)
end
end
