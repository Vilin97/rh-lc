module

public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.Columns.ChainInst
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
public import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.PrincipalCongruenceLevelK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_shift {m c : ℕ} (hm : m ≤ c) {a d : E}
    (ha : IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * a)) (hd : IntAt P d) :
    IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  have e : ((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d) =
      ((qOf P : E) ^ (m : ℤ))⁻¹ * a + (qOf P : E) ^ (c - m) * d := by
    rw [zpow_natCast]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  rw [e]
  exact ha.add ((intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) _).mul hd)

theorem prinCong_maps {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) {x : Sp E N} (hx : x ∈ LocE.sclLat P (qOf P) N e) :
    (k : Sp E N ≃ₗ[E] Sp E N) x ∈ LocE.sclLat P (qOf P) N e := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  rw [ciMem_sclLat] at hx ⊢
  have hxs : x ∈ stdAt E N P := by
    rw [ciMem_stdAt]
    intro l
    obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
    have h1 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) m).mul (hx l)
    rw [hm, zpow_natCast] at h1
    rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h1
  have hd := mem_stdAt.1 (hk x hxs)
  intro l
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
  have hmc : m ≤ c := by have := he l.1; omega
  have e1 : (k : Sp E N ≃ₗ[E] Sp E N) x l = x l + (qOf P : E) ^ c * ((((qOf P : E) ^ c)⁻¹ • (k.1 x - x)) l) := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul]
    show _ = x l + ((k : Sp E N ≃ₗ[E] Sp E N) x l - x l)
    ring
  rw [e1, hm]
  have hxl := hx l
  rw [hm] at hxl
  exact intAt_shift P hmc hxl (hd l)

theorem prinCong_stab {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) : (k : Sp E N ≃ₗ[E] Sp E N) ∈ stabL E N (LocE.sclLat P (qOf P) N e) := by
  intro x
  refine ⟨fun h => ?_, prinCong_maps P he hk⟩
  have h1 := prinCong_maps P he ((prinCong N P c).inv_mem hk) h
  have e2 : ((k⁻¹ : GLint E N P) : Sp E N ≃ₗ[E] Sp E N) ((k : Sp E N ≃ₗ[E] Sp E N) x) = x :=
    LinearEquiv.symm_apply_apply _ x
  rwa [e2] at h1

theorem principal_congruence_le_level_k1_at {N : ℕ} (r c : ℕ) (hc : 0 < c) : prinCong N P c ≤ twK1H P N r c := by
  intro k hk
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  refine ⟨⟨k.2, ?_⟩, prinCong_stab P (fun l => ?_) hk, prinCong_stab P (fun l => ?_) hk, fun w hw => ?_⟩
  · exact prinCong_stab P (N := N + 0) (fun l => by split_ifs <;> omega) hk
  · unfold kOneLastExponents; split_ifs <;> omega
  · unfold twistedLevelExponent; split_ifs <;> omega
  · have hws : w ∈ stdAt E N P := by
      have h0 := prinCong_maps P (e := fun _ => 0) (fun _ => by omega) ((prinCong N P c).one_mem) (x := w) ?_
      · rw [ciMem_sclLat] at h0; rw [ciMem_stdAt]; intro l; simpa using h0 l
      · rw [ciMem_sclLat] at hw ⊢
        intro l
        have h1 := hw l
        unfold twistedLevelExponent at h1
        split_ifs at h1 with hl
        · simpa using h1
        · have h2 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) c).mul h1
          rw [zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h2
          simpa using h2
    have hd := mem_stdAt.1 (hk w hws)
    rw [ciMem_sclLat]
    intro l
    have := hd l
    simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast] at this ⊢
    exact this

theorem principal_congruence_le_level_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ),
    0 < c → prinCong N P c ≤ twK1H P N r c :=
  by
  intro E _ _ _ P N r c hc
  exact principal_congruence_le_level_k1_at P r c hc

end GlobalTheory.PrincipalCongruenceLevelK1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1Statement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.principal_congruence_le_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ), 0 < c → prinCong N P c ≤ twK1H P N r c := by
  first | exact @GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 | exact GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 | (intros; apply GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEq

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.SumRowType

variable {E : Type} [Field E]

theorem atN_sumE_last {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t : ℕ) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) n = if n = t then 1 else 0 := by
  rw [Loc.atN, dite_eq_left (Nat.lt_succ_self n)]
  have h := sumE_last (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)
  have e : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Br.iL (rfl : n + 1 = n + 1) := rfl
  rw [e, h, Units.val_one, one_mul]
  rfl

theorem atN_sumE_up {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t s : ℕ) (hs : s < n) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) s = Loc.atN (j (Loc.eN E n t)) s := by
  rw [Loc.atN, dite_eq_left (by omega), Loc.atN, dite_eq_left hs]
  have h := congrFun (prH_sumE (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)) ⟨s, hs⟩
  have e1 : prH E (rfl : n + 1 = n + 1) (Loc.eN E (n + 1) t) = Loc.eN E n t := by
    funext i
    rw [prH_apply]
    rfl
  rw [e1] at h
  rw [← h, prH_apply]
  rfl

end GlobalTheory.SumRowType

namespace GlobalTheory.SumRowType

open Matrix in
theorem det_sumE {E : Type} [Field E] {n : ℕ} (r : ℕ) (hr : r ≤ n) (j : Sp E n ≃ₗ[E] Sp E n) :
    (Matrix.of fun s t : Fin (n + 1 - r) =>
        Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1).toLinearMap (Loc.eN E (n + 1) (r + t.1))) (r + s.1)).det =
      (Matrix.of fun s t : Fin (n - r) => Loc.atN (j.toLinearMap (Loc.eN E n (r + t.1))) (r + s.1)).det := by
  obtain ⟨m, rfl⟩ : ∃ m, n = r + m := ⟨n - r, by omega⟩
  have hm : r + m + 1 - r = m + 1 := by omega
  have hm' : r + m - r = m := by omega
  set A := Matrix.of fun s t : Fin (r + m + 1 - r) =>
    Loc.atN ((sumE (rfl : r + m + 1 = r + m + 1) j 1).toLinearMap (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) with hA
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm).symm A]
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm').symm]
  rw [Matrix.det_succ_row _ (Fin.last m)]
  rw [Finset.sum_eq_single (Fin.last m)]
  · have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) (Fin.last m) = 1 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + m))) (r + m) = 1
      rw [atN_sumE_last, if_pos rfl]
    rw [e1, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, one_mul]
    congr 1
    ext s t
    show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) =
      Loc.atN (j (Loc.eN E (r + m) (r + t.1))) (r + s.1)
    exact atN_sumE_up j _ _ (by have := s.2; omega)
  · intro b _ hb
    have hb' : b.1 < m := Fin.val_lt_last hb
    have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) b = 0 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + b.1))) (r + m) = 0
      rw [atN_sumE_last, if_neg (by omega)]
    rw [e1, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lamQB_sumE : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  intro E K _ _ _ _ P ξ N n hN r hr j
  subst hN
  unfold LocE.lamQB
  rw [det_sumE r hr j]

end GlobalTheory.SumRowType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEqStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.rowTypeCharacter_blockSumOne_eq : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  first | exact @GlobalTheory.SumRowType.lamQB_sumE | exact GlobalTheory.SumRowType.lamQB_sumE | (intros; apply GlobalTheory.SumRowType.lamQB_sumE <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecompositionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

theorem _root_.GlobalTheory.T.twisted_k1_block_decomposition : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ g : GLint E N P, g ∈ twK1H P N r (c + 1) → ∃ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b ∧ (extI hN P j)⁻¹ * g ∈ prinCong N P (c + 1) := by
  first | exact @GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 | exact GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 | (intros; apply GlobalTheory.BlockDecompositionK1.exists_block_of_twisted_k1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelQuotientEqTwistedTop

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopLevQ

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem lamQB_prinCong (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N : ℕ} (r c : ℕ) (hc : 0 < c)
    (k : GLint E N P) (hk : k ∈ prinCong N P c) : LocE.lamQB ξ r N k.1.toLinearMap = 1 := by
  have h1 := redGL_of_prinCong hc hk
  refine twLamQB_red_one P ξ le_rfl k.1 fun s t _ _ _ _ => ⟨glint_entry k s t, ?_⟩
  have h2 := congrArg (fun M : GL (Fin N) (𝓞 E ⧸ P.asIdeal) => (M : Matrix (Fin N) (Fin N) (𝓞 E ⧸ P.asIdeal)) s t) h1
  simp only [redGL_val, Units.val_one, Matrix.one_apply] at h2
  exact h2

theorem levI_ext {N : ℕ} {P : HeightOneSpectrum (𝓞 E)} {A B : LevI E K N P} (e : A.H = B.H)
    (e' : ∀ k (h1 : k ∈ A.H) (h2 : k ∈ B.H), A.lam ⟨k, h1⟩ = B.lam ⟨k, h2⟩) : A = B := by
  obtain ⟨H, lam⟩ := A
  obtain ⟨H', lam'⟩ := B
  obtain rfl : H = H' := e
  obtain rfl : lam = lam' := MonoidHom.ext fun a => e' a.1 a.2 a.2
  rfl

theorem level_congruence_eq_twisted_k1 (P : HeightOneSpectrum (𝓞 E)) (hu : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {N n : ℕ} (hN : N = n + 1) (r b c : ℕ) (hn : n = r + b) :
    levCong hN P c ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩ = kOneLevel P N r (c + 1) ξ := by
  set l : Lev (𝓞 E ⧸ P.asIdeal) K n := ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩
  have hH : (levCong hN P c l).H = twK1H P N r (c + 1) := by
    refine le_antisymm (sup_le ?_ (GlobalTheory.T.principal_congruence_le_twisted_k1 P r (c + 1) c.succ_pos)) fun g hg => ?_
    · rintro _ ⟨j, hj, rfl⟩
      exact GlobalTheory.T.block_ext_mem_twisted_k1 P hu hN r b (c + 1) hn j hj
    · obtain ⟨j, hj, hb⟩ := GlobalTheory.T.twisted_k1_block_decomposition P hN r b c hn g hg
      exact (mem_levCong hN c l g).2 ⟨j, hj, hb⟩
  refine levI_ext hH fun k h1 h2 => ?_
  obtain ⟨j, hj, hb⟩ := (mem_levCong hN c l k).1 h1
  rw [levCong_lam hN c l h1 hj hb]
  apply Units.ext
  have hjK : extI hN P j ∈ twK1H P N r (c + 1) := GlobalTheory.T.block_ext_mem_twisted_k1 P hu hN r b (c + 1) hn j hj
  have hbK : (extI hN P j)⁻¹ * k ∈ twK1H P N r (c + 1) := GlobalTheory.T.principal_congruence_le_twisted_k1 P r (c + 1) c.succ_pos hb
  have hk : (⟨k, h2⟩ : twK1H P N r (c + 1)) = ⟨_, hjK⟩ * ⟨_, hbK⟩ := Subtype.ext (mul_inv_cancel_left _ _).symm
  show _ = ((kOneCharacter P N r (c + 1) ξ).toHomUnits ⟨k, h2⟩ : K)
  rw [MonoidHom.coe_toHomUnits, hk, map_mul]
  show _ = LocE.lamQB ξ r N (extI hN P j).1.toLinearMap * LocE.lamQB ξ r N ((extI hN P j)⁻¹ * k).1.toLinearMap
  rw [lamQB_prinCong P ξ r (c + 1) c.succ_pos _ hb, mul_one, extI_val, GlobalTheory.T.rowTypeCharacter_blockSumOne_eq P ξ hN r (by omega) j.1,
    GlobalTheory.TopLaw.lamQB_eq_red ξ hn j hj]
  rfl

end Gen

section Top

theorem levQTop_eq_twTt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  intro X Pr R _ sel S mu hX hPr hsel _ _
  funext Q
  have hu : ((qOf Q.1 : ℕ) : 𝓞 X.E) ∉ Q.1.asIdeal ^ 2 :=
    (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel ⟨Q.1, by classical exact Finset.mem_union_right _ Q.2⟩).1.2
  exact level_congruence_eq_twisted_k1 Q.1 hu _ (N_m_succ R) R.r (R.m * R.t) (4 * R.m) (rank_X'_eq R)

end Top
end GlobalTheory.TopLevQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelQuotientEqTwistedTopStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.level_quotient_eq_twisted_top : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  first | exact @GlobalTheory.TopLevQ.levQTop_eq_twTt | exact GlobalTheory.TopLevQ.levQTop_eq_twTt | (intros; apply GlobalTheory.TopLevQ.levQTop_eq_twTt <;> assumption)
end
end
