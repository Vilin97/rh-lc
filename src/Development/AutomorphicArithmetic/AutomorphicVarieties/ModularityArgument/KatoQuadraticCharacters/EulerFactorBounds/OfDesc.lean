module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
public import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassInvariantDescentCoprimeLevelModPowStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPow
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
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClassStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowPropertiesStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPowStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_level_mul_pow_of_invariant_mod_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow | exact GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow | (intros; apply GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelPowPrimeFourthPowerDescent

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.DescInv

theorem gamma_anti {a b : ℕ} (h : a ∣ b) :
    CongruenceSubgroup.Gamma b ≤ CongruenceSubgroup.Gamma a := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have key : ∀ (x : ℤ) (c : ZMod b), (x : ZMod b) = c → (x : ZMod a) = ZMod.castHom h (ZMod a) c := by
    intro x c hx; rw [← hx, map_intCast]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key _ _ h1, map_one]
  · simpa using key _ _ h2
  · simpa using key _ _ h3
  · rw [key _ _ h4, map_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem lev_of_dvd {X : Tower Ω ε} {a b : ℕ} (h : a ∣ b) {f : X.K} (hf : Lev X a f) : Lev X b f :=
  fun γ hγ => hf γ (gamma_anti h hγ)

theorem exists_dvd_pow_mul_coprime (M : ℕ) (hM : 0 < M) :
    ∀ N : ℕ, 0 < N → ∃ e b : ℕ, 0 < b ∧ Nat.Coprime M b ∧ N ∣ M ^ e * b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN
  by_cases hc : Nat.Coprime M N
  · exact ⟨0, N, hN, hc, by simp⟩
  · have hd0 : Nat.gcd M N ≠ 0 := (Nat.gcd_pos_of_pos_left N hM).ne'
    have hd1 : 1 < Nat.gcd M N := by
      have : Nat.gcd M N ≠ 1 := hc
      omega
    obtain ⟨N', hN'⟩ := Nat.gcd_dvd_right M N
    have hN'pos : 0 < N' := by
      rcases Nat.eq_zero_or_pos N' with h0 | h0
      · rw [h0, mul_zero] at hN'; omega
      · exact h0
    have hlt : N' < N := by
      rw [hN']; nlinarith
    obtain ⟨e, b, hb, hcop, hdiv⟩ := ih N' hlt hN'pos
    refine ⟨e + 1, b, hb, hcop, ?_⟩
    have : M ^ (e + 1) * b = M * (M ^ e * b) := by ring
    rw [this, hN']
    exact Nat.mul_dvd_mul (Nat.gcd_dvd_left M N) hdiv

end GlobalTheory.KZ.ES.DescInv


open GlobalTheory.KZ.ES.DescInv in
theorem GlobalTheory.KZ.ES.desc_pow_four : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (l n M : ℕ), l.Prime → 0 < M → 6 * l ∣ M → ∀ f : X.Kˣ,
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) →
    ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n M hl hM h6 f hf
  classical
  obtain ⟨M'', hM''pos, hM''⟩ := X.level (f : X.K)
  haveI : NeZero M'' := ⟨hM''pos.ne'⟩

  have hex : ∀ r : SL(2, ZMod M''), ∃ (g : X.Kˣ) (L : ℕ), 0 < L ∧ Lev X L (g : X.K) ∧
      ∀ γ ∈ CongruenceSubgroup.Gamma M,
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ = r →
        X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n) := by
    intro r
    by_cases hr : ∃ γ₀ ∈ CongruenceSubgroup.Gamma M,
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ₀ = r
    · obtain ⟨γ₀, hγ₀, hr0⟩ := hr
      obtain ⟨g, hg⟩ := hf γ₀ hγ₀
      obtain ⟨L, hL, hLg⟩ := X.level (g : X.K)
      refine ⟨g, L, hL, hLg, fun γ _ hrγ => ?_⟩
      have hδ : γ * γ₀⁻¹ ∈ CongruenceSubgroup.Gamma M'' := by
        rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, hrγ, hr0, mul_inv_cancel]
      have hγ : γ = (γ * γ₀⁻¹) * γ₀ := by group
      rw [hγ, map_mul, X.sl_mul, hM'' _ hδ, hg]
    · exact ⟨1, 1, one_pos, fun γ _ => by simp, fun γ hγ hrγ => absurd ⟨γ, hγ, hrγ⟩ hr⟩
  choose G L hLpos hLev hG using hex
  set L₀ : ℕ := ∏ r, L r with hL₀
  have hL₀pos : 0 < L₀ := Finset.prod_pos fun r _ => hLpos r
  have hLdvd : ∀ r, L r ∣ L₀ := fun r => Finset.dvd_prod_of_mem L (Finset.mem_univ r)
  obtain ⟨e, b, hb, hcop, hdiv⟩ := exists_dvd_pow_mul_coprime M hM (M'' * L₀) (Nat.mul_pos hM''pos hL₀pos)
  have hdiv' : M'' * L₀ ∣ M ^ (e + 1) * b :=
    hdiv.trans (Nat.mul_dvd_mul_right (pow_dvd_pow M (Nat.le_succ e)) b)
  have hMa : 0 < M ^ (e + 1) := pow_pos hM _
  have hMMa : M ∣ M ^ (e + 1) := dvd_pow_self M (Nat.succ_ne_zero e)
  have h6a : 6 * l ∣ M ^ (e + 1) := h6.trans hMMa
  have hcopa : Nat.Coprime (M ^ (e + 1)) b := Nat.Coprime.pow_left _ hcop
  have hfLev : Lev X (M ^ (e + 1) * b) (f : X.K) :=
    lev_of_dvd ((dvd_mul_right M'' L₀).trans hdiv') hM''
  have hstep : ∀ γ ∈ CongruenceSubgroup.Gamma (M ^ (e + 1)), ∃ g : X.Kˣ, Lev X (M ^ (e + 1) * b) (g : X.K) ∧
      X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n) := by
    intro γ hγ
    have hγM : γ ∈ CongruenceSubgroup.Gamma M := gamma_anti hMMa hγ
    let r := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ
    exact ⟨G r, lev_of_dvd (((hLdvd r).trans (dvd_mul_left L₀ M'')).trans hdiv') (hLev r), hG r γ hγM rfl⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.classInvariant_descent_coprimeLevel_modPow ε X l n (M ^ (e + 1)) b hl hMa hb h6a hcopa f hfLev hstep
  have hFstep : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ,
      X.sl (ofSL γ) (((f ^ 4 * h ^ (l ^ n) : X.Kˣ)) : X.K) = (f ^ 4 * h ^ (l ^ n) : X.Kˣ) * (g : X.K) ^ (l ^ n) := by
    intro γ hγ
    obtain ⟨g, hg⟩ := hf γ hγ
    have hne : X.sl (ofSL γ) (h : X.K) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (X.sl (ofSL γ)).injective]; exact h.ne_zero
    refine ⟨g ^ 4 * Units.mk0 _ hne * h⁻¹, ?_⟩
    have hh0 : (h : X.K) ≠ 0 := h.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_inv_eq_inv_val, map_mul, map_pow, hg,
      mul_pow, inv_pow]
    have hp : (h : X.K) ^ (l ^ n) ≠ 0 := pow_ne_zero _ hh0
    field_simp
    ring
  obtain ⟨k, h', hh'⟩ := GlobalTheory.T.exists_level_mul_pow_of_invariant_mod_pow ε X l n M (e + 1) hl hM (f ^ 4 * h ^ (l ^ n)) (by simpa using hh) hFstep
  refine ⟨k, h * h', ?_⟩
  convert hh' using 1
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelPowPrimeFourthPowerDescentStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_level_pow_prime_fourth_power_descent : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M : ℕ), l.Prime → 0 < M → 6 * l ∣ M → ∀ f : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.desc_pow_four | exact GlobalTheory.KZ.ES.desc_pow_four | (intros; apply GlobalTheory.KZ.ES.desc_pow_four <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OfDesc

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups

theorem UpperTheory.V.Z.Kato.Nb.sEsLev : UpperTheory.V.Z.Kato.Nb.SEsLev := by
  unfold SEsLev
  intro Ω _ _ _ ε X l _ N w hN b hb n
  have hl : Nat.Prime l := Fact.out
  obtain ⟨⟨c, hcA, hbu⟩, hinv⟩ := hb
  have api := sApi Ω ε X l n
  have cls := sCls Ω ε X l n
  have ev := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  have hsub : ∀ (x y x' y' : ℤ_[l]) (a e : ℕ), (l : ℤ_[l]) ^ n ∣ x - x' → (l : ℤ_[l]) ^ n ∣ y - y' →
      (l : ℤ_[l]) ^ n ∣ x ^ a * y ^ e - x' ^ a * y' ^ e := by
    intro x y x' y' a e hx hy
    have h : x ^ a * y ^ e - x' ^ a * y' ^ e = (x ^ a - x' ^ a) * y ^ e + x' ^ a * (y ^ e - y' ^ e) := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left (hx.trans (sub_dvd_pow_sub_pow x x' a)) _)
      (dvd_mul_of_dvd_right (hy.trans (sub_dvd_pow_sub_pow y y' e)) _)
  have cong : ∀ u u' : Fin 2 → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ u i - u' i) →
      (AdicCompletion.eval (idl l) (X.Kl l) n) (b u - b u') = 0 := by
    intro u u' h

    rw [hbu u, hbu u', ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact api.2.2.2.2.1 _ _ _ (hsub _ _ _ _ _ _ (h 0) (h 1))
  refine ⟨cong, ?_, ?_⟩
  · intro t u
    rw [hbu, hbu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    have hi : (i : ℕ) + (w - i) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.2)
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [show t ^ w = t ^ (i : ℕ) * t ^ (w - i) by rw [← pow_add, hi]]
    ring
  · intro u
    have hbA : b u ∈ X.A l := by
      rw [hbu]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcA i)
    obtain ⟨φ0, hφ, hd⟩ := X.j_hol
    obtain ⟨f, hfU, hf⟩ := GlobalTheory.T.exists_unit_eval_eq_kummer_class ε X ⟨φ0, hd, hφ⟩ l n (b u) hbA
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 6 * l * N * l ^ n := ⟨_, rfl⟩
    have hMpos : 0 < M := by
      rw [hM]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hl.pos) hN) (pow_pos hl.pos n)
    have hMd : 6 * l ∣ M := ⟨N * l ^ n, by rw [hM]; ring⟩
    have hNM : (N : ℤ) ∣ (M : ℤ) := ⟨6 * l * l ^ n, by rw [hM]; push_cast; ring⟩
    have hlM : (l : ℤ) ∣ (M : ℤ) := ⟨6 * N * l ^ n, by rw [hM]; push_cast; ring⟩
    have hlnM : (l : ℤ) ^ n ∣ (M : ℤ) := ⟨6 * l * N, by rw [hM]; push_cast; ring⟩
    have key : ∀ (d : ℕ) (x y : ℤ), (d : ℤ) ∣ y - x → ((x : ZMod d) = (y : ZMod d)) :=
      fun d x y h => (ZMod.intCast_eq_intCast_iff_dvd_sub x y d).mpr h
    have hdl : ∀ x : ℤ, (M : ℤ) ∣ x → (l : ℤ_[l]) ^ n ∣ (x : ℤ_[l]) := by
      intro x hx
      obtain ⟨e, he⟩ := hlnM.trans hx
      exact ⟨(e : ℤ_[l]), by rw [he]; push_cast; ring⟩
    have hγ : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ,
        (X.sl (ofSL γ)) (f : X.K) = (f : X.K) * (g : X.K) ^ l ^ n := by
      intro γ hγM
      rw [CongruenceSubgroup.Gamma_mem] at hγM
      obtain ⟨h00, h01, h10, h11⟩ := hγM
      have d00 : (M : ℤ) ∣ 1 - γ 0 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h00)
      have d01 : (M : ℤ) ∣ 0 - γ 0 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h01)
      have d10 : (M : ℤ) ∣ 0 - γ 1 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h10)
      have d11 : (M : ℤ) ∣ 1 - γ 1 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h11)
      have hG : γ ∈ Gam N l := by
        show γ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
        refine Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N γ).mpr ⟨?_, ?_, ?_⟩,
          CongruenceSubgroup.Gamma0_mem.mpr ?_⟩
        · simpa using key N _ _ (hNM.trans d00)
        · simpa using key N _ _ (hNM.trans d11)
        · simpa using key N _ _ (hNM.trans d10)
        · simpa using key l _ _ (hlM.trans d10)
      have hact := congrFun (hinv γ hG) u
      simp only [GlobalTheory.KZ.Tower.act, LinearMap.coe_mk, AddHom.coe_mk] at hact
      rw [Betti.toGQ_sl] at hact
      have hcu : ∀ i, (l : ℤ_[l]) ^ n ∣ (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) i - u i := by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 - u 0
              = ((γ 0 0 - 1 : ℤ) : ℤ_[l]) * u 0 + ((γ 0 1 : ℤ) : ℤ_[l]) * u 1 := by
            simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring
          rw [e]
          exact dvd_add (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d00)) _)
            (dvd_mul_of_dvd_left (hdl _ (by simpa using d01)) _)
        · have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 - u 1
              = ((γ 1 0 : ℤ) : ℤ_[l]) * u 0 + ((γ 1 1 - 1 : ℤ) : ℤ_[l]) * u 1 := by
            simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring
          rw [e]
          exact dvd_add (dvd_mul_of_dvd_left (hdl _ (by simpa using d10)) _)
            (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d11)) _)
      have heq : (AdicCompletion.eval (idl l) (X.Kl l) n) (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
          = X.cls l n f := by
        rw [← hf, ← sub_eq_zero, ← map_sub]
        exact cong _ u hcu
      have h2 := KmapA.eval_kmap X l (X.sl (ofSL γ)).toRingEquiv n _ f heq
      rw [hact, hf] at h2
      obtain ⟨g, hg⟩ := (ev.2.1 _ _).mp h2.symm
      refine ⟨g, ?_⟩
      have := congrArg Units.val hg
      simpa using this
    obtain ⟨k', h, hlev⟩ := GlobalTheory.T.exists_level_pow_prime_fourth_power_descent ε X l n M hl hMpos hMd f hγ
    refine ⟨n + k', f ^ 4 * h ^ l ^ n, Nat.le_add_right _ _, ?_, ?_, ?_⟩
    · intro W hW
      obtain ⟨g, hg⟩ := hfU W hW
      refine ⟨g ^ 4 * h, ?_⟩
      have hg0 : (g : X.K) ≠ 0 := g.ne_zero
      have hh0 : (h : X.K) ≠ 0 := h.ne_zero
      have e : ((f ^ 4 * h ^ l ^ n : X.Kˣ) : X.K) / ((g ^ 4 * h : X.Kˣ) : X.K) ^ l ^ n
          = ((f : X.K) / (g : X.K) ^ l ^ n) ^ 4 := by
        push_cast
        field_simp
        ring
      rw [e, map_pow, hg, one_pow]
    · have e : M * l ^ k' = 6 * l * N * l ^ (n + k') := by rw [hM, pow_add]; ring
      rw [← e]
      push_cast
      exact hlev
    · have r1 : UpperTheory.Kd.K4.Rep X l n f (b u) := hf
      have r2 := cls.2.2.1 f (b u) 4 r1
      have r3 : UpperTheory.Kd.K4.Rep X l n (h ^ l ^ n) 0 := by
        show _ = _
        rw [map_zero]
        have h3 := (ev.2.1 (h ^ l ^ n) 1).mpr ⟨h, by simp⟩
        rw [h3, ev.2.2.2.1]
      have h4 := (cls.2.1 _ _ _ _ r2 r3).1
      simpa using h4
end
end
