module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegularStatement
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobius
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesCuspidalCharacterGLFinStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInductionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLDegRegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotModEqOfLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingCuspidalCharacterGLRootPowerSumCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRootPowerSumMapGaloisEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiGPairingEqChGPairingStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterShintaniPsiLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductShintaniLiftGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLDegRegStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupportStatement
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCuspMulStarChG

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_GL_toLin' {F : Type} [Field F] (m : ℕ) (f : Module.End F (Fin m → F) → ℂ) :
    ∑ᶠ x : GL (Fin m) F, f (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) =
      ∑ᶠ g ∈ {g : Module.End F (Fin m → F) | IsUnit g}, f g := by
  rw [← finsum_mem_univ]
  refine finsum_mem_eq_of_bijOn
    (fun x : GL (Fin m) F => (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F) : Module.End F (Fin m → F)))
    ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro x _
    exact (Units.isUnit x).map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
  · intro x _ y _ h
    exact Units.ext (Matrix.toLin'.injective h)
  · intro g hg
    have h : IsUnit ((Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).symm g) := IsUnit.map _ hg
    refine ⟨h.unit, Set.mem_univ _, ?_⟩
    exact (Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).apply_symm_apply g

theorem finsum_cusp_mul_star_chG : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k l : ℕ, 0 < m → ∑ᶠ x, cusp θ m k x * star (chG (rootSum θ l) m x) = (-1) ^ (m - 1) * (Nat.card (GL (Fin m) F) : ℂ) * (((Finset.range m).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ m - 1)])).card : ℂ) := by
  intro F _ _ θ hθ m k l hm
  have hr : Module.finrank F (Fin m → F) = m := by simp
  have h := ipGL_psi_rootSum F (Fin m → F) θ hθ (by rw [hr]; exact hm) k l
  rw [hr, ipGL, ← finsum_GL_toLin', glCard] at h
  rw [mul_assoc, ← h, mul_finsum]
  refine finsum_congr fun x => ?_
  simp only [cusp, psiG, chG, Matrix.charpoly_toLin', mul_assoc]

end GlobalTheory.Shin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGaloisPairingEqPmOnePrimeDegree

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.PairPM

theorem rootSum_zero {K : Type} [Field K] (θ : AlgebraicClosure K →* ℂ) (P : K[X]) :
    rootSum θ 0 P = (P.natDegree : ℂ) := by
  simp only [rootSum, pow_zero, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem natCard_ext (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Nat.card F' = Nat.card F ^ Module.finrank F F' := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F; haveI := Fintype.ofFinite F'
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := F')]

theorem sum_cusp_eq_zero {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m e : ℕ) (hm : 0 < m)
    (h : ∀ a, ¬ e * Nat.card K ^ a ≡ 0 [MOD Nat.card K ^ m - 1]) :
    ∑ᶠ x, cusp θ m e x = 0 := by
  have H := finsum_cusp_mul_star_chG K θ hθ m e 0 hm
  have hf : (Finset.range m).filter (fun i => e * Nat.card K ^ i ≡ 0 [MOD Nat.card K ^ m - 1]) = ∅ := by
    ext i; simp [h i]
  rw [hf] at H
  have hc : ∀ x : GL (Fin m) K, star (chG (rootSum θ 0) m x) = (m : ℂ) := by
    intro x; simp [chG, rootSum_zero, Matrix.charpoly_natDegree_eq_dim]
  simp only [hc, Finset.card_empty, Nat.cast_zero, mul_zero] at H
  rw [← finsum_mul] at H
  exact (mul_eq_zero.1 H).resolve_right (by exact_mod_cast hm.ne')

theorem gram_lift {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (q l m k : ℕ) (hq : 2 ≤ q)
    (hl : 0 < l) (hm : 0 < m) (hK : Nat.card K = q ^ l) (hreg : Reg q (l * m) k) :
    ∀ i j, i < l → j < l → ∑ᶠ x, cusp θ m (k * q ^ i) x * star (chG (rootSum θ (k * q ^ j)) m x) =
      if i = j then (((-1 : ℤ) ^ (m - 1) : ℤ) : ℂ) * (Nat.card (GL (Fin m) K) : ℂ) else 0 := by
  intro i j hi hj
  rw [finsum_cusp_mul_star_chG K θ hθ m _ _ hm, hK]
  have h3 := (reg_step_of_dvd q l m k hq hl hm hreg).2.2 i j
  have hf : (Finset.range m).filter (fun a => k * q ^ i * (q ^ l) ^ a ≡ k * q ^ j [MOD (q ^ l) ^ m - 1]) =
      if i = j then {0} else ∅ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ha, h⟩
      obtain ⟨rfl, rfl⟩ := (h3 a hi hj ha).1 h
      simp
    · intro h
      by_cases hij : i = j
      · rw [if_pos hij, Finset.mem_singleton] at h
        subst h; subst hij
        exact ⟨hm, (h3 0 hi hi hm).2 ⟨rfl, rfl⟩⟩
      · rw [if_neg hij] at h
        simp at h
  rw [hf]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

theorem hfree_J {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card K) p.1 p.2 ∧
      (2 ≤ p.1 ∨ ¬ p.2 ≡ 0 [MOD Nat.card K - 1])) → HFree (J θ L (deg L))
  | [], _ => by intro h; simp [deg] at h
  | p :: L, hL => by
    have hp := hL p (List.mem_cons_self ..)
    have hL' : ∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card K) p.1 p.2 ∧
        (2 ≤ p.1 ∨ ¬ p.2 ≡ 0 [MOD Nat.card K - 1]) := fun p' h' => hL p' (List.mem_cons_of_mem _ h')
    rw [J_cons]
    have hdeg : deg (p :: L) = p.1 + deg L := by simp [deg]
    exact GlobalTheory.T.hyperplaneFixerSumVanishes_harishChandraInduction K p.1 (deg L) (deg (p :: L)) hdeg _ _
      (GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular K θ hθ p.1 p.2 hp.1 hp.2.1).1
      (GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular K θ hθ L (fun p' h' => ⟨(hL' p' h').1, (hL' p' h').2.1⟩) _ rfl)
      (GlobalTheory.T.hyperplaneFixerSumVanishes_cuspidalCharacterGLFiniteField K θ hθ p.1 p.2 hp.2.2) (hfree_J θ hθ L hL')

end GlobalTheory.Shin.PairPM

namespace GlobalTheory.Shin.PairPM

theorem pairing_pm_one : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k n : ℕ, 0 < m → n = Module.finrank F F' * m → Reg (Nat.card F) n k → ∃ z : ℤ, (z = 1 ∨ z = -1) ∧
    ∑ᶠ x, psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n x *
      star (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n x) = z * (Nat.card (GL (Fin n) F') : ℂ) := by
  intro F F' _ _ _ _ s hl _ ι θ hθ m k n hm hn hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have hK : Nat.card F' = Nat.card F ^ Module.finrank F F' := natCard_ext F F'
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq : 2 ≤ q := Finite.one_lt_card
  have hl0 : 0 < l := hl.pos
  have hl2 : 2 ≤ l := hl.two_le
  have hreg' : Reg q (l * m) k := hn ▸ hreg
  have hR := reg_step_of_dvd q l m k hq hl0 hm hreg'
  have hLL : liftL q l [(n, k)] = (List.range l).map (fun i => (m, k * q ^ i)) := by
    simp [liftL, hn, Nat.mul_div_cancel_left _ hl0]
  obtain ⟨hdeg, hmem⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [(n, k)] hq hl0 (by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨by rw [hn]; exact Nat.mul_pos hl0 hm, by rw [hn]; exact dvd_mul_right _ _, hreg⟩)
  have hdeg' : deg (liftL q l [(n, k)]) = n := by rw [hdeg]; simp [deg]
  have hY := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ (liftL q l [(n, k)]) (fun p hp => by rw [hK]; exact hmem p hp) n hdeg'.symm
  have hF := hfree_J θ hθ (liftL q l [(n, k)]) (by
    intro p hp
    refine ⟨(hmem p hp).1, by rw [hK]; exact (hmem p hp).2, ?_⟩
    rw [hLL, List.mem_map] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases h2 : 2 ≤ m
    · exact Or.inl h2
    · right
      have h1 : m = 1 := by omega
      have := hR.2.1 (by nlinarith) i
      rw [h1, mul_one] at this
      rw [hK]
      exact this)
  rw [hdeg'] at hF
  refine ⟨((-1 : ℤ) ^ (m - 1)) ^ l, ?_, ?_⟩
  · rw [← pow_mul]
    exact neg_one_pow_eq_or ℤ _
  · rw [GlobalTheory.T.finsum_psiG_mul_star_eq_chG F' _ n _ hY hF]
    have hS : chG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n =
        chG (fun P => ∏ j ∈ Finset.range l, rootSum θ (k * q ^ j) P) n := by
      funext x
      simp only [chG]
      exact GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k _
    rw [hS]
    have hZ := GlobalTheory.T.pairing_cuspidalCharacterGL_rootPowerSumCharacter F' θ m (fun i => k * q ^ i) ((-1) ^ (m - 1))
      (fun i => sum_cusp_eq_zero θ hθ m _ hm (by
        intro a
        rw [hK, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
        exact hR.2.1 (by nlinarith) _))
      l (gram_lift θ hθ q l m k hq hl0 hm hK hreg') (List.range l) (Finset.range l) List.nodup_range
      (fun i hi => List.mem_range.1 hi) (fun j hj => Finset.mem_range.1 hj) (by simp) n
      (by rw [hn, List.length_range, mul_comm])
    rw [List.toFinset_range, if_pos rfl, List.length_range, ← hLL] at hZ
    have hst : ∀ (a b : GL (Fin n) F' → ℂ), ∑ᶠ x, a x * star (b x) = star (∑ᶠ x, b x * star (a x)) := by
      intro a b
      rw [show star (∑ᶠ x, b x * star (a x)) = starAddEquiv (∑ᶠ x, b x * star (a x)) from rfl,
        map_finsum _ (Set.toFinite _)]
      refine finsum_congr fun x => ?_
      simp [star_mul]
    rw [hst, hZ]
    push_cast
    simp [star_pow]

end GlobalTheory.Shin.PairPM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGaloisPairingEqPmOnePrimeDegreeStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.cuspidal_galois_pairing_eq_pm_one_prime_degree : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k n : ℕ, 0 < m → n = Module.finrank F F' * m → Reg (Nat.card F) n k → ∃ z : ℤ, (z = 1 ∨ z = -1) ∧ ∑ᶠ x, psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n x * star (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n x) = z * (Nat.card (GL (Fin n) F') : ℂ) := by
  first | (exact @GlobalTheory.Shin.PairPM.pairing_pm_one) | (exact GlobalTheory.Shin.PairPM.pairing_pm_one) | (intros; apply GlobalTheory.Shin.PairPM.pairing_pm_one  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinCoordsArithVar

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_const_mul {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (a : ℂ) (f : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') :
    shLift s (fun x => a * f x) δ = a * shLift s f δ := by
  unfold shLift
  split_ifs <;> simp

theorem shLift_cusp_kills_J : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ n k : ℕ, 0 < n → Module.finrank F F' ∣ n → Reg (Nat.card F) n k →
    Kills (shLift s (cusp (pullθ ι θ) n k)) (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hln hreg
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Module.Finite F F' := Module.Finite.of_finite
  haveI : IsGalois F F' := inferInstance
  have hΓ : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := IsGalois.card_aut_eq_finrank F F'
  haveI : Finite (F' ≃ₐ[F] F') := Nat.finite_of_card_ne_zero (by rw [hΓ]; exact hl.ne_zero)
  letI : Fintype (F' ≃ₐ[F] F') := Fintype.ofFinite _
  haveI : Fact (Nat.card (F' ≃ₐ[F] F')).Prime := ⟨hΓ ▸ hl⟩
  have hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
    intro t
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Subgroup.zpowers s) with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.1 h) hs
    · rw [h]; exact Subgroup.mem_top t

  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy hxy
    apply ι.toRingHom.injective
    exact hθ (ι x) (ι y) ((map_ne_zero ι.toRingHom).2 hx) ((map_ne_zero ι.toRingHom).2 hy) hxy
  set l := Module.finrank F F' with hldef
  set q := Nat.card F with hqdef
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcardF' : Nat.card F' = q ^ l := Module.natCard_eq_pow_finrank

  obtain ⟨X, hX, hXg, hXs⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc
  have hc2 : c = 1 ∨ c = -1 := neg_one_pow_eq_or ℂ (n - 1)
  set X' : GHat F F' n → ℂ := fun g => c * X g with hX'
  have hX'v : X' ∈ Virt ℂ ℂ (GHat F F' n) := by
    rcases hc2 with h | h
    · have : X' = X := by funext g; simp [hX', h]
      rw [this]; exact hX
    · have : X' = -X := by funext g; simp [hX', h]
      rw [this]; exact neg_mem hX
  have hcusp : cusp (pullθ ι θ) n k = fun x => c * psiG (rootSum (pullθ ι θ) k) n x := rfl
  have hX's : ∀ δ, X' (inl δ * inr s) = shLift s (cusp (pullθ ι θ) n k) δ := by
    intro δ
    rw [hcusp, shLift_const_mul, ← hXs δ]

  obtain ⟨hchar, hnorm⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hclc : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    rw [hcusp]
    simp only
    rw [((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y]
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s hgen n _ _ hclc hclc
  rw [hnorm] at hiso
  have hGne : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'
  have hnorm' : ∑ᶠ δ, X' (inl δ * inr s) * star (X' (inl δ * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [hX's]
    apply mul_left_cancel₀ hGne
    rw [hiso, mul_comm]

  obtain ⟨hdeg, hlift⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [(n, k)] hq2 hl.pos (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨hn, hln, hreg⟩)
  have hdegn : deg (liftL q l [(n, k)]) = n := by rw [hdeg]; simp [deg]
  have hYchar : IsChar ℂ ℂ (J θ (liftL q l [(n, k)]) n) := by
    apply GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ _ _ n hdegn.symm
    intro p hp
    rw [hcardF']
    exact hlift p hp
  have hYst : ∀ g, J θ (liftL q l [(n, k)]) n (galAct F F' n s g) = J θ (liftL q l [(n, k)]) n g :=
    GlobalTheory.T.harishChandraProduct_shintaniLift_galois F F' θ s [(n, k)] n hdegn.symm

  obtain ⟨m, hm⟩ := hln
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; omega
    · exact h
  obtain ⟨z, hz, hzsum⟩ := GlobalTheory.T.cuspidal_galois_pairing_eq_pm_one_prime_degree F F' s hl hs ι θ hθ m k n hm0 hm hreg
  have hpair : ∑ᶠ g, X' (inl g) * star (J θ (liftL q l [(n, k)]) n g)
      = ((if c = 1 then z else -z : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    have : (fun g : GL (Fin n) F' => X' (inl g) * star (J θ (liftL q l [(n, k)]) n g))
        = fun g => c * (X (inl g) * star (J θ (liftL q l [(n, k)]) n g)) := by
      funext g; simp only [hX']; ring
    rw [this, ← mul_finsum]
    simp only [hXg]
    rw [hzsum]
    rcases hc2 with h | h
    · rw [h]; simp
    · rw [h]; have : (-1 : ℂ) ≠ 1 := by norm_num
      simp [this]
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (if c = 1 then z else -z)) := by
    rw [hΓ]
    intro hd
    have hd' : (l : ℤ) ∣ z := by
      split_ifs at hd
      · exact hd
      · exact (dvd_neg).1 hd
    have h1 : (l : ℤ) ∣ 1 := by
      rcases hz with h | h
      · rwa [h] at hd'
      · rw [h] at hd'; exact (dvd_neg).1 hd'
    have : l ∣ 1 := by exact_mod_cast h1
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  have hK := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X' hX'v hnorm'
    (J θ (liftL q l [(n, k)]) n) hYchar hYst _ hpair hndvd
  have hfun : (fun δ => X' (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := funext hX's
  rw [hfun] at hK
  exact hK

end GlobalTheory.Shin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsCuspDivisibleDegree

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.shintani_lift_kills_cusp_divisible_degree : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n) := by
  first | (exact @GlobalTheory.Shin.shLift_cusp_kills_J) | (exact GlobalTheory.Shin.shLift_cusp_kills_J) | (intros; apply GlobalTheory.Shin.shLift_cusp_kills_J  <;> assumption)
end
end
