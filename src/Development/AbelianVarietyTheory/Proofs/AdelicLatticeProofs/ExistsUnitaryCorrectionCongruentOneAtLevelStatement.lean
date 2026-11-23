module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNatSmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimes
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflectionsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLawsStatement
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimesStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.normOne_approximation_at_level_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), (∀ x, c (c x) = x) → c ≠ 1 → ∀ (u : E) (N D : ℕ), u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ (∃ t : ℕ, t.Coprime N ∧ ∃ b : 𝓞 E, (t : E) * (u' / u - 1) = (D : E) * (b : E)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ (∃ b : 𝓞 E, (s : E) * (u' - 1) = (D : E) * (b : E)) ∧ ∃ b : 𝓞 E, (s : E) * (u'⁻¹ - 1) = (D : E) * (b : E) := by
  first | exact @GlobalTheory.UnRep.normOne_approx | exact GlobalTheory.UnRep.normOne_approx | (intros; apply GlobalTheory.UnRep.normOne_approx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormOneReflectionCorrectionAtLevel

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_nat_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem ..)

theorem exists_nat_smul_map_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (φ : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, (d : E) • φ v ∈ L := by
  classical
  choose d hd hdL using exists_nat_smul_mem_of_span L hL
  obtain ⟨S, hS⟩ := hfg
  refine ⟨∏ s ∈ S, d (φ s), Finset.prod_pos fun s _ => hd _, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul S _ (Finset.mem_coe.1 hx), Nat.cast_mul, mul_smul,
      Nat.cast_smul_eq_nsmul E (∏ s ∈ S.erase x, d (φ s))]
    exact L.toAddSubmonoid.nsmul_mem (hdL _) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    have h1 : φ (a • x) = (a : E) • φ x := φ.map_smul (a : E) x
    rw [h1, smul_comm]
    exact L.smul_mem a hx

theorem exists_refl_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL x u N D hx hu hN hD
  have hap := (GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG x hx).1
  let φ : (Fin n → E) →ₗ[E] (Fin n → E) :=
    { toFun := fun v => (hermE c G v x / hermE c G x x) • x
      map_add' := by
        intro v w
        rw [← add_smul, ← add_div]
        congr 2
        simp [hermE, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        rw [RingHom.id_apply, smul_smul, ← mul_div_assoc]
        congr 2
        simp [hermE, Finset.mul_sum, mul_assoc] }
  obtain ⟨d, hd, hdL⟩ := exists_nat_smul_map_mem L hfg hL φ
  have hap' : ∀ a v, refl c G x a *ᵥ v = v + (a - 1) • φ v := by
    intro a v
    rw [hap]
    show _ = v + (a - 1) • ((hermE c G v x / hermE c G x x) • x)
    rw [smul_smul, mul_div_assoc]
  obtain ⟨u', hu', ⟨t, ht, b, hb⟩, s, hs, ⟨b₁, hb₁⟩, b₂, hb₂⟩ :=
    GlobalTheory.T.normOne_approximation_at_level_primes F E c hG.1 hG.2.1 u N (D * d) hu hN (Nat.mul_pos hD hd)
  have key : ∀ (a : E) (b : 𝓞 E), (s : E) * (a - 1) = ((D * d : ℕ) : E) * (b : E) →
      ∀ v ∈ L, s • (refl c G x a *ᵥ v) ∈ L := by
    intro a b hb v hv
    rw [hap', smul_add]
    refine L.add_mem (L.smul_mem s hv) ?_
    have : s • ((a - 1) • φ v) = ((D : 𝓞 E) * b) • ((d : E) • φ v) := by
      show (s : E) • ((a - 1) • φ v) = (((D : 𝓞 E) * b : 𝓞 E) : E) • ((d : E) • φ v)
      rw [smul_smul, smul_smul, hb]
      congr 1
      push_cast
      ring
    rw [this]
    exact L.smul_mem _ (hdL v hv)
  refine ⟨u', hu', ⟨t, ht, fun v hv => ⟨b • ((d : E) • φ v), L.smul_mem b (hdL v hv), ?_⟩⟩,
    s, hs, fun v hv => ⟨key _ _ hb₁ v hv, key _ _ hb₂ v hv⟩⟩
  rw [hap', add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul E t, ← Nat.cast_smul_eq_nsmul E D]
  show _ = (D : E) • ((b : E) • ((d : E) • φ v))
  rw [smul_smul, smul_smul, smul_smul, hb]
  congr 1
  push_cast
  ring

end GlobalTheory.UnRep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormOneReflectionCorrectionAtLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_norm_one_reflection_correction_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UnRep.exists_refl_correction | exact GlobalTheory.UnRep.exists_refl_correction | (intros; apply GlobalTheory.UnRep.exists_refl_correction <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCorrectionCongruentOneAtLevel

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Correct

variable {E : Type} [Field E] {n : ℕ}

theorem exists_nat_mulVec_mem [NumberField E] (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • (M *ᵥ v) ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem
  | exact _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem
  | (apply _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem ..)

theorem congAt_mul {L : Submodule (𝓞 E) (Fin n → E)} {N D : ℕ} {A B : Matrix (Fin n) (Fin n) E}
    (hA : CongAt L N D A) (hB : CongAt L N D B) : CongAt L N D (A * B) := by
  obtain ⟨t₁, c₁, h₁⟩ := hA
  obtain ⟨t₂, c₂, h₂⟩ := hB
  refine ⟨t₁ * t₂, Nat.Coprime.mul_left c₁ c₂, fun v hv => ?_⟩
  obtain ⟨w₂, hw₂, e₂⟩ := h₂ v hv
  have hy : t₂ • (B *ᵥ v) ∈ L := by
    have : t₂ • (B *ᵥ v) = t₂ • v + D • w₂ := by rw [← e₂, smul_sub]; abel
    rw [this]
    exact L.add_mem (nsmul_mem hv _) (nsmul_mem hw₂ _)
  obtain ⟨w₁, hw₁, e₁⟩ := h₁ _ hy
  refine ⟨w₁ + t₁ • w₂, L.add_mem hw₁ (nsmul_mem hw₂ _), ?_⟩
  rw [smul_add, smul_comm D t₁, ← e₁, ← e₂, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  module

theorem congAt_conj [CharZero E] {L : Submodule (𝓞 E) (Fin n → E)} {N D d e : ℕ} (he : 0 < e)
    {A R R' : Matrix (Fin n) (Fin n) E} (hRR : R * R' = 1)
    (hR : ∀ v ∈ L, d • (R *ᵥ v) ∈ L) (hR' : ∀ v ∈ L, e • (R' *ᵥ v) ∈ L)
    (hA : CongAt L N (D * d * e) A) : CongAt L N D (R * A * R') := by
  obtain ⟨t, ct, h⟩ := hA
  refine ⟨t, ct, fun v hv => ?_⟩
  obtain ⟨w, hw, e₁⟩ := h _ (hR' v hv)
  refine ⟨_, hR w hw, ?_⟩
  have e₂ := congrArg (fun z => R *ᵥ z) e₁
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec] at e₂
  have he' : (e : E) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  apply smul_right_injective (Fin n → E) he'
  simp only [Nat.cast_smul_eq_nsmul]
  rw [Matrix.mul_assoc]
  linear_combination (exp := 1) e₂

theorem splitOr_mul {F : Type} [Field F] [Algebra F E] {c : E ≃ₐ[F] E} {N : ℕ} {s t : 𝓞 E}
    (hs : SplitOr c N s) (ht : SplitOr c N t) : SplitOr c N (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, fun P hP h => (hP.mem_or_mem h).elim (hs.2 P hP) (ht.2 P hP)⟩

theorem smul_mul_mem {L : Submodule (𝓞 E) (Fin n → E)} {s t : 𝓞 E} {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ v ∈ L, s • (A *ᵥ v) ∈ L) (hB : ∀ v ∈ L, t • (B *ᵥ v) ∈ L) (v : Fin n → E) (hv : v ∈ L) :
    (s * t) • ((A * B) *ᵥ v) ∈ L := by
  have := hA _ (hB v hv)
  rwa [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_smul] at this

theorem exists_unitary_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL γ₀ N D hγ₀ hN hD
  obtain ⟨l, hl, hprod⟩ := GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections F E c n G hG _ hγ₀
  clear hγ₀
  induction l generalizing γ₀ D with
  | nil =>
    have h1 : γ₀ = 1 := Units.ext (by simpa using hprod)
    subst h1
    refine ⟨1, fun x y => by simp, ⟨1, by simp, fun v _ => ⟨0, L.zero_mem, by simp⟩⟩, 1,
      ⟨one_ne_zero, fun P hP h => absurd ((Ideal.eq_top_iff_one P).2 h) hP.ne_top⟩, fun v hv => ?_⟩
    simpa using hv
  | cons p l ih =>
    obtain ⟨x, u⟩ := p
    obtain ⟨hx, hu⟩ := hl (x, u) List.mem_cons_self
    simp only at hx hu
    obtain ⟨-, r1, rmul, run⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG x hx
    have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
    let R : (a : E) → a ≠ 0 → GL (Fin n) E := fun a ha =>
      ⟨refl c G x a, refl c G x a⁻¹, by rw [rmul, mul_inv_cancel₀ ha, r1],
        by rw [rmul, inv_mul_cancel₀ ha, r1]⟩
    obtain ⟨d, hd, hRd⟩ := exists_nat_mulVec_mem L hfg hL (R u hu0).1
    obtain ⟨e, he, hRe⟩ := exists_nat_mulVec_mem L hfg hL ((R u hu0)⁻¹).1
    obtain ⟨γ₁, hγ₁, hc₁, s₁, hs₁, hL₁⟩ := ih ((R u hu0)⁻¹ * γ₀) (D * d * e)
      (Nat.mul_pos (Nat.mul_pos hD hd) he) (fun p hp => hl p (List.mem_cons_of_mem _ hp)) (by
        rw [Units.val_mul, hprod, List.map_cons, List.prod_cons, ← mul_assoc]
        change _ = _
        have : ((R u hu0)⁻¹).1 * refl c G x u = 1 := (R u hu0).inv_mul
        rw [this, one_mul])
    obtain ⟨u', hu', hc', s', hs', hL'⟩ := GlobalTheory.T.exists_norm_one_reflection_correction_at_level F E c n G hG L hfg hL x u N D hx hu hN hD
    have hu'0 : u' ≠ 0 := left_ne_zero_of_mul_eq_one hu'
    refine ⟨R u' hu'0 * γ₁, ?_, ?_, s' * s₁, splitOr_mul hs' hs₁, fun v hv => ⟨?_, ?_⟩⟩
    · intro y z
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact (run u' hu' _ _).trans (hγ₁ y z)
    · have hconj := congAt_conj he (R u hu0).mul_inv hRd hRe hc₁
      have h := congAt_mul hc' hconj
      have e1 : refl c G x (u' / u) = (R u' hu'0 * (R u hu0)⁻¹).1 := by
        rw [div_eq_mul_inv, ← rmul]; rfl
      rw [e1, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul] at h
      convert h using 2
      group
    · rw [Units.val_mul]
      exact smul_mul_mem (fun v hv => (hL' v hv).1) (fun v hv => (hL₁ v hv).1) v hv
    · rw [mul_inv_rev, Units.val_mul, mul_comm s']
      exact smul_mul_mem (fun v hv => (hL₁ v hv).2) (fun v hv => (hL' v hv).2) v hv

end GlobalTheory.UnRep.Correct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCorrectionCongruentOneAtLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_unitary_correction_congruent_one_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UnRep.Correct.exists_unitary_correction | exact GlobalTheory.UnRep.Correct.exists_unitary_correction | (intros; apply GlobalTheory.UnRep.Correct.exists_unitary_correction <;> assumption)
end
end
