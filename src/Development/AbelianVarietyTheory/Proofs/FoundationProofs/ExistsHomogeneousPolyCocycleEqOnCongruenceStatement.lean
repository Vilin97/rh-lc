module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsScalarGamma1CapGamma0ModLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLawsStatement
public import Mathlib.GroupTheory.Schreier
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleExtensionOfNegCentralElement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem exists_cocycle_extension_of_neg_action : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  intro G _ R _ V _ _ ρ hmul hone h2 S hS Δ hΔ hΔtriv c hc hk φ hφS hφadd hφinv
  obtain ⟨u, hu⟩ := h2
  have hinv : ∀ g v, ρ g (ρ g⁻¹ v) = v := by
    intro g v; rw [← hmul, inv_mul_cancel, hone]
  have hconj : ∀ g, ∀ δ ∈ Δ, φ (g * δ * g⁻¹) = ρ g⁻¹ (φ δ) := by
    intro g δ hδ
    rw [← hφinv g δ hδ, ← hmul, mul_inv_cancel, hone]
  have hkmul : ∀ g h : G, c * (g * h) * c⁻¹ * (g * h)⁻¹
      = (c * g * c⁻¹ * g⁻¹) * (g * (c * h * c⁻¹ * h⁻¹) * g⁻¹) := by
    intro g h; group
  have hw : ∀ g h : G, ρ (g * h) (φ (c * (g * h) * c⁻¹ * (g * h)⁻¹))
      = ρ h (ρ g (φ (c * g * c⁻¹ * g⁻¹))) + ρ h (φ (c * h * c⁻¹ * h⁻¹)) := by
    intro g h
    rw [hkmul, hφadd _ (hk g) _ (hΔ.conj_mem _ (hk h) g), hconj g _ (hk h), hmul,
      map_add, map_add, hinv]
  have h1 : φ 1 = 0 := by
    have := hφadd 1 Δ.one_mem 1 Δ.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hneg : ∀ δ ∈ Δ, φ δ⁻¹ = -φ δ := by
    intro δ hδ
    have := hφadd δ hδ δ⁻¹ (Δ.inv_mem hδ)
    rw [mul_inv_cancel, h1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  refine ⟨fun g => -(↑u⁻¹ : R) • ρ g (φ (c * g * c⁻¹ * g⁻¹)), ?_, ?_, ?_⟩
  · intro g
    exact S.smul_mem _ (hS g _ (hφS _ (hk g)))
  · intro g h
    simp only
    rw [hw, smul_add, map_smul]
  · intro δ hδ
    simp only
    have hcδ : c * δ * c⁻¹ ∈ Δ := hΔ.conj_mem _ hδ c
    have hc' : φ (c * δ * c⁻¹) = -φ δ := by
      have e1 := hφinv c δ hδ
      rw [hc _ (hφS _ hcδ)] at e1
      rw [← e1, neg_neg]
    rw [hΔtriv δ hδ, hφadd _ hcδ _ (Δ.inv_mem hδ), hc', hneg δ hδ,
      show -φ δ + -φ δ = -((2 : R) • φ δ) by rw [two_smul, neg_add],
      smul_neg, neg_smul, neg_neg, smul_smul, ← hu, Units.inv_mul, one_smul]

end GlobalTheory.KZ.H3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleExtensionOfNegCentralElementStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_cocycle_extension_of_neg_central_element : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  first | exact @GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action | exact GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action | (intros; apply GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformCongruenceLevelGamma1CapGamma0

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem gamma_le_of_dvd {M M' : ℕ} (h : M ∣ M') :
    CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro δ hδ
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  have key : ∀ x : ℤ, ((x : ZMod M) = ZMod.castHom h (ZMod M) (x : ZMod M')) := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

theorem unif_level : ∀ (N l : ℕ) (R : Type) [CommRing R] (Φ : SL(2, ℤ) → MvPolynomial (Fin 2) R), 0 < N → 0 < l →
    (∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, Φ (δ * δ') = Φ δ + Φ δ') →
    (∀ γ ∈ Gam N l, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹))) Φ) →
    ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ Gam N l, ∀ δ ∈ CongruenceSubgroup.Gamma M,
      slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ := by
  intro N l R _ Φ hN hl _ hinv
  obtain ⟨hmul, hone, -, -, -, -, -⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws R

  let H : ℕ → Subgroup SL(2, ℤ) := fun M =>
    { carrier := {γ | ∀ δ ∈ CongruenceSubgroup.Gamma M,
        slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ}
      mul_mem' := by
        intro a b ha hb δ hδ
        have hn : b * δ * b⁻¹ ∈ CongruenceSubgroup.Gamma M :=
          (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ b
        have e : a * b * δ * (a * b)⁻¹ = a * (b * δ * b⁻¹) * a⁻¹ := by group
        show slP ((a * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ (a * b * δ * (a * b)⁻¹)) = Φ δ
        rw [e, Matrix.SpecialLinearGroup.coe_mul, hmul, ha _ hn, hb _ hδ]
      one_mem' := by
        intro δ _
        simp only [one_mul, inv_one, mul_one, Matrix.SpecialLinearGroup.coe_one, hone]
      inv_mem' := by
        intro a ha δ hδ
        have hn : a⁻¹ * δ * a⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma M :=
          (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ a⁻¹
        have h1 := ha _ hn
        have e : a * (a⁻¹ * δ * a⁻¹⁻¹) * a⁻¹ = δ := by group
        rw [e] at h1
        show slP ((a⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ (a⁻¹ * δ * a⁻¹⁻¹)) = Φ δ
        rw [← h1, ← hmul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, hone] }
  have Hmono : ∀ {M M' : ℕ}, M ∣ M' → H M ≤ H M' := by
    intro M M' hd γ hγ δ hδ
    exact hγ δ (gamma_le_of_dvd hd hδ)
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (Gam N l).FiniteIndex := by unfold Gam; infer_instance
  haveI : Group.FG (Gam N l) := Subgroup.fg_of_index_ne_zero _
  obtain ⟨_, S, _, hS⟩ := (Group.fg_iff').1 (inferInstance : Group.FG (Gam N l))
  choose Mf hMf hMeq using fun s : Gam N l => hinv s.1 s.2
  let M := ∏ s ∈ S, Mf s
  have hMpos : 0 < M := Finset.prod_pos fun s _ => hMf s
  refine ⟨M, hMpos, ?_⟩
  have hle : Subgroup.closure (S : Set (Gam N l)) ≤ (H M).comap (Gam N l).subtype := by
    rw [Subgroup.closure_le]
    intro s hs
    have hd : Mf s ∣ M := Finset.dvd_prod_of_mem _ hs
    apply Hmono hd
    intro δ hδ
    exact hMeq s δ hδ
  intro γ hγ δ hδ
  have : (⟨γ, hγ⟩ : Gam N l) ∈ Subgroup.closure (S : Set (Gam N l)) := by rw [hS]; trivial
  exact hle this δ hδ

end GlobalTheory.KZ.H3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformCongruenceLevelGamma1CapGamma0Statement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.uniform_congruence_level_gamma1CapGamma0 : ∀ (N l : ℕ) (R : Type) [CommRing R] (Φ : SL(2, ℤ) → MvPolynomial (Fin 2) R), 0 < N → 0 < l → (∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, Φ (δ * δ') = Φ δ + Φ δ') → (∀ γ ∈ Gam N l, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹))) Φ) → ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ Gam N l, ∀ δ ∈ CongruenceSubgroup.Gamma M, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ := by
  first | exact @GlobalTheory.KZ.H3.unif_level | exact GlobalTheory.KZ.H3.unif_level | (intros; apply GlobalTheory.KZ.H3.unif_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomogeneousPolyCocycleEqOnCongruence

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem intCast_zmod_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {x y : ℤ} (hx : (x : ZMod K) = y) :
    (x : ZMod K₁) = y := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hx ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hx

theorem mem_Gamma_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ CongruenceSubgroup.Gamma K₁ := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h1)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h2)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h3)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h4)

theorem mem_Gam_of_Gamma {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ Gam N l := by
  have h1 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hN hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hl hδ)
  show δ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
  exact Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N δ).mpr ⟨h1.1, h1.2.2.2, h1.2.2.1⟩,
    CongruenceSubgroup.Gamma0_mem.mpr h2.2.2.1⟩

theorem entries_eq_one_of_mem_Gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma K)
    (i j : Fin 2) :
    (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h1, h2, h3, h4]

theorem exists_coc_near : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ,
    IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)),
      IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  intro N l w hN hl hl2 hlN hw Φ hΦ n
  obtain ⟨hhom, hadd, hinv, -⟩ := hΦ
  obtain ⟨M₁, hM₁, hadd₁⟩ := hadd n
  obtain ⟨M₂, hM₂, hinv₂⟩ :=
    GlobalTheory.T.uniform_congruence_level_gamma1CapGamma0 N l (ZMod (l ^ n)) (Φ n) hN hl.pos ⟨M₁, hM₁, hadd₁⟩ (hinv n)
  obtain ⟨b, M', hlM', hMeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := M₁ * M₂) (Nat.mul_pos hM₁ hM₂).ne' l hl.one_lt.ne'
  have hM'pos : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · exact absurd (h ▸ dvd_zero l) hlM'
    · exact h
  obtain ⟨c, hcΓ, hcomm, hcneg⟩ := GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level N l (max b n) M' hN hl hl2 hlN hM'pos hlM'
  have hMK : M₁ * M₂ ∣ M' * N * l ^ (max b n) := by
    rw [hMeq]
    exact dvd_trans (mul_dvd_mul (pow_dvd_pow l (le_max_left b n)) (dvd_refl M')) ⟨N, by ring⟩
  have hM₁K : M₁ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_right _ _) hMK
  have hM₂K : M₂ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_left _ _) hMK
  have hnA : l ^ n ∣ l ^ (max b n) := pow_dvd_pow l (le_max_right b n)
  have hnK : l ^ n ∣ M' * N * l ^ (max b n) := dvd_trans hnA (dvd_mul_left _ _)
  obtain ⟨L1, L2, L3, -, -, L6, L7⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws (ZMod (l ^ n))
  have hΔ : ((CongruenceSubgroup.Gamma (M' * N * l ^ (max b n))).subgroupOf (Gam N l)).Normal := by
    haveI := CongruenceSubgroup.Gamma_normal (M' * N * l ^ (max b n))
    exact Subgroup.normal_subgroupOf
  have h2 : IsUnit (2 : ZMod (l ^ n)) := by
    have hc : Nat.Coprime 2 (l ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))
    simpa using (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc
  obtain ⟨z, hzS, hzc, hzΔ⟩ := GlobalTheory.T.exists_cocycle_extension_of_neg_central_element (Gam N l) (ZMod (l ^ n)) (MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap)
    (fun g h v => by simp [L1]) (fun v => by simp [L2]) h2
    (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod (l ^ n)) w)
    (fun g v hv => by
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv ⊢
      exact L3 _ _ _ hv)
    _ hΔ
    (fun δ hδ v => by
      have hδ' : (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma (l ^ n) :=
        mem_Gamma_of_dvd hnK (Subgroup.mem_subgroupOf.mp hδ)
      show slP _ v = v
      rw [L6 _ 1 v (entries_eq_one_of_mem_Gamma hδ'), L2])
    ⟨c, hcΓ⟩
    (fun v hv => by
      show slP _ v = -v
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv
      rw [L6 _ (-1) v ?_, L7 w v hv, hw.neg_one_pow, neg_one_smul]
      intro i j
      have h := hcneg i j
      fin_cases i <;> fin_cases j <;> simp at h ⊢
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h))
    (fun g => by
      rw [Subgroup.mem_subgroupOf]
      simpa using hcomm g)
    (fun g => Φ n g)
    (fun δ _ => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hhom n _))
    (fun δ hδ δ' hδ' => by
      have := hadd₁ _ (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ)) _
        (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ'))
      simpa using this)
    (fun g δ hδ => by
      have := hinv₂ g g.2 δ (mem_Gamma_of_dvd hM₂K (Subgroup.mem_subgroupOf.mp hδ))
      simpa using this)
  classical
  refine ⟨fun γ => if h : γ ∈ Gam N l then z ⟨γ, h⟩ else 0, ⟨?_, ?_⟩, ?_⟩
  · intro γ hγ
    simp only [dif_pos hγ]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp (hzS _)
  · intro γ hγ δ hδ
    simp only [dif_pos hγ, dif_pos hδ, dif_pos (mul_mem hγ hδ)]
    simpa using hzc ⟨γ, hγ⟩ ⟨δ, hδ⟩
  · refine ⟨M' * N * l ^ (max b n) * l,
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hM'pos hN) (pow_pos hl.pos _)) hl.pos, fun δ hδ => ?_⟩
    have hδG : δ ∈ Gam N l :=
      mem_Gam_of_Gamma (dvd_mul_of_dvd_left ⟨M' * l ^ (max b n), by ring⟩ _) (dvd_mul_left _ _) hδ
    have hδK : δ ∈ CongruenceSubgroup.Gamma (M' * N * l ^ (max b n)) :=
      mem_Gamma_of_dvd (dvd_mul_right _ _) hδ
    simp only [dif_pos hδG]
    exact hzΔ ⟨δ, hδG⟩ (Subgroup.mem_subgroupOf.mpr hδK)

end GlobalTheory.KZ.H3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomogeneousPolyCocycleEqOnCongruenceStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_homogeneousPolyCocycle_eqOn_congruence : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ, IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  first | exact @GlobalTheory.KZ.H3.exists_coc_near | exact GlobalTheory.KZ.H3.exists_coc_near | (intros; apply GlobalTheory.KZ.H3.exists_coc_near <;> assumption)
end
end
