module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansionsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeltaPowQExpansionIffLaurentSeries

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem laurent_exp_shift (M : ℕ) (hM : 0 < M) (w : ℕ) (k : ℤ) (τ : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * ((k - (w * M : ℕ) : ℤ) : ℂ) * τ / M) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem laurent_qAll_int (E : Subring ℂ) (M : ℕ) (hM : 0 < M) (f : ℍ → ℂ) (c : ℕ → ℤ)
    (h : HasQ 1 f fun n => (c n : ℂ)) : QAll (· ∈ E) M f :=
  QAll.of_dvd hM (one_dvd M) E.zero_mem ⟨_, h, fun n => intCast_mem E (c n)⟩

theorem laurent_iff : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  intro E M φ hM
  obtain ⟨⟨cD, -, hD⟩, ⟨cI, -, hI⟩⟩ := GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions
  obtain ⟨-, -, -, hmul, hpow, -⟩ := GlobalTheory.QFam.QAllSubring.ring_closed E M hM
  have hqD := laurent_qAll_int E M hM _ cD hD
  have hqI := laurent_qAll_int E M hM _ cI hI
  have hDD0 : ∀ τ : ℍ, DD τ ≠ 0 := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb, hbE⟩ := hmul _ _ (hpow _ w hqI) hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    let c : ℤ → ℂ := fun n => if -((w * M : ℕ) : ℤ) ≤ n then b (n + ((w * M : ℕ) : ℤ)).toNat else 0
    refine ⟨c, -((w * M : ℕ) : ℤ), fun n => ?_, fun n hn => ?_, fun τ => ?_⟩
    · simp only [c]
      split_ifs
      · exact hbE _
      · exact E.zero_mem
    · simp only [c]
      rw [if_neg (not_le.mpr hn)]
    · rw [← hginj.hasSum_iff]
      · have h1 := (hb τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹
        have hφ : (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            ((Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) ^ w * (DD τ ^ w * φ τ)) = φ τ := by
          rw [div_pow]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))),
            pow_ne_zero w (hDD0 τ)]
        rw [hφ] at h1
        have key : (fun k : ℕ => (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            (b k * Complex.exp (2 * Real.pi * Complex.I * k * τ / M))) =
            (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) ∘ g := by
          funext k
          simp only [Function.comp, g, c]
          rw [if_pos (by omega)]
          have hk : ((k : ℤ) - ((w * M : ℕ) : ℤ) + ((w * M : ℕ) : ℤ)).toNat = k := by omega
          rw [hk]
          have := laurent_exp_shift M hM w k τ
          rw [← Int.cast_natCast k, ← this]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
        rw [key] at h1
        exact h1
      · intro n hn
        have : ¬ (-((w * M : ℕ) : ℤ) ≤ n) := fun h => hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by
          simp only [g]; omega⟩
        simp only [c]
        rw [if_neg this, zero_mul]
  · rintro ⟨c, n₀, hcE, hc0, hs⟩
    refine ⟨(-n₀).toNat, ?_⟩
    set w := (-n₀).toNat with hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    have hwM : (w : ℤ) ≤ ((w * M : ℕ) : ℤ) := by
      have : w ≤ w * M := Nat.le_mul_of_pos_right w hM
      exact_mod_cast this
    have hq : HasQ M (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ) fun k => c (g k) := by
      intro τ
      have h1 := (hs τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)
      rw [← hginj.hasSum_iff] at h1
      · have key : (fun i : ℤ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) * τ / M))) ∘ g =
            fun k : ℕ => c (g k) * Complex.exp (2 * Real.pi * Complex.I * k * τ / M) := by
          funext k
          simp only [Function.comp, g]
          rw [mul_left_comm, laurent_exp_shift M hM w k τ]
          push_cast
          rfl
        rw [key] at h1
        exact h1
      · intro n hn
        have : n < n₀ := by
          by_contra hh
          exact hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by simp only [g]; omega⟩
        simp [hc0 n this]
    have hqE : QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ :=
      ⟨_, hq, fun k => hcE _⟩
    have h2 := hmul _ _ (hpow _ w hqD) hqE
    have key : (fun τ : ℍ => (DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) ^ w *
        (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ)) = fun τ => DD τ ^ w * φ τ := by
      funext τ
      rw [div_pow]
      field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
    rw [key] at h2
    exact h2

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeltaPowQExpansionIffLaurentSeriesStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  first | exact @GlobalTheory.FN.laurent_iff | exact GlobalTheory.FN.laurent_iff | (intros; apply GlobalTheory.FN.laurent_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformPoleOrder

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem uniform_pole_order : ∀ (E : Subring ℂ) (M : ℕ) (f : ℍ → ℂ), 0 < M →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ) →
    (∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * f (γ • τ)) → ∃ w : ℕ, Lv E M w f := by
  intro E M f hM hinv hw
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  choose w hw using hw
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let lift : SL(2, ZMod M) → SL(2, ℤ) := fun g => if h : ∃ γ, red γ = g then h.choose else 1
  let W : ℕ := Finset.univ.sup fun g => w (lift g)
  refine ⟨W, hinv, fun γ => ?_⟩
  have hex : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
  have hl : lift (red γ) = hex.choose := dif_pos hex
  set γ' := lift (red γ) with hγ'
  have hred : red γ' = red γ := by rw [hl]; exact hex.choose_spec
  have hmem : γ * γ'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem']
    show red (γ * γ'⁻¹) = 1
    rw [map_mul, map_inv, hred, mul_inv_cancel]
  have hf : ∀ τ : ℍ, f (γ • τ) = f (γ' • τ) := fun τ => by
    have := hinv _ hmem (γ' • τ)
    rw [← this, ← mul_smul, inv_mul_cancel_right]
  have hle : w γ' ≤ W := Finset.le_sup (f := fun g => w (lift g)) (Finset.mem_univ (red γ))
  have hD : QAll (· ∈ E) M fun τ => DD τ ^ (W - w γ') :=
    QAllSubring.pow _ (eis_qAll M hM DD (Or.inr (Or.inr rfl)) E)
  have := QAllSubring.mul hD (hw γ')
  convert this using 2 with τ
  rw [hf τ, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformPoleOrderStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_Lv_of_invariant_Gamma_of_forall_QAll : ∀ (E : Subring ℂ) (M : ℕ) (f : ℍ → ℂ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ) → (∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * f (γ • τ)) → ∃ w : ℕ, Lv E M w f := by
  first | exact @GlobalTheory.FN.uniform_pole_order | exact GlobalTheory.FN.uniform_pole_order | (intros; apply GlobalTheory.FN.uniform_pole_order <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansions

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_of_qexp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  intro Ω _ _ _ ε T a M hM _ hinv hexp
  have hHs : ∀ τ : ℍ, (τ : ℂ) ∈ Hs := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.2
  have hmob : ∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.2.2.2.1
  set f : ℍ → ℂ := fun τ => a τ with hf
  have hinvf : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ := by
    intro γ hγ τ
    simp only [hf]
    rw [← hmob γ τ]
    exact hinv γ hγ τ (hHs τ)
  have hw : ∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ ε.range) M fun τ => DD τ ^ w * f (γ • τ) := by
    intro γ
    obtain ⟨c, n0, hc0, hs⟩ := hexp γ
    refine (GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries ε.range M (fun τ => f (γ • τ)) hM).2 ⟨fun n => ε (c n), n0, fun n => ⟨c n, rfl⟩, ?_, ?_⟩
    · intro n hn
      simp [hc0 n hn]
    · intro τ
      have := hs τ (hHs τ)
      simp only [hf]
      rw [← hmob γ τ]
      exact this
  obtain ⟨w, hLv⟩ := GlobalTheory.T.exists_Lv_of_invariant_Gamma_of_forall_QAll ε.range M f hM hinvf hw
  have hmem : f ∈ ring ε.range := mem_ring_of_inR ⟨M, w, hM, hLv⟩
  refine ⟨T.io ⟨f, hmem⟩, ?_⟩
  rw [T.an_io]
  exact GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.1 a

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansionsStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.mem_modularFunctionFractionField_of_qExpansions : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  first | exact @GlobalTheory.FN.exists_of_qexp | exact GlobalTheory.FN.exists_of_qexp | (intros; apply GlobalTheory.FN.exists_of_qexp <;> assumption)
end
end
