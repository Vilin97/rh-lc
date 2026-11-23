module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataTowerUnionAdjoinStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefect
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
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImageStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribedStatement
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebra

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefectStatement

section

@[expose] public section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.exists_derivationOn_extension_cube_defect : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D → ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  first | exact @GlobalTheory.AlmostEt.exists_derOn_ext | exact GlobalTheory.AlmostEt.exists_derOn_ext | (intros; apply GlobalTheory.AlmostEt.exists_derOn_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatibleStatement

section

@[expose] public section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.exists_derivationOn_iSup_of_compatible : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B : ℕ → Subalgebra A S), Monotone B → ∀ D : ℕ → S → M, (∀ m, IsDerOn (B m) (D m)) → (∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) → ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  first | exact @GlobalTheory.AlmostEt.isDerOn_iSup_glue | exact GlobalTheory.AlmostEt.isDerOn_iSup_glue | (intros; apply GlobalTheory.AlmostEt.isDerOn_iSup_glue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionQDerivationModIntegralClosure

section

@[expose] public section

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.QDer

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem isDerOn_mono {B B' : Subalgebra A S} {D : S → M} (h : IsDerOn B D) (hle : B' ≤ B) :
    IsDerOn B' D :=
  ⟨fun x hx y hy => h.add x (hle hx) y (hle hy), fun x hx y hy => h.mul x (hle hx) y (hle hy),
    h.alg⟩

theorem isDerOn_sub {B : Subalgebra A S} {D₁ D₂ : S → M} (h₁ : IsDerOn B D₁) (h₂ : IsDerOn B D₂) :
    IsDerOn B (fun x => D₁ x - D₂ x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    simp only [h₁.add x hx y hy, h₂.add x hx y hy]
    abel
  · intro x hx y hy
    simp only [h₁.mul x hx y hy, h₂.mul x hx y hy, smul_sub]
    abel
  · intro a
    simp [h₁.alg a, h₂.alg a]

theorem isDerOn_pow {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    {n : ℕ} (hn : 1 ≤ n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, h.mul _ (pow_mem hx _) _ hx, ih (by omega), smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

end General

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by simp [zS, T.ζpow])

theorem qS_succ_pow (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by simp [qS, T.qpow])

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zS_succ_pow]; exact pow_mem (zS_mem_levelAlg T _) _
  · rw [← qS_succ_pow]; exact pow_mem (qS_mem_levelAlg T _) _

theorem towerAlg_le_iSup (T : Tower p Ω) : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (zS_mem_levelAlg T m))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (qS_mem_levelAlg T m))

theorem exists_level (hC : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) :
    ∃ D : integralClosure (O0 p) Ω → Frac p Ω, IsDerOn (levelAlg T n) D ∧ D (zS T n) = 0 ∧
      D (qS T n) = Submodule.Quotient.mk (T.qq n / (p : Ω) ^ n) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed p Ω hC T n hn (Frac p Ω) 0 _ (smul_zero _) ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p), ?_⟩
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rw [Algebra.linearMap_apply, ← IsScalarTower.algebraMap_apply, Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) ^ n * qS T n ^ (p ^ n - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) ^ n * T.qq n ^ (p ^ n - 1) := by
    simp [qS]
  rw [key, ← GlobalTheory.AlmostEt.qq_pow T n]
  field_simp
  rw [pow_sub_one_mul hpn]

theorem smul_mk_eq (hC : IsClo p Ω) (T : Tower p Ω) (m : ℕ) :
    ((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1)) •
        (Submodule.Quotient.mk (T.qq (m + 1) / (p : Ω) ^ (m + 1)) : Frac p Ω) =
      Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpn : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) * T.qq (m + 1) ^ (p - 1) := by
    simp [qS]
  rw [key, ← T.qpow m, ← pow_sub_one_mul hpn (T.qq (m + 1)), pow_succ]
  field_simp

theorem exists_qDer (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (hC : IsClo p Ω) (T : Tower p Ω) :
    ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧
      ∀ m : ℕ, D (zS T m) = 0 ∧ D (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  choose Dl hDl hz hq using fun m : ℕ => exists_level hC T (m + 1) (by omega)

  have hz' : ∀ m, Dl m (zS T m) = 0 := fun m => by
    rw [← zS_succ_pow, isDerOn_pow (hDl m) (zS_mem_levelAlg T _) hp1, hz, smul_zero]
  have hq' : ∀ m, Dl m (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := fun m => by
    rw [← qS_succ_pow, isDerOn_pow (hDl m) (qS_mem_levelAlg T _) hp1, hq, smul_mk_eq hC T m]

  have hcomp : ∀ m, ∀ x ∈ levelAlg T (m + 1), Dl (m + 1) x = Dl m x := by
    intro m x hx
    have hE := isDerOn_sub (isDerOn_mono (hDl (m + 1)) (levelAlg_le_succ T (m + 1))) (hDl m)
    have hspan := GlobalTheory.T.derivationOn_adjoin_mem_span_image (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω) {zS T (m + 1), qS T (m + 1)}
      _ hE x hx
    have h1 : Dl (m + 1) (zS T (m + 1)) - Dl m (zS T (m + 1)) = 0 := by rw [hz' (m + 1), hz m, sub_zero]
    have h2 : Dl (m + 1) (qS T (m + 1)) - Dl m (qS T (m + 1)) = 0 := by rw [hq' (m + 1), hq m, sub_self]
    simp only [Set.image_insert_eq, Set.image_singleton, h1, h2, Set.insert_eq_of_mem,
      Set.mem_singleton_iff, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hspan
    exact sub_eq_zero.1 hspan
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D, hD, hag⟩ := GlobalTheory.T.exists_derivationOn_iSup_of_compatible (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono Dl hDl hcomp
  refine ⟨D, isDerOn_mono hD (towerAlg_le_iSup T), fun m => ⟨?_, ?_⟩⟩
  · rw [hag m _ (levelAlg_le_succ T m (zS_mem_levelAlg T m)), hz']
  · rw [hag m _ (levelAlg_le_succ T m (qS_mem_levelAlg T m)), hq']

end GlobalTheory.AlmostEt.QDer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionQDerivationModIntegralClosureStatement

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_towerUnion_qDerivation_modIntegralClosure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = 0 ∧ D (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  first | exact @GlobalTheory.AlmostEt.QDer.exists_qDer | exact GlobalTheory.AlmostEt.QDer.exists_qDer | (intros; apply GlobalTheory.AlmostEt.QDer.exists_qDer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosureStatement

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_towerUnion_zetaDerivation_modIntegralClosure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧ D (qS T m) = 0 := by
  first | exact @GlobalTheory.AlmostEt.zeta_derivation | exact GlobalTheory.AlmostEt.zeta_derivation | (intros; apply GlobalTheory.AlmostEt.zeta_derivation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebraStatement

section

@[expose] public section

open GlobalTheory.AlmostEt

theorem _root_.GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ) (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 → ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) → ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D → ∑ i, x i • D (y i) = 0 := by
  first | exact @GlobalTheory.AlmostEt.kaehler_rel_local | exact GlobalTheory.AlmostEt.kaehler_rel_local | (intros; apply GlobalTheory.AlmostEt.kaehler_rel_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOfSmulMkEqZero

section

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_eq_of_smul_mk_eq_zero {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (s : integralClosure (O0 p) Ω) (ω : Ω)
    (h : s • (Submodule.Quotient.mk ω : Frac p Ω) = 0) :
    ∃ t : integralClosure (O0 p) Ω, (t : Ω) = (s : Ω) * ω := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by simpa [Algebra.smul_def] using ht⟩

theorem dlog_indep_pow_three : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n →
    ∀ x y zi qi : (integralClosure (O0 p) Ω), zS T n * zi = 1 → qS T n * qi = 1 →
    (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T n) +
      (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T n) = 0 →
    (∃ t, (p : (integralClosure (O0 p) Ω)) ^ 3 * x = (p : (integralClosure (O0 p) Ω)) ^ (n - 1) * t) ∧
    (∃ t, (p : (integralClosure (O0 p) Ω)) ^ 3 * y = (p : (integralClosure (O0 p) Ω)) ^ n * t) := by
  intro p _ Ω _ _ hp2 hclo T n hn x y zi qi hz hq hrel
  have hpΩ : (p : Ω) ≠ 0 := by
    haveI := GlobalTheory.K5.Basic.charZero_of_isClo hclo
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrel' : ∑ i, (![x * zi, y * qi] : Fin 2 → integralClosure (O0 p) Ω) i •
      KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω)
        ((![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i) = 0 := by
    simpa [Fin.sum_univ_two] using hrel
  obtain ⟨F, hF⟩ := GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra (O0 p) (integralClosure (O0 p) Ω) 2 _ _ hrel'
  obtain ⟨C, tr, m, a, b, hFC, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin p Ω hp2 hclo T F
  have hzT : zS T n ∈ towerAlg T := Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hqT : qS T n ∈ towerAlg T := Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  have hyC : ∀ i, (![zS T n, qS T n] : Fin 2 → integralClosure (O0 p) Ω) i ∈ C := by
    intro i; fin_cases i
    · exact htr.le hzT
    · exact htr.le hqT
  have hzΩ : T.ζ n * (zi : Ω) = 1 := by
    have := congrArg Subtype.val hz; simpa [zS] using this
  have hqΩ : T.qq n * (qi : Ω) = 1 := by
    have := congrArg Subtype.val hq; simpa [qS] using this
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  constructor
  · obtain ⟨Dz, hDz, hDzv⟩ := GlobalTheory.T.exists_towerUnion_zetaDerivation_modIntegralClosure p Ω hclo T
    obtain ⟨D', hD', hD'v⟩ := GlobalTheory.T.exists_derivationOn_extension_cube_defect (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
      (towerAlg T) C tr m a b _ htr Dz hDz
    have h := hF C hFC hyC (Frac p Ω) D' hD'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD'v _ hzT, hD'v _ hqT, (hDzv (k + 1)).1, (hDzv (k + 1)).2, smul_zero, smul_zero,
      add_zero, smul_smul] at h
    obtain ⟨t, ht⟩ := exists_eq_of_smul_mk_eq_zero _ _ h
    refine ⟨t, Subtype.ext ?_⟩
    push_cast at ht ⊢
    rw [ht]
    field_simp
    linear_combination (-((x : Ω) * (p : Ω) ^ (k + 1))) * hzΩ
  · obtain ⟨Dq, hDq, hDqv⟩ := GlobalTheory.T.exists_towerUnion_qDerivation_modIntegralClosure p Ω hclo T
    obtain ⟨D', hD', hD'v⟩ := GlobalTheory.T.exists_derivationOn_extension_cube_defect (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
      (towerAlg T) C tr m a b _ htr Dq hDq
    have h := hF C hFC hyC (Frac p Ω) D' hD'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD'v _ hzT, hD'v _ hqT, (hDqv (k + 1)).1, (hDqv (k + 1)).2, smul_zero, smul_zero,
      zero_add, smul_smul] at h
    obtain ⟨t, ht⟩ := exists_eq_of_smul_mk_eq_zero _ _ h
    refine ⟨t, Subtype.ext ?_⟩
    push_cast at ht ⊢
    rw [ht]
    field_simp
    linear_combination (-(y : Ω)) * hqΩ

end GlobalTheory.AlmostEt
end
end
