module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivativesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionPosOfCuspidalCharacter

section

@[expose] public section

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.Generic

variable {g : ℕ} [Fact g.Prime]

theorem br_zero_self {d : ℕ} (M : Mt g d) : br 0 d M = M := by
  funext i j
  simp [br, entN, i.isLt, j.isLt]

theorem res_zero_self {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g d) : res 0 d χ 1 h = χ h := by
  unfold res
  have hI : ∀ x : Gn g d, InPar 0 (x : Mt g d) := fun x i j hj _ => absurd hj (Nat.not_lt_zero _)
  have hT : ∀ x : Gn g d, tl 0 (x : Mt g d) = ((1 : Gn g 0) : Mt g 0) := fun x => by
    funext i; exact i.elim0
  simp only [hI, hT, br_zero_self, true_and, zero_mul, pow_zero, inv_one, one_mul, Units.val_inj]
  rw [Finset.sum_ite_eq']
  simp

theorem wh_zero_fun (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : wh ψ (fun _ : Gn g n => (0 : ℂ)) = 0 := by
  simp [wh, tr]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, _, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

end GlobalTheory.GLq.Generic

theorem GlobalTheory.GLq.wh_cusp_pos : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  intro g _ ψ hψ d χ hc
  have hc' := hc
  obtain ⟨hd, hirr, _⟩ := hc'
  have hder := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (GlobalTheory.GLq.Generic.isClass_of_isIrr hirr)
  rw [Finset.sum_eq_single 0] at hder
  rotate_left
  · intro m hm hm0
    have hmd : m < d := Finset.mem_range.mp hm
    have hz : res m (d - m) χ 1 = fun _ => 0 := by
      funext y
      exact GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g d m χ hc (Nat.pos_of_ne_zero hm0) hmd 1 y
    have : der ψ m χ 1 = 0 := by
      show wh ψ (res m (d - m) χ 1) = 0
      rw [hz]
      exact GlobalTheory.GLq.Generic.wh_zero_fun ψ _
    rw [this, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr hd) h0
  have h0 : der ψ 0 χ 1 = wh ψ χ := by
    change wh ψ (n := d) (res 0 d χ 1) = wh ψ χ
    congr 1
    funext h
    exact GlobalTheory.GLq.Generic.res_zero_self χ h
  rw [h0] at hder
  obtain ⟨V, _, hV⟩ := hirr
  have hchar : IsChar χ := ⟨V, hV⟩
  obtain ⟨d', hd'pos, hd'⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).2.1 ⟨V, ‹_›, hV⟩
  obtain ⟨n, hn⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g d 0 0 ψ).1 hchar
  have hwh : wh ψ χ = n := hn
  refine ⟨n, Nat.pos_of_ne_zero ?_, hwh⟩
  rintro rfl
  rw [hwh, Nat.cast_zero, zero_mul, hd'] at hder
  exact absurd hder (by exact_mod_cast hd'pos.ne')
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionPosOfCuspidalCharacterStatement

section

@[expose] public section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.whittakerDimension_pos_of_cuspidal_character : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  first | exact @GlobalTheory.GLq.wh_cusp_pos | exact GlobalTheory.GLq.wh_cusp_pos | (intros; apply GlobalTheory.GLq.wh_cusp_pos <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenericConstituentHarishChandraCuspidal

section

@[expose] public section

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.GenericConstituent

variable {g : ℕ} [Fact g.Prime]

theorem wh_const_mul' (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_mul_const' (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => f x * c) = wh ψ f * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wh_list_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (L : List (Gn g n → ℂ)) :
    wh ψ L.sum = (L.map (wh ψ)).sum := by
  induction L with
  | nil => simp [wh, tr]
  | cons a L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold wh tr
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_list_sum_right {G : Type} [Group G] [Fintype G] (ρ : G → ℂ) (L : List (G → ℂ)) :
    ip ρ L.sum = (L.map (ip ρ)).sum := by
  induction L with
  | nil => simp [ip]
  | cons a L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ip_sum_count {G : Type} [Group G] [Fintype G] (ρ : G → ℂ) (hρ : IsIrr ρ) (L : List (G → ℂ))
    (hL : ∀ σ ∈ L, IsIrr σ) : (L.map (ip ρ)).sum = (L.count ρ : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih (fun σ hσ => hL σ (List.mem_cons_of_mem a hσ)), List.count_cons,
      (GlobalTheory.GLq.ZOrth.zorth G ρ a hρ (hL a List.mem_cons_self)).2.2]
    by_cases h : ρ = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem isClass_of_isChar {n : ℕ} {χ : Gn g n → ℂ} (h : IsChar χ) : IsClass χ :=
  (GlobalTheory.charDec (Gn g n) χ).2.2.1 h

theorem wh_hcL_prod (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∀ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) → wh ψ (hcL L (degL L)) = (L.map fun p => wh ψ p.2).prod := by
  intro L
  induction L with
  | nil =>
    intro _
    exact GlobalTheory.GLq.Leibniz.wh_gl_zero ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, IsCusp q.2 := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hβ : IsClass (hcL L (degL L)) :=
      isClass_of_isChar (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl
        (fun q hq => isChar_of_isIrr (hL' q hq).2.1)).1
    have hα : IsClass p.2 := isClass_of_isChar (isChar_of_isIrr hp.2.1)
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg]
    · simp_rw [wh_const_mul']
      rw [wh_mul_const', ih hL', List.map_cons, List.prod_cons]
    · intro y x z
      simp only
      rw [hα]
    · intro x y z
      simp only
      rw [hβ]

theorem exists_generic_constituent : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (L : List (Pc g)) (n : ℕ), degL L = n → (∀ p ∈ L, IsCusp p.2) →
      ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL L n) ≠ 0 := by
  intro g _ ψ hψ L n hn hL
  subst hn
  have hwh : wh ψ (hcL L (degL L)) ≠ 0 := by
    rw [wh_hcL_prod ψ hψ L hL]
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨p, hp, h1⟩ := List.mem_map.1 h0
    obtain ⟨m, hm, hm'⟩ := GlobalTheory.T.whittakerDimension_pos_of_cuspidal_character g ψ hψ p.1 p.2 (hL p hp)
    rw [hm'] at h1
    have : m = 0 := by exact_mod_cast h1
    omega
  have hch : IsChar (hcL L (degL L)) :=
    (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl (fun q hq => isChar_of_isIrr (hL q hq).2.1)).1
  obtain ⟨Lρ, hirr, hsum⟩ := (GlobalTheory.charDec _ (hcL L (degL L))).1 hch
  have hex : ∃ ρ ∈ Lρ, wh ψ ρ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply hwh
    rw [hsum, wh_list_sum]
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
      exact hno ρ hρ
  obtain ⟨ρ, hρ, hwρ⟩ := hex
  refine ⟨ρ, hirr ρ hρ, hwρ, ?_⟩
  rw [hsum, ip_list_sum_right, ip_sum_count ρ (hirr ρ hρ) Lρ hirr]
  exact Nat.cast_ne_zero.2 (List.count_pos_iff.2 hρ).ne'

end GlobalTheory.GLq.GenericConstituent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenericConstituentHarishChandraCuspidalStatement

section

@[expose] public section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.exists_generic_constituent_harishChandra_cuspidal : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n : ℕ), degL L = n → (∀ p ∈ L, IsCusp p.2) → ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL L n) ≠ 0 := by
  first | exact @GlobalTheory.GLq.GenericConstituent.exists_generic_constituent | exact GlobalTheory.GLq.GenericConstituent.exists_generic_constituent | (intros; apply GlobalTheory.GLq.GenericConstituent.exists_generic_constituent <;> assumption)
end
end
