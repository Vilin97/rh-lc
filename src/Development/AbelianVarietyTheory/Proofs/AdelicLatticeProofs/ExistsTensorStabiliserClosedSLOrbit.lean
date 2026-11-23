module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftTranslationReynoldsOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatPolyEvalEqTensorPowerSumRightActionStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalInvariantTensorStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebraStatement
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftInvariantPolySeparatingCoset

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.CosetSep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def vanC (S : Set (Matrix ι ι ℂ)) : Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {f | ∀ g ∈ S, evC f g = 0}
  add_mem' := by
    intro a b ha hb g hg
    have h1 := ha g hg
    have h2 := hb g hg
    simp only [evC] at h1 h2 ⊢
    rw [map_add (f := _), h1, h2, add_zero]
  zero_mem' := by
    intro g _
    simp [evC]
  smul_mem' := by
    intro c a ha g hg
    have h1 := ha g hg
    simp only [evC] at h1 ⊢
    rw [smul_eq_mul, map_mul, h1, mul_zero]


omit [DecidableEq ι] in
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC] at hp hq ⊢
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p ij hp =>
    simp only [evC] at hp ⊢
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    simp [ltr, Matrix.mul_apply]

omit [DecidableEq ι] in
lemma exists_rtr (h : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ f' : MvPolynomial (ι × ι) ℂ, ∀ z, evC f' z = evC f (z * h) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, fun z => by simp [evC]⟩
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', fun z => ?_⟩
    have h1 := hp z
    have h2 := hq z
    simp only [evC] at h1 h2 ⊢
    rw [map_add (f := _), map_add (f := _), h1, h2]
  | mul_X p ij hp =>
    obtain ⟨p', hp⟩ := hp
    refine ⟨p' * ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (h k ij.2), fun z => ?_⟩
    have h1 := hp z
    simp only [evC] at h1 ⊢
    rw [map_mul, map_mul, h1]
    congr 1
    simp [Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_map (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  simp only [evC, ev]
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

lemma mem_of_forall_vanC {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {z : Matrix ι ι ℂ}
    (hz : ∀ f ∈ vanC Γ, evC f z = 0) : z ∈ Γ := by
  apply hΓ.closed
  intro f hf
  rw [← evC_map]
  apply hz
  intro g hg
  rw [evC_map]
  exact hf g hg

lemma vanC_sup_eq_top {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {y : Matrix ι ι ℂ} (hy : y.det = 1)
    (hyΓ : y ∉ Γ) : vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  set z : Matrix ι ι ℂ := Matrix.of fun i j => x (i, j) with hz
  have key : ∀ f ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ), evC f z = 0 := by
    intro f hf
    have h1 := (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).1 (hle hf)
    simpa [evC, hz] using h1
  have hzΓ : z ∈ Γ := mem_of_forall_vanC hΓ fun f hf => key f (Ideal.mem_sup_left hf)
  have hyy : y * y.adjugate = 1 := by rw [Matrix.mul_adjugate, hy, one_smul]
  have hyy' : y.adjugate * y = 1 := by rw [Matrix.adjugate_mul, hy, one_smul]
  have hwΓ : z * y.adjugate ∈ Γ := by
    refine mem_of_forall_vanC hΓ fun f hf => ?_
    obtain ⟨f', hf'⟩ := exists_rtr y.adjugate f
    rw [← hf']
    refine key f' (Ideal.mem_sup_right ?_)
    rintro _ ⟨g, hg, rfl⟩
    rw [hf', mul_assoc, hyy, mul_one]
    exact hf g hg
  apply hyΓ
  have h1 : (z * y.adjugate).adjugate * (z * y.adjugate) = 1 := by
    rw [Matrix.adjugate_mul, hΓ.det_eq _ hwΓ, one_smul]
  have h2 : y = (z * y.adjugate).adjugate * z := by
    calc y = (z * y.adjugate).adjugate * (z * y.adjugate) * y := by rw [h1, one_mul]
      _ = (z * y.adjugate).adjugate * (z * (y.adjugate * y)) := by simp only [mul_assoc]
      _ = _ := by rw [hyy', mul_one]
  rw [h2]
  exact hΓ.mul_mem _ (hΓ.adj_mem _ hwΓ) _ hzΓ

end GlobalTheory.ClassFin.CosetSep

namespace GlobalTheory.ClassFin


open CosetSep in
theorem exists_isInv_evC_one_ne : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsQGroup Γ → IsReynolds Γ Rey → ∀ y : Matrix ι ι ℂ, y.det = 1 → y ∉ Γ → ∃ f, IsInv Γ f ∧ evC f 1 ≠ evC f y := by
  intro ι _ _ Γ Rey hΓ hR y hy hyΓ
  have htop := vanC_sup_eq_top hΓ hy hyΓ
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) := by
    rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  have hRa : Rey a ∈ vanC Γ := by
    refine hR.stable ((vanC Γ).restrictScalars ℂ) ?_ a ha
    intro g hg f hf h hh
    rw [evC_ltr]
    exact hf _ (hΓ.mul_mem _ hg _ hh)
  have hRb : Rey b ∈ vanC ((fun g => g * y) '' Γ) := by
    refine hR.stable ((vanC ((fun g => g * y) '' Γ)).restrictScalars ℂ) ?_ b hb
    rintro g hg f hf _ ⟨h, hh, rfl⟩
    rw [evC_ltr, ← mul_assoc]
    exact hf _ ⟨g * h, hΓ.mul_mem _ hg _ hh, rfl⟩
  have hR1 : Rey 1 = 1 := hR.fix 1 (fun g _ z => by simp [evC])
  have hsum : Rey a + Rey b = 1 := by rw [← map_add (f := _), hab, hR1]
  refine ⟨Rey a, hR.inv a, ?_⟩
  have e1 : evC (Rey a) 1 = 0 := hRa 1 hΓ.one_mem
  have e2 : evC (Rey b) y = 0 := hRb y ⟨1, hΓ.one_mem, one_mul y⟩
  have e3 : evC (Rey a) y = 1 := by
    have h := congrArg (fun f => evC f y) hsum
    simp only [evC] at h e2 ⊢
    rw [map_add (f := _), e2, add_zero, map_one] at h
    exact h
  rw [e1, e3]
  exact zero_ne_one

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftInvariantPolySeparatingCosetStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_leftInvariantPoly_separating_coset : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsQGroup Γ → IsReynolds Γ Rey → ∀ y : Matrix ι ι ℂ, y.det = 1 → y ∉ Γ → ∃ f, IsInv Γ f ∧ evC f 1 ≠ evC f y := by
  first | exact @GlobalTheory.ClassFin.exists_isInv_evC_one_ne | exact GlobalTheory.ClassFin.exists_isInv_evC_one_ne | (intros; apply GlobalTheory.ClassFin.exists_isInv_evC_one_ne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedImageSLUnderGeneratingInvariants

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open MvPolynomial

variable {ι : Type}

theorem evC_aeval_invariants {κ : Type} (Φ : κ → MvPolynomial (ι × ι) ℂ) (P : MvPolynomial κ ℂ)
    (y : Matrix ι ι ℂ) : evC (aeval Φ P) y = eval (fun k => evC (Φ k) y) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [evC, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p n hp => simp only [evC, map_mul, aeval_X, eval_X] at *; rw [hp]

theorem evC_det_generic [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) :
    evC (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det y = y.det := by
  unfold evC
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem exists_evC_eq_of_relations [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ]
    (Φ : κ → MvPolynomial (ι × ι) ℂ) (hR : IsReynolds Γ Rey) (hΦ : ∀ k, IsInv Γ (Φ k))
    (hgen : ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) (z : κ → ℂ)
    (hz : ∀ P : MvPolynomial κ ℂ, aeval Φ P = 0 → eval z P = 0) :
    ∃ y : Matrix ι ι ℂ, z = fun k => evC (Φ k) y := by
  set I : Ideal (MvPolynomial (ι × ι) ℂ) := Ideal.span (Set.range fun k => Φ k - C (z k)) with hI
  have hne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ I := h ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have hinv : ∀ k, IsInv Γ (Φ k - C (z k)) := by
      intro k g hg y
      have := hΦ k g hg y
      simp only [evC, map_sub, eval_C] at *
      rw [this]
    have hone : Rey 1 = 1 := hR.fix 1 (fun g hg y => by simp [evC])
    have h2 : ∑ k, (Φ k - C (z k)) * Rey (a k) = 1 := by

      rw [← hone, ← ha, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm (a k), hR.mul _ _ (hinv k)]
    have h3 : ∀ k, ∃ P : MvPolynomial κ ℂ, aeval Φ P = Rey (a k) := by
      intro k
      have := hgen _ (hR.inv (a k))
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    choose P hP using h3
    have h4 := hz (∑ k, (X k - C (z k)) * P k - 1) (by

      simp only [map_sub, map_sum, map_mul, aeval_X, aeval_C, map_one, hP, algebraMap_eq]
      rw [h2, sub_self])
    simp at h4
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨Matrix.of fun i j => x (i, j), funext fun k => ?_⟩
  have hk : Φ k - C (z k) ∈ M := hIM (Ideal.subset_span ⟨k, rfl⟩)
  rw [hx, mem_vanishingIdeal_singleton_iff] at hk
  simp only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, coe_aeval_eq_eval] at hk
  have : evC (Φ k) (Matrix.of fun i j => x (i, j)) = aeval x (Φ k) := rfl
  rw [this]
  exact (sub_eq_zero.1 hk).symm

theorem isClosed_image_invariants :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  intro ι _ _ Γ Rey κ _ Φ hR hdet hΦ hgen
  have hD : IsInv Γ (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det := by
    intro g hg y
    rw [evC_det_generic, evC_det_generic, det_mul, hdet g hg, one_mul]
  have hD' := hgen _ hD
  rw [Algebra.adjoin_range_eq_range_aeval] at hD'
  obtain ⟨Q, hQ⟩ := hD'
  have hQ' : ∀ y : Matrix ι ι ℂ, eval (fun k => evC (Φ k) y) Q = y.det := by
    intro y
    rw [← evC_aeval_invariants, ← evC_det_generic y, ← hQ]
    rfl
  have hset : {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} =
      {z | eval z Q = 1} ∩ ⋂ P : MvPolynomial κ ℂ, ⋂ _ : aeval Φ P = 0, {z | eval z P = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by rw [hQ', hy], fun P hP => ?_⟩
      rw [← evC_aeval_invariants, hP]
      simp [evC]
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := exists_evC_eq_of_relations Γ Rey κ Φ hR hΦ hgen z h2
      exact ⟨y, by rw [← hQ', h1], rfl⟩
  rw [hset]
  exact (isClosed_eq (MvPolynomial.continuous_eval Q) continuous_const).inter
    (isClosed_iInter fun P => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval P) continuous_const)

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedImageSLUnderGeneratingInvariantsStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isClosed_image_SL_under_generating_invariants : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  first | exact @GlobalTheory.ClassFin.isClosed_image_invariants | exact GlobalTheory.ClassFin.isClosed_image_invariants | (intros; apply GlobalTheory.ClassFin.isClosed_image_invariants <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorStabiliserClosedSLOrbit

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_tensor_stabiliser_closed_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ (∀ y : Matrix ι ι ℂ, y.det = 1 → act d (fun k => ((t k : ℚ) : ℂ)) y = (fun k => ((t k : ℚ) : ℂ)) → y ∈ Γ) ∧ IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, hRey⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ.toIsPre hss
  obtain ⟨m, d, t, hfix, hgen⟩ := GlobalTheory.T.exists_rational_invariant_tensor' ι Γ hΓ.toIsPre hss
  obtain ⟨h1, hmul, -⟩ := (GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).2 m d (fun k => ((t k : ℚ) : ℂ))
  refine ⟨m, d, t, hfix, ?_, ?_⟩
  · intro y hy hyt
    by_contra hn
    obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_leftInvariantPoly_separating_coset ι Γ Rey hΓ hRey y hy hn
    obtain ⟨P, hP⟩ := hgen f hf
    apply hne
    rw [hP, hP, h1, hyt]
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction ι m d t
    have hev : ∀ (y : Matrix ι ι ℂ) (k : TIdx ι d),
        evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y = act d (fun k => ((t k : ℚ) : ℂ)) y k := by
      intro y k
      have h := hΦ ℂ y k
      simp only [eq_ratCast] at h
      rw [← h, evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]
    have hcl := GlobalTheory.T.isClosed_image_SL_under_generating_invariants ι Γ Rey (TIdx ι d) (fun k => MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) hRey
      hΓ.det_eq (fun k g hg y => by rw [hev, hev, hmul, hfix g hg]) (fun f hf => by
        obtain ⟨P, hP⟩ := hgen f hf
        rw [Algebra.adjoin_range_eq_range_aeval]
        refine ⟨P, ?_⟩
        apply MvPolynomial.funext
        intro x
        have h := hP (Matrix.of fun i j => x (i, j))
        have hx : (fun ij : ι × ι => (Matrix.of fun i j => x (i, j)) ij.1 ij.2) = x := rfl
        have h2 : act d (fun k => ((t k : ℚ) : ℂ)) (Matrix.of fun i j => x (i, j)) =
            fun k => MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) := by
          funext k
          rw [← hev, evC, hx]
        rw [evC, hx, h2] at h
        rw [h]
        show MvPolynomial.eval x (MvPolynomial.aeval _ P) = _
        clear hP h
        induction P using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add (f := _), hp, hq]
        | mul_X p n hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X])
    have : orb d (fun k => ((t k : ℚ) : ℂ)) = {z : TIdx ι d → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧
        z = fun k => evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y} := by
      ext z
      simp only [orb, hev]
    rw [this]
    exact hcl

end GlobalTheory.ClassFin
end
end
