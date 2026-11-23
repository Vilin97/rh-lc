module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CiEvalMSmul
public import Formalism.PeriodIntegrals.HwIrred
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalRingCardinality.DataCoeff
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
import Mathlib.Tactic.ReduceModChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CzDiagUnitary
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CfEqSumOfSubset

section

@[expose] public section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial

theorem cf_eq_sum_of_subset {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul, zero_mul]

theorem cf_add_left {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  classical
  rw [cf_eq_sum_of_subset (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    cf_eq_sum_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    cf_eq_sum_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem cf_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  rw [MvPolynomial.smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_left]

theorem cf_F {N : ℕ} (lam : DomWeight N) :
    (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).im = 0 ∧
      0 < (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re := by
  have hne : extremal ℂ N lam ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW
  obtain ⟨h1, h2⟩ := Formalism.GradedWeylDivisibility.fockPos _ _ hne
  exact ⟨h2, h1⟩

theorem cf_F_ne {N : ℕ} (lam : DomWeight N) :
    Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam) ≠ 0 := by
  intro h0
  have h1 := (cf_F lam).2
  rw [h0, Complex.zero_re] at h1
  exact lt_irrefl _ h1

def Blin {N : ℕ} (lam : DomWeight N) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun p := normFock lam p q
  map_add' p p' := by
    simp only [normFock]
    rw [cf_add_left, add_div]
  map_smul' c p := by
    simp only [normFock, RingHom.id_apply, smul_eq_mul]
    rw [cf_smul_left, mul_div_assoc]

theorem cf_Blin_apply {N : ℕ} (lam : DomWeight N) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Blin lam q p = normFock lam p q := rfl

theorem cf_herm {N : ℕ} (lam : DomWeight N) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam q p = star (normFock lam p q) := by
  unfold normFock
  rw [Formalism.GradedWeylDivisibility.fockHerm, star_div₀]
  congr 1
  have h := (cf_F lam).1
  apply Complex.ext
  · simp
  · simp [h]

theorem normFock_self_ne_zero {N : ℕ} (lam : DomWeight N) (p : MvPolynomial (Fin N × Fin N) ℂ) (hp : p ≠ 0) :
    normFock lam p p ≠ 0 := by
  unfold normFock
  refine div_ne_zero ?_ (cf_F_ne lam)
  intro h0
  have h1 := (Formalism.GradedWeylDivisibility.fockPos _ p hp).1
  rw [h0, Complex.zero_re] at h1
  exact lt_irrefl _ h1

theorem cf_adj {N : ℕ} (lam : DomWeight N) (g : Matrix (Fin N) (Fin N) ℂ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (Formalism.GradedWeylDivisibility.rowAct ℂ g p) q = normFock lam p (Formalism.GradedWeylDivisibility.rowAct ℂ g.conjTranspose q) := by
  unfold normFock
  rw [Formalism.GradedWeylDivisibility.fockRowAdj]

theorem cf_ee {N : ℕ} (lam : DomWeight N) : normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1 := by
  unfold normFock
  exact div_self (cf_F_ne lam)

end PI.WSF
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.CrRowActRowAct

section

@[expose] public section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial

theorem cr_rowAct_X {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (w : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (X w : MvPolynomial (Fin N × Fin N) ℂ) = ∑ b : Fin N, C (g w.1 b) * X (b, w.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

theorem cr_rowAct_C {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (C a : MvPolynomial (Fin N × Fin N) ℂ) = C a :=
  (Formalism.GradedWeylDivisibility.rowAct ℂ g).commutes a

theorem cr_evalM_rowAct {N : ℕ} (g x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM (g * x) s := by
  induction s using MvPolynomial.induction_on
  next a =>
    rw [cr_rowAct_C]
    simp [evalM]
  next p q hp hq =>
    simp only [map_add (f := _), evalM] at hp hq ⊢
    rw [hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp, cr_rowAct_X]
    congr 1
    simp [Matrix.mul_apply]

theorem cr_rowAct_one {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) s = s := by
  have h : (Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) :
      MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro w
    rw [cr_rowAct_X]
    simp [Matrix.one_apply]
  rw [h]
  rfl

theorem cr_rowAct_rowAct {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (Formalism.GradedWeylDivisibility.rowAct ℂ h s) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) s := by
  have hc : (Formalism.GradedWeylDivisibility.rowAct ℂ g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ h) =
      (Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro w

    rw [AlgHom.comp_apply, cr_rowAct_X, map_sum, cr_rowAct_X]

    simp only [map_mul, cr_rowAct_C, cr_rowAct_X, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]
    exact Finset.sum_comm
  rw [← hc, AlgHom.comp_apply]

theorem cr_polyFun {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    ∀ L : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ, ∃ P : MvPolynomial (Fin N × Fin N) ℂ,
      ∀ g : Matrix (Fin N) (Fin N) ℂ, L (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM g P := by
  intro L
  let Φ : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ]
      MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) ℂ) :=
    aeval fun v => ∑ b : Fin N, C (X (v.1, b) : MvPolynomial (Fin N × Fin N) ℂ) * X (b, v.2)
  have hmap : ∀ g : Matrix (Fin N) (Fin N) ℂ,
      MvPolynomial.map (MvPolynomial.eval fun v : Fin N × Fin N => g v.1 v.2) (Φ s) = Formalism.GradedWeylDivisibility.rowAct ℂ g s := by
    intro g
    induction s using MvPolynomial.induction_on
    next a =>
      rw [cr_rowAct_C]
      simp [Φ]
    next p q hp hq =>
      simp only [map_add (f := _), hp, hq]
    next p w hp =>
      simp only [map_mul, hp, cr_rowAct_X]

      simp only [Φ, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.eval_X]
  have hmono : ∀ (m : Fin N × Fin N →₀ ℕ) (a : ℂ), L (monomial m a) = a * L (monomial m 1) := by
    intro m a
    calc L (monomial m a) = L (a • monomial m (1 : ℂ)) := by rw [smul_monomial, smul_eq_mul, mul_one]
      _ = a * L (monomial m 1) := by rw [map_smul, smul_eq_mul]
  refine ⟨∑ m ∈ (Φ s).support, (Φ s).coeff m * C (L (monomial m 1)), fun g => ?_⟩
  rw [← hmap g]
  conv_lhs => rw [(Φ s).as_sum]

  simp only [map_sum, MvPolynomial.map_monomial, evalM, map_mul, MvPolynomial.eval_C]
  exact Finset.sum_congr rfl fun m _ => hmono m _

end PI.WSF
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionC

section

@[expose] public section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory Matrix

private lemma normFock_add_left {N : ℕ} (lam : DomWeight N) (p p' q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (p + p') q = normFock lam p q + normFock lam p' q := by
  simpa [cf_Blin_apply] using (Blin lam q).map_add p p'

private lemma normFock_smul_left {N : ℕ} (lam : DomWeight N) (c : ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (c • p) q = c * normFock lam p q := by
  have := (Blin lam q).map_smul c p
  rwa [cf_Blin_apply, cf_Blin_apply, smul_eq_mul] at this

private lemma aform_sum_smul_left {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ) {ι : Type*}
    (t : Finset ι) (c : ι → ℂ) (p : ι → MvPolynomial (Fin N × Fin N) ℂ) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ (∑ i ∈ t, c i • p i) q = ∑ i ∈ t, c i * Aform μ (p i) q := by

  simp only [← ci_Alin_apply hμ, map_sum, map_smul, smul_eq_mul]

private lemma exists_nonneg_fockF_self {σ : Type*} (f : MvPolynomial σ ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ Formalism.REAL.fockF f f = (r : ℂ) := by
  refine ⟨∑ m ∈ f.support, Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ),
    Finset.sum_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _), ?_⟩
  unfold Formalism.REAL.fockF
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.star_def, Complex.mul_conj]

private lemma normFock_self_re_nonneg_and_real {N : ℕ} (lam : DomWeight N) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    0 ≤ (normFock lam p p).re ∧ normFock lam p p = ((normFock lam p p).re : ℂ) := by
  obtain ⟨a, ha, hpa⟩ := exists_nonneg_fockF_self p
  obtain ⟨b, hb, heb⟩ := exists_nonneg_fockF_self (extremal ℂ N lam)
  have h : normFock lam p p = ((a / b : ℝ) : ℂ) := by
    rw [normFock, hpa, heb, Complex.ofReal_div]
  rw [h, Complex.ofReal_re]
  exact ⟨div_nonneg ha hb, rfl⟩

theorem schurOrth_of (h : PI.HwIrred) (hA : EvalOne) : SchurOrth := by
  intro N lam μ hμ s hs
  set V : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := nablaSq ℂ N lam with hV
  have hstab : ∀ (g : Matrix (Fin N) (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ), f ∈ V →
      Formalism.GradedWeylDivisibility.rowAct ℂ g f ∈ V :=
    fun g f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW g f hf
  have anti : Antitone lam.natW := fun a b hab => by
    have := lam.anti hab
    exact Int.toNat_le_toNat (by omega)
  have he : extremal ℂ N lam ∈ V := Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW anti
  have he0 : extremal ℂ N lam ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW
  haveI : FiniteDimensional ℂ V := by
    obtain ⟨bb, ⟨-, hspan, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ N N lam.natW
    haveI : Finite (Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N lam.natW).to_subtype
    have : V = Submodule.span ℂ (Set.range bb) := hspan.symm
    rw [this]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range bb)
  haveI : Nontrivial V := ⟨⟨⟨_, he⟩, 0, fun h0 => he0 (congrArg Subtype.val h0)⟩⟩
  letI core : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => normFock lam (y : MvPolynomial (Fin N × Fin N) ℂ) x
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (normFock lam (x : MvPolynomial (Fin N × Fin N) ℂ) y) = normFock lam y x
        rw [cf_herm lam (x : MvPolynomial (Fin N × Fin N) ℂ) y]
        rfl
      re_inner_nonneg := fun x => (normFock_self_re_nonneg_and_real lam x).1
      add_left := fun x y z => by
        show normFock lam (z : MvPolynomial (Fin N × Fin N) ℂ) ((x + y : V) : MvPolynomial (Fin N × Fin N) ℂ) =
          normFock lam z x + normFock lam z y
        rw [Submodule.coe_add, cf_herm lam ((x : MvPolynomial (Fin N × Fin N) ℂ) + y) z, normFock_add_left, star_add,
          ← cf_herm, ← cf_herm]
      smul_left := fun x y r => by
        show normFock lam (y : MvPolynomial (Fin N × Fin N) ℂ) ((r • x : V) : MvPolynomial (Fin N × Fin N) ℂ) =
          (starRingEnd ℂ) r * normFock lam y x
        rw [Submodule.coe_smul, cf_herm lam (r • (x : MvPolynomial (Fin N × Fin N) ℂ)) y, normFock_smul_left, star_mul',
          ← cf_herm]
        rfl
      definite := fun x hx => by
        by_contra hne
        exact normFock_self_ne_zero lam (x : MvPolynomial (Fin N × Fin N) ℂ) (fun h0 => hne (Subtype.ext h0)) hx }
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ core
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hin : ∀ x y : V, @inner ℂ V _ x y = normFock lam (y : MvPolynomial (Fin N × Fin N) ℂ) x := fun _ _ => rfl
  let b := stdOrthonormalBasis ℂ V
  let rv : Matrix (Fin N) (Fin N) ℂ → V → V := fun g x => ⟨Formalism.GradedWeylDivisibility.rowAct ℂ g x, hstab g x x.2⟩
  have hrv : ∀ g (x : V), (rv g x : MvPolynomial (Fin N × Fin N) ℂ) = Formalism.GradedWeylDivisibility.rowAct ℂ g x := fun _ _ => rfl
  have hunit : ∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ f : MvPolynomial (Fin N × Fin N) ℂ,
      Formalism.GradedWeylDivisibility.rowAct ℂ u (Formalism.GradedWeylDivisibility.rowAct ℂ u.conjTranspose f) = f := by
    intro u hu f
    rw [cr_rowAct_rowAct, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hu, cr_rowAct_one]

  let T : V →ₗ[ℂ] V := ∑ i, ((Alin hμ (b i : MvPolynomial (Fin N × Fin N) ℂ)).comp V.subtype).smulRight (b i)
  have hTapp : ∀ x : V, T x = ∑ i, Aform μ (x : MvPolynomial (Fin N × Fin N) ℂ) (b i) • b i := by
    intro x
    simp only [T]
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply, LinearMap.comp_apply, Submodule.subtype_apply, ci_Alin_apply]
  have hT : ∀ x w : V, @inner ℂ V _ (T x) w = Aform μ (w : MvPolynomial (Fin N × Fin N) ℂ) x := by
    intro x w
    have hw : (w : MvPolynomial (Fin N × Fin N) ℂ) =
        ∑ i, @inner ℂ V _ (b i) w • (b i : MvPolynomial (Fin N × Fin N) ℂ) := by
      conv_lhs => rw [← b.sum_repr' w]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hTapp, sum_inner, hw, aform_sum_smul_left hμ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, ci_herm μ (x : MvPolynomial (Fin N × Fin N) ℂ) (b i), mul_comm]
    rfl
  have hcomm : ∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ x : V, T (rv u x) = rv u (T x) := by
    intro u hu x
    refine ext_inner_right ℂ fun w => ?_
    have e1 : @inner ℂ V _ (rv u (T x)) w = @inner ℂ V _ (T x) (rv u.conjTranspose w) := by
      rw [hin, hin, hrv, hrv, cf_herm lam ((Formalism.GradedWeylDivisibility.rowAct ℂ u) (T x : MvPolynomial (Fin N × Fin N) ℂ)) w, cf_adj,
        ← cf_herm]
    rw [hT, e1, hT, hrv, ← ci_invariant hμ u hu (Formalism.GradedWeylDivisibility.rowAct ℂ u.conjTranspose w) x, hunit u hu]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v0, hv0⟩ := hc.exists_hasEigenvector
  have hkey : ∀ y : V, T y = c • y → ∀ g : Matrix (Fin N) (Fin N) ℂ, IsUnit g.det → T (rv g y) = c • rv g y := by
    intro y hy g hg
    set z : V := T (rv g y) - c • rv g y with hz
    let ℓ : V →ₗ[ℂ] ℂ := (innerₛₗ ℂ z).comp (T - c • LinearMap.id)
    obtain ⟨L, hL⟩ := LinearMap.exists_extend ℓ
    have hLv : ∀ p : V, L p = @inner ℂ V _ z (T p) - c * @inner ℂ V _ z p := fun p => by
      have h2 := LinearMap.congr_fun hL p
      simp [ℓ] at h2
      rw [h2, inner_sub_right, inner_smul_right]
    obtain ⟨P, hP⟩ := cr_polyFun (y : MvPolynomial (Fin N × Fin N) ℂ) L
    have hu0 : ∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, evalM u P = 0 := by
      intro u hu
      rw [← hP u, ← hrv u y, hLv, hcomm u hu, hy]
      have : rv u (c • y) = c • rv u y := Subtype.ext (by simp [hrv, map_smul])
      rw [this, inner_smul_right, sub_self]
    have h0 := cz_zariski P hu0 g hg
    rw [← hP g, ← hrv g y, hLv] at h0
    have hzz : @inner ℂ V _ z z = 0 := by
      nth_rewrite 2 [hz]
      rw [inner_sub_right, inner_smul_right]
      exact h0
    rw [← sub_eq_zero]
    exact inner_self_eq_zero.mp hzz
  let K := LinearMap.ker (T - c • LinearMap.id)
  have hK : ∀ y : V, y ∈ K ↔ T y = c • y := fun y => by
    simp [K, sub_eq_zero]
  let W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := K.map V.subtype
  have hWle : W ≤ nablaSq ℂ N lam := Submodule.map_subtype_le V K
  have hWinv : ∀ (g : GL (Fin N) ℂ), ∀ f ∈ W, sqAct ℂ N lam g f ∈ W := by
    intro g f hf
    obtain ⟨y, hy, rfl⟩ := hf
    have hg : IsUnit ((g : Matrix (Fin N) (Fin N) ℂ).transpose).det := by
      rw [Matrix.det_transpose]; exact Matrix.isUnits_det_units g
    refine W.smul_mem _ ⟨rv (g : Matrix (Fin N) (Fin N) ℂ).transpose y, (hK _).mpr
      (hkey y ((hK y).mp hy) _ hg), rfl⟩
  have hWne : W ≠ ⊥ := by
    intro h0
    have : (v0 : MvPolynomial (Fin N × Fin N) ℂ) ∈ W := ⟨v0, (hK v0).mpr hv0.apply_eq_smul, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact hv0.2 (Subtype.ext this)
  have hall : ∀ y : V, T y = c • y := by
    intro y
    rcases (h N lam).2.1 W hWle hWinv with h0 | h0
    · exact absurd h0 hWne
    · have : (y : MvPolynomial (Fin N × Fin N) ℂ) ∈ W := by rw [h0]; exact y.2
      obtain ⟨y', hy', hyy⟩ := this
      rw [← (Subtype.ext hyy : y' = y)]
      exact (hK y').mp hy'
  have hAB : ∀ x w : V, Aform μ (w : MvPolynomial (Fin N × Fin N) ℂ) x =
      (starRingEnd ℂ) c * normFock lam (w : MvPolynomial (Fin N × Fin N) ℂ) x := by
    intro x w
    rw [← hT, hall, inner_smul_left, hin]

  have hsum1 : ∀ x ∈ Matrix.unitaryGroup (Fin N) ℂ,
      ∑ i, evalM x (b i : MvPolynomial (Fin N × Fin N) ℂ) * star (evalM x (b i : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    intro x hx
    let y : V := rv x.conjTranspose ⟨_, he⟩
    have hev : ∀ i, evalM x (b i : MvPolynomial (Fin N × Fin N) ℂ) = @inner ℂ V _ y (b i) := by
      intro i
      have h1 := cr_evalM_rowAct x 1 (b i : MvPolynomial (Fin N × Fin N) ℂ)
      rw [mul_one] at h1
      rw [← h1, hA N lam _ (hstab x _ (b i).2), cf_adj, hin]
    simp only [hev]
    have : ∀ i, star (@inner ℂ V _ y (b i)) = @inner ℂ V _ (b i) y := fun i => inner_conj_symm _ _
    simp only [this]
    rw [b.sum_inner_mul_inner y y, hin, hrv, cf_adj, Matrix.conjTranspose_conjTranspose, hunit x hx]
    exact cf_ee lam
  have htrace : ∑ i, Aform μ (b i : MvPolynomial (Fin N × Fin N) ℂ) (b i) = 1 := by
    simp only [Aform]
    rw [← MeasureTheory.integral_finsetSum _ fun i _ => ci_integrable hμ (ci_cont2 _ _)]
    rw [integral_congr_ae (g := fun _ => (1 : ℂ)) ?_]
    · haveI := hμ.1
      simp
    · filter_upwards [hμ.2.1] with x hx
      exact hsum1 x hx
  have hcd : (starRingEnd ℂ) c * (Module.finrank ℂ V : ℂ) = 1 := by
    have hdiag : ∀ i, Aform μ (b i : MvPolynomial (Fin N × Fin N) ℂ) (b i) = (starRingEnd ℂ) c := by
      intro i
      rw [hAB, ← hin]
      have : @inner ℂ V _ (b i) (b i) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
      rw [this, mul_one]
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htrace
    rw [mul_comm]; exact htrace
  have hss : normFock lam s s = (Module.finrank ℂ V : ℂ) * Aform μ s s := by
    rw [show s = ((⟨s, hs⟩ : V) : MvPolynomial (Fin N × Fin N) ℂ) from rfl, hAB, ← mul_assoc,
      mul_comm (Module.finrank ℂ V : ℂ), hcd, one_mul]
  have hint : Aform μ s s = ((∫ x, ‖evalM x s‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [Aform, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdim : Module.finrank ℂ (delSq ℂ N lam) = Module.finrank ℂ V := by
    rw [hV, (h N lam).1]
  rw [hss, hint, hdim, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]

end PI.WSF
end
end
end
