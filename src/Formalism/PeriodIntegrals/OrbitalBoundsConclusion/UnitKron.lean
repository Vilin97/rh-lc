module

public import Formalism.PeriodIntegrals.UnitKron
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Development
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.EqZeroOfMulVec

section

@[expose] public section

namespace PI.UnitKronW

open Matrix Polynomial ComplexOrder

theorem pres_pow {k : ℕ} {H G : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ * H * G = H) (n : ℕ) :
    (G ^ n)ᴴ * H * G ^ n = H := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.conjTranspose_mul]
    calc Gᴴ * (G ^ n)ᴴ * H * (G ^ n * G) = Gᴴ * ((G ^ n)ᴴ * H * G ^ n) * G := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ih, hG]

theorem eq_zero_of_mulVec {k : ℕ} (N : Matrix (Fin k) (Fin k) ℂ) (h : ∀ x, N *ᵥ x = 0) : N = 0 := by
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by simp [Matrix.toLin'_apply, h])

theorem unip_step {k : ℕ} {H W : Matrix (Fin k) (Fin k) ℂ} (hH : H.PosDef) (hW : Wᴴ * H * W = H)
    (v : Fin k → ℂ) (hv : (W - 1) *ᵥ ((W - 1) *ᵥ v) = 0) : (W - 1) *ᵥ v = 0 := by
  have pres : ∀ x y : Fin k → ℂ, star (W *ᵥ x) ⬝ᵥ (H *ᵥ (W *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hW]
  obtain ⟨u, hu⟩ : ∃ u, u = (W - 1) *ᵥ v := ⟨_, rfl⟩
  rw [← hu] at hv ⊢
  have hWu : W *ᵥ u = u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have hu2 : u = W *ᵥ v - v := by rw [hu, Matrix.sub_mulVec, Matrix.one_mulVec]
  have h1 : star u ⬝ᵥ (H *ᵥ (W *ᵥ v)) = star u ⬝ᵥ (H *ᵥ v) := by
    have := pres u v
    rw [hWu] at this
    exact this
  have key : star u ⬝ᵥ (H *ᵥ u) = 0 := by
    nth_rw 2 [hu2]
    rw [Matrix.mulVec_sub]
    first
      | rw [dotProduct_sub, h1, sub_self]
      | rw [Matrix.dotProduct_sub, h1, sub_self]
  by_contra hne
  have hpos : 0 < star u ⬝ᵥ (H *ᵥ u) := by
    first
      | exact hH.2 u hne
      | exact hH.dotProduct_mulVec_pos hne
  rw [key] at hpos
  exact lt_irrefl _ hpos

theorem unip_pow {k : ℕ} {H W : Matrix (Fin k) (Fin k) ℂ} (hH : H.PosDef) (hW : Wᴴ * H * W = H) :
    ∀ j : ℕ, (W - 1) ^ (j + 1) = 0 → W - 1 = 0 := by
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply eq_zero_of_mulVec
    intro x
    have e : (W - 1) ^ (j + 1 + 1) *ᵥ x = (W - 1) *ᵥ ((W - 1) *ᵥ ((W - 1) ^ j *ᵥ x)) := by
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h2 : (W - 1) *ᵥ ((W - 1) *ᵥ ((W - 1) ^ j *ᵥ x)) = 0 := by
      rw [← e, h, Matrix.zero_mulVec]
    have h3 := unip_step hH hW _ h2
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact h3

theorem charpoly_dvd {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (n : ℕ)
    (hn : ∀ μ ∈ G.charpoly.roots, μ ^ n = 1) : G.charpoly ∣ (X ^ n - 1 : ℂ[X]) ^ k := by
  have hmon : G.charpoly.Monic := Matrix.charpoly_monic G
  have hcard : Multiset.card G.charpoly.roots = k := by
    have h1 : Multiset.card G.charpoly.roots = G.charpoly.natDegree := by
      first
        | exact (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))
        | exact IsAlgClosed.card_roots_eq_natDegree
        | exact (Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits _)).symm
    rw [h1, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hprod : (G.charpoly.roots.map fun a => X - C a).prod = G.charpoly :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
      rw [hcard, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  rw [← hprod]
  have hd : (G.charpoly.roots.map fun a => X - C a).prod ∣
      (G.charpoly.roots.map fun _ => (X ^ n - 1 : ℂ[X])).prod := by
    apply Multiset.prod_dvd_prod_of_dvd
    intro μ hμ
    rw [Polynomial.dvd_iff_isRoot]
    simp [hn μ hμ]
  rw [Multiset.map_const', Multiset.prod_replicate, hcard] at hd
  exact hd

theorem stepC : StepC := by
  unfold StepC
  intro k H G hH hG n hn
  have hW := pres_pow hG n
  have hdvd := charpoly_dvd G n hn
  have h0 : (G ^ n - 1) ^ k = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    have h := congrArg (Polynomial.aeval G) hq
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul] at h
    simpa using h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · ext i j
    exact Fin.elim0 i
  · have h1 := unip_pow hH hW (k - 1) (by rw [Nat.sub_add_cancel hk]; exact h0)
    exact sub_eq_zero.mp h1

end PI.UnitKronW
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.IntRootProp

section

@[expose] public section

namespace PI.UnitKronW

open Polynomial NumberField

def IntRootProp : Prop :=
  ∀ (E L : Type) [Field E] [Field L] [Algebra E L] (p : E[X]), p.Monic → (∀ i, IsIntegral ℤ (p.coeff i)) →
    ∀ x : L, (p.map (algebraMap E L)).IsRoot x → IsIntegral ℤ x

theorem stepB_of (hI : IntRootProp) : StepB := by
  intro E _ _ p hp hc hnorm φ₀ μ hμ
  have h1 : eval₂ φ₀ μ p = 0 := by rw [← eval_map]; exact hμ
  obtain ⟨q, hq0, hirr, hqp, hqμ⟩ : ∃ q : E[X], q ≠ 0 ∧ Irreducible q ∧ q ∣ p ∧ eval₂ φ₀ μ q = 0 := by
    letI : Algebra E ℂ := φ₀.toAlgebra
    have hμa : aeval μ p = 0 := by rw [aeval_def]; exact h1
    have hint_r : IsIntegral E μ := ⟨p, hp, h1⟩
    refine ⟨minpoly E μ, minpoly.ne_zero hint_r, minpoly.irreducible hint_r, minpoly.dvd E μ hμa, ?_⟩
    have h3 := minpoly.aeval E μ
    rw [aeval_def] at h3
    exact h3
  haveI : Fact (Irreducible q) := ⟨hirr⟩
  haveI : Module.Finite E (AdjoinRoot q) := Module.Finite.of_basis (AdjoinRoot.powerBasis hq0).basis
  haveI : NumberField (AdjoinRoot q) := NumberField.of_module_finite E (AdjoinRoot q)
  have hx : (p.map (algebraMap E (AdjoinRoot q))).IsRoot (AdjoinRoot.root q) := by
    show eval (AdjoinRoot.root q) (p.map (algebraMap E (AdjoinRoot q))) = 0
    rw [eval_map, AdjoinRoot.algebraMap_eq]
    obtain ⟨r, hr⟩ := hqp
    rw [hr, eval₂_mul, AdjoinRoot.eval₂_root, zero_mul]
  have hxint : IsIntegral ℤ (AdjoinRoot.root q) := hI E (AdjoinRoot q) p hp hc _ hx
  have hxn : ∀ ψ : AdjoinRoot q →+* ℂ, ‖ψ (AdjoinRoot.root q)‖ = 1 := by
    intro ψ
    apply hnorm (ψ.comp (algebraMap E (AdjoinRoot q))) (ψ (AdjoinRoot.root q))
    have h2 : eval₂ (algebraMap E (AdjoinRoot q)) (AdjoinRoot.root q) p = 0 := by
      rw [← eval_map]; exact hx
    show eval (ψ (AdjoinRoot.root q)) (p.map (ψ.comp (algebraMap E (AdjoinRoot q)))) = 0
    rw [eval_map, ← hom_eval₂, h2, map_zero]
  obtain ⟨n, hn, hxpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := AdjoinRoot q) (A := ℂ) hxint hxn
  refine ⟨n, hn, ?_⟩
  calc μ ^ n = (AdjoinRoot.lift φ₀ μ hqμ (AdjoinRoot.root q)) ^ n := by rw [AdjoinRoot.lift_root]
    _ = 1 := by rw [← map_pow, hxpow, map_one]

end PI.UnitKronW

namespace PI.UnitKronW

open Polynomial

theorem intRootProp : IntRootProp := by
  intro E L _ _ _ p hp hc x hx
  have hcoef : ∀ n, (p.map (algebraMap E L)).coeff n ∈
      Set.range (algebraMap (integralClosure ℤ L) L) := by
    intro n
    rw [coeff_map]
    have hmem : algebraMap E L (p.coeff n) ∈ integralClosure ℤ L := by
      rw [mem_integralClosure_iff]
      exact (hc n).map (algebraMap E L).toIntAlgHom
    exact ⟨⟨algebraMap E L (p.coeff n), hmem⟩, rfl⟩
  obtain ⟨r, hr, -, hrm⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts _).mpr hcoef) (hp.map (algebraMap E L))
  have hxS : IsIntegral (integralClosure ℤ L) x := by
    refine ⟨r, hrm, ?_⟩
    rw [← eval_map, hr]
    exact hx
  exact isIntegral_trans x hxS

theorem stepB : StepB :=
  stepB_of intRootProp

end PI.UnitKronW
end
end

-- Source module: Lemmata.GeneralBFactRightBis.Imports

section

@[expose] public section

open Matrix Polynomial ComplexOrder

namespace Bl.general_b_fact_right_bis

theorem goal1 {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (μ : ℂ) (hμ : G.charpoly.IsRoot μ) :
    ∃ v : Fin k → ℂ, v ≠ 0 ∧ G *ᵥ v = μ • v := by
  have hdet : (Matrix.scalar (Fin k) μ - G).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hμ
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  rw [← h]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

end Bl.general_b_fact_right_bis
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.PosDefFormNeZero

section

@[expose] public section

namespace PI.UnitKronW

open Matrix Polynomial ComplexOrder

theorem form_pres {k : ℕ} {H G : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ * H * G = H) (x y : Fin k → ℂ) :
    star (G *ᵥ x) ⬝ᵥ (H *ᵥ (G *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
  conv_rhs => rw [← hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

theorem posDef_form_ne_zero {k : ℕ} {H : Matrix (Fin k) (Fin k) ℂ} (hH : H.PosDef) {v : Fin k → ℂ}
    (hv : v ≠ 0) : star v ⬝ᵥ (H *ᵥ v) ≠ 0 :=
  ((Matrix.posDef_iff_dotProduct_mulVec.mp hH).2 hv).ne'

theorem exists_eigenvector {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (μ : ℂ) (hμ : G.charpoly.IsRoot μ) :
    ∃ v : Fin k → ℂ, v ≠ 0 ∧ G *ᵥ v = μ • v := by
  first | exact Bl.general_b_fact_right_bis.goal1 .. | (apply Bl.general_b_fact_right_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis.goal1 <;> first | assumption | infer_instance)

theorem stepA : StepA := by
  intro k H G hH hG μ hμ
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector G μ hμ
  have h := form_pres hG v v
  rw [hv, Matrix.mulVec_smul, star_smul] at h
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
  have hq := posDef_form_ne_zero hH hv0
  have h1 : star μ * μ = 1 := by
    have : (star μ * μ) * (star v ⬝ᵥ (H *ᵥ v)) = 1 * (star v ⬝ᵥ (H *ᵥ v)) := by
      rw [one_mul]; linear_combination h
    exact mul_right_cancel₀ hq this
  have h2 : Complex.normSq μ = 1 := by
    have := congrArg Complex.re h1
    rw [Complex.star_def, mul_comm, Complex.mul_conj] at this
    simpa using this
  rw [Complex.normSq_eq_norm_sq] at h2
  nlinarith [norm_nonneg μ]

end PI.UnitKronW
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitKron

section

@[expose] public section

theorem unit_kronecker : PI.UnitKron :=
  PI.UnitKronW.unitKron_of PI.UnitKronW.stepA PI.UnitKronW.stepB PI.UnitKronW.stepC
end
end
