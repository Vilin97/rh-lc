module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicElementOfAlgebraicVectorSubspace
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfFrobeniusEigenvectorMemFilZero

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

theorem UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Bcr l) (δ : ℚ_[l]), c ≠ 0 → (PP l).φB c = algebraMap ℚ_[l] (Bcr l) δ * c → (PP l).ιB c ∈ ((PP l).PD (botExt l)).Fil 0 → ‖δ‖ ≤ 1 := by
  intro l _ c δ hc hφ hF
  by_contra hδ
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ
  have hv : δ.valuation < 0 := by
    by_contra h
    exact hδ ((Padic.norm_le_one_iff_val_nonneg δ).2 (not_lt.1 h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ((a + 1 : ℕ) : ℤ) = -δ.valuation := ⟨(-δ.valuation - 1).toNat, by push_cast; omega⟩
  have hl : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ‖δ * (l : ℚ_[l]) ^ (a + 1)‖ = 1 := by
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hδ0, ← zpow_add₀ hl, ha]
    simp
  let u : ℤ_[l] := ⟨δ * (l : ℚ_[l]) ^ (a + 1), hu.le⟩
  have huu : IsUnit u := PadicInt.isUnit_iff.2 hu
  obtain ⟨N, N', hNN, hN, hN', hφN, -⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace (l := l) (n := 1) (Matrix.of fun _ _ => u)
    (by rw [Matrix.det_fin_one]; exact huu)
  set P := PP l with hP
  set D := P.PD (botExt l) with hD
  have h1 : N 0 0 * N' 0 0 = 1 := by
    have := congrFun (congrFun hNN 0) 0
    simpa [Matrix.mul_apply] using this
  have h2 : P.φB (N 0 0) = algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * N 0 0 := by
    have := congrFun (congrFun hφN 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one] at this
    exact this
  set w := N 0 0
  set w' := N' 0 0 with hw'
  have h3 : algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w' = w' := by
    have h := congrArg P.φB h1
    rw [map_mul, map_one, h2] at h
    linear_combination w' * h - (algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w') * h1
  have ht : P.φB D.t = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * D.t := by
    have := D.t_φ
    rw [P.PD_φ, P.PD_p, Algebra.smul_def] at this
    exact this
  have hb : D.φ (c * D.t ^ (a + 1) * w') = c * D.t ^ (a + 1) * w' := by
    rw [P.PD_φ, map_mul, map_mul, map_pow, hφ, ht, mul_pow]
    rw [map_mul, map_pow] at h3
    linear_combination (c * D.t ^ (a + 1)) * h3
  have ht0 : D.ι D.t ∈ D.Fil 0 := D.Fil_anti 0 D.mem_filtration_one
  have htp : ∀ n : ℕ, D.ι (D.t ^ n) ∈ D.Fil 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero, map_one]; exact D.one_mem
    | succ n ih => rw [pow_succ, map_mul]; exact D.Fil_mul 0 0 _ _ ih ht0
  have hF1 : D.ι (c * D.t ^ (a + 1) * w') ∈ D.Fil 1 := by
    rw [map_mul, map_mul, pow_succ, map_mul]
    have e1 : D.ι c ∈ D.Fil 0 := by rw [P.PD_ι]; exact hF
    have e2 : D.ι w' ∈ D.Fil 0 := by rw [P.PD_ι]; exact hN' 0 0
    exact D.Fil_mul 1 0 _ _ (D.Fil_mul 0 1 _ _ e1 (D.Fil_mul 0 1 _ _ (htp a) D.mem_filtration_one)) e2
  obtain ⟨r, hr⟩ := D.fund _ hb (D.Fil_anti 0 hF1)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    have hw : IsUnit w' := IsUnit.of_mul_eq_one w (by rw [mul_comm]; exact h1)
    rw [eq_comm, hw.mul_left_eq_zero, (D.t_unit.pow _).mul_left_eq_zero] at hr
    exact hc hr
  have hone : (1 : P.R.BdR) ∈ D.Fil 1 := by
    rw [← hr, P.PD_ι, AlgHom.commutes] at hF1
    have := (D.Fil 1).smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 r⁻¹) hF1
    rwa [algebraMap_smul, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hr0, map_one] at this
  have := D.Fil_mul 1 1 _ _ D.mem_filtration_one hone
  rw [mul_one] at this
  exact D.not_mem_filtration_two this
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfFrobeniusPowEigenvectorMemFilZero

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem shift_prod {R : Type} [CommMonoid R] (a : ℕ → R) (f : ℕ) :
    (∏ i ∈ Finset.range f, a (i + 1)) * a 0 = (∏ i ∈ Finset.range f, a i) * a f := by
  rw [← Finset.prod_range_succ', Finset.prod_range_succ]

private theorem descend {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [IsDomain B]
    (PD : PeriodData G Qp K₀ K B BdR) (f : ℕ) (hσ : ∀ x, (PD.σ ^ f) x = x) (b : B) (δ : K₀) (hb : b ≠ 0)
    (hφ : (PD.φ ^ f) b = algebraMap K₀ B δ * b) (hF : ∀ i : ℕ, PD.ι ((PD.φ ^ i) b) ∈ PD.Fil 0) :
    ∃ (c : B) (x : Qp), c ≠ 0 ∧ PD.φ c = algebraMap Qp B x * c ∧ PD.ι c ∈ PD.Fil 0 ∧
      algebraMap Qp K₀ x = ∏ i ∈ Finset.range f, (PD.σ ^ i) δ := by
  have hinj : ∀ (i : ℕ) (y : B), y ≠ 0 → (PD.φ ^ i) y ≠ 0 := by
    intro i y hy h
    apply hy
    have h1 : Function.Injective (PD.φ ^ i) := by
      rw [AlgHom.coe_pow]; exact PD.φ_inj.iterate i
    exact h1 (h.trans (map_zero _).symm)
  have hK : ∀ (i : ℕ) (y : K₀), (PD.φ ^ i) (algebraMap K₀ B y) = algebraMap K₀ B ((PD.σ ^ i) y) := by
    intro i y
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, PD.φ_K₀]
  have hprod : ∀ a : ℕ → B, (∀ i, PD.ι (a i) ∈ PD.Fil 0) → PD.ι (∏ i ∈ Finset.range f, a i) ∈ PD.Fil 0 := by
    intro a ha
    rw [map_prod]
    exact Finset.prod_induction _ (fun y => y ∈ PD.Fil 0)
      (fun y z hy hz => by simpa using PD.Fil_mul 0 0 y z hy hz) PD.one_mem fun i _ => ha i
  have hδ : δ ≠ 0 := by
    rintro rfl
    exact hinj f b hb (by rw [hφ, map_zero, zero_mul])
  set c := ∏ i ∈ Finset.range f, (PD.φ ^ i) b with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hinj i b hb
  have hφc : PD.φ c = algebraMap K₀ B δ * c := by
    apply mul_right_cancel₀ hb
    have h := shift_prod (fun i => (PD.φ ^ i) b) f
    simp only [pow_succ', AlgHom.mul_apply, pow_zero, AlgHom.one_apply] at h
    rw [← map_prod, ← hc, hφ] at h
    rw [h]; ring
  set N := ∏ i ∈ Finset.range f, (PD.σ ^ i) δ with hN
  have hσN : PD.σ N = N := by
    apply mul_right_cancel₀ hδ
    have h := shift_prod (fun i => (PD.σ ^ i) δ) f
    simp only [pow_succ', AlgHom.mul_apply, pow_zero, AlgHom.one_apply] at h
    rw [← map_prod, ← hN, hσ] at h
    exact h
  obtain ⟨x, hx⟩ := PD.fund (algebraMap K₀ B N) (by rw [PD.φ_K₀, hσN]) (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR, Algebra.algebraMap_eq_smul_one]
    exact (PD.Fil 0).smul_mem _ PD.one_mem)
  refine ⟨∏ i ∈ Finset.range f, (PD.φ ^ i) c, x, Finset.prod_ne_zero_iff.2 fun i _ => hinj i c hc0, ?_,
    hprod _ fun i => ?_, ?_⟩
  · rw [hx, hN, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hφc, map_mul, hK]
  · rw [hc, map_prod]
    refine hprod _ fun j => ?_
    rw [← AlgHom.mul_apply, ← pow_add]
    exact hF _
  · rw [IsScalarTower.algebraMap_apply Qp K₀ B] at hx
    exact (algebraMap K₀ B).injective hx

private theorem norm_algHom' {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (Om l)}
    (f : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) : ‖f x‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq f f.toRingHom.injective x
  have h2 := minpoly.algHom_eq K.val K.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

theorem UpperTheory.norm_le_one_of_frobenius_pow_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ (b : Bcr l) (δ : ↥(K0 K)), b ≠ 0 → ((PP l).φB)^[f] b = algebraMap ↥(K0 K) (Bcr l) δ * b → (∀ i : ℕ, (PP l).ιB (((PP l).φB)^[i] b) ∈ ((PP l).PD (botExt l)).Fil 0) → ‖(δ : Om l)‖ ≤ 1 := by
  intro l _ K f hf hσ b δ hb hφ hF
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have e : ((PP l).PD K).φ = (PP l).φB := AlgHom.ext ((PP l).PD_φ K)
  have hFil : ∀ y, y ∈ ((PP l).PD K).Fil 0 ↔ y ∈ ((PP l).PD (botExt l)).Fil 0 := fun y => by
    rw [← SetLike.mem_coe, (PP l).PD_Fil K (botExt l), SetLike.mem_coe]
  obtain ⟨c, x, hc, hφc, hFc, hx⟩ := descend ((PP l).PD K) f (fun y => by rw [AlgHom.coe_pow, hσ]) b δ hb
    (by rw [e, AlgHom.coe_pow, hφ]) (fun i => by rw [e, AlgHom.coe_pow, (PP l).PD_ι, hFil]; exact hF i)
  rw [e] at hφc
  rw [(PP l).PD_ι, hFil] at hFc
  have h1 := UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero c x hc hφc hFc
  have h2 := congrArg (fun y : ↥(K0 K) => ‖(K0 K).val y‖) hx
  simp only [map_prod, norm_prod, AlgHom.commutes] at h2
  have h3 : ∀ i : ℕ, ‖(K0 K).val ((((PP l).PD K).σ ^ i) δ)‖ = ‖(δ : Om l)‖ :=
    fun i => norm_algHom' ((K0 K).val.comp (((PP l).PD K).σ ^ i)) δ
  simp only [h3] at h2
  rw [Finset.prod_const, Finset.card_range, norm_algebraMap'] at h2
  rw [h2] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hf.ne').1 h1
end
end
