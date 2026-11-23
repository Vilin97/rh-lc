module

public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DeltaPsiH
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.CovDet
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TwoLatLeTwoSp
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ExplicitMapOntoTwoLetterSpace
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaNuNextAdd
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.CovWeyl

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TaIntOfRename

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def ta_covR (A : Type) [CommRing A] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A))

theorem ta_covR_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (i : Fin (m + 1)) :
    map φ (ta_covR A m i) = ta_covR B m i := by
  unfold ta_covR
  rw [map_mul, map_pow, map_neg, map_one]
  congr 1
  exact (RingHom.map_det (map φ) (Matrix.of fun a b : Fin m =>
    (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A))).trans (by
      congr 1
      ext a b
      simp)

theorem ta_covR_eq (K : Type) [Field K] (m : ℕ) : ta_covR K m = covY K m := rfl

theorem ta_aeval_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (β : MvPolynomial (Fin (m + 1)) A) :
    map φ (aeval (ta_covR A m) β) = aeval (ta_covR B m) (map φ β) := by
  induction β using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X, ta_covR_map]

section Int

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

def ta_Int (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K] {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∃ β : MvPolynomial σ O, map (algebraMap O K) β = F

theorem ta_Int_coeff {σ : Type} {F : MvPolynomial σ K} (h : ta_Int O F) (u : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff F u ∈ Set.range (algebraMap O K) := by
  obtain ⟨β, rfl⟩ := h
  exact ⟨AddMonoidAlgebra.coeff β u, (coeff_map _ _ _).symm⟩

theorem ta_Int_of_coeff {σ : Type} {F : MvPolynomial σ K} (h : ∀ u, AddMonoidAlgebra.coeff F u ∈ Set.range (algebraMap O K)) :
    ta_Int O F := by
  classical
  choose c hc using h
  refine ⟨∑ u ∈ F.support, monomial u (c u), ?_⟩

  simp only [map_sum, map_monomial, hc]
  exact F.support_sum_monomial_coeff

theorem ta_Int_add {σ : Type} {F G : MvPolynomial σ K} (h1 : ta_Int O F) (h2 : ta_Int O G) : ta_Int O (F + G) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨a + b, map_add _ _ _⟩

theorem ta_Int_mul {σ : Type} {F G : MvPolynomial σ K} (h1 : ta_Int O F) (h2 : ta_Int O G) : ta_Int O (F * G) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨a * b, map_mul _ _ _⟩

theorem ta_Int_smul {σ : Type} {F : MvPolynomial σ K} (c : O) (h : ta_Int O F) : ta_Int O (algebraMap O K c • F) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨C c * a, by rw [map_mul, map_C, smul_eq_C_mul]⟩

theorem ta_Int_rename {σ τ : Type} (e : σ → τ) {F : MvPolynomial σ K} (h : ta_Int O F) : ta_Int O (rename e F) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨rename e a, map_rename _ _ _⟩

theorem ta_Int_of_rename {σ τ : Type} (e : σ → τ) (he : Function.Injective e) {F : MvPolynomial σ K}
    (h : ta_Int O (rename e F)) : ta_Int O F := by
  refine ta_Int_of_coeff fun u => ?_
  rw [← coeff_rename_mapDomain e he]
  exact ta_Int_coeff h _

theorem ta_Int_prodX {k : ℕ} (a : Fin k → ℕ) : ta_Int O (∏ i, X i ^ a i : MvPolynomial (Fin k) K) :=
  ⟨∏ i, X i ^ a i, by simp [map_prod]⟩

theorem ta_Int_aeval (m : ℕ) {b : MvPolynomial (Fin (m + 1)) K} (h : ta_Int O b) : ta_Int O (aeval (covY K m) b) := by
  obtain ⟨β, rfl⟩ := h
  exact ⟨aeval (ta_covR O m) β, by rw [ta_aeval_map, ta_covR_eq]⟩

end Int

section Sat

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem ta_exists_pow (w : O) (hw : Irreducible w) {σ : Type} (b : MvPolynomial σ K) :
    ∃ n : ℕ, ta_Int O ((algebraMap O K w ^ n) • b) := by
  classical
  obtain ⟨⟨s, hs⟩, hsI⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (b.support.image fun u => AddMonoidAlgebra.coeff b u)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hw
  refine ⟨n, ta_Int_of_coeff fun u => ?_⟩
  change algebraMap O K w ^ n * AddMonoidAlgebra.coeff b u ∈ _
  by_cases hu : u ∈ b.support
  · obtain ⟨r, hr⟩ := hsI _ (Finset.mem_image_of_mem _ hu)
    refine ⟨(↑v⁻¹ : O) * r, ?_⟩
    have hr' : algebraMap O K r = algebraMap O K s * AddMonoidAlgebra.coeff b u := by
      rw [hr]
      exact Algebra.smul_def _ _
    rw [map_mul, hr', hv, map_mul, map_pow, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · rw [mem_support_iff, not_not] at hu
    exact ⟨0, by rw [hu, mul_zero, map_zero]⟩

theorem ta_sat (w : O) (hw : Irreducible w) (m : ℕ) (hm : 1 ≤ m) (b : MvPolynomial (Fin (m + 1)) K)
    (h : ta_Int O (aeval (covY K m) b)) : ta_Int O b := by
  classical
  have hw0 : w ≠ 0 := hw.ne_zero
  have hinjOK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hW0 : algebraMap O K w ≠ 0 := fun h0 => hw0 (hinjOK (by rw [h0, map_zero]))
  obtain ⟨γ, hγ⟩ := h
  haveI hmax : (Ideal.span {w}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hw
  letI : Field (O ⧸ Ideal.span {w}) := Ideal.Quotient.field _
  have hind : Function.Injective (aeval (R := O ⧸ Ideal.span {w}) (covY (O ⧸ Ideal.span {w}) m)) := by
    have := Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_alg_independent (O ⧸ Ideal.span {w}) m hm
    rw [covY_eq] at this
    exact this
  have step : ∀ n : ℕ, ta_Int O (algebraMap O K w ^ (n + 1) • b) → ta_Int O (algebraMap O K w ^ n • b) := by
    intro n hn
    obtain ⟨β, hβ⟩ := hn
    have e1 : map (algebraMap O K) (aeval (ta_covR O m) β) = map (algebraMap O K) (C (w ^ (n + 1)) * γ) := by
      rw [ta_aeval_map, ta_covR_eq, hβ, map_smul, map_mul, map_C, hγ, smul_eq_C_mul]
      simp only [map_pow]
    have e2 := map_injective _ hinjOK e1
    have e3 : aeval (R := O ⧸ Ideal.span {w}) (covY (O ⧸ Ideal.span {w}) m)
        (map (Ideal.Quotient.mk (Ideal.span {w})) β) = 0 := by
      rw [← ta_covR_eq, ← ta_aeval_map, e2, map_mul, map_C, map_pow,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w), zero_pow (Nat.succ_ne_zero n),
        C_0, zero_mul]
    have e4 : map (Ideal.Quotient.mk (Ideal.span {w})) β = 0 := hind (by rw [e3, map_zero])
    apply ta_Int_of_coeff
    intro u
    have hu : AddMonoidAlgebra.coeff β u ∈ Ideal.span {w} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := congrArg (AddMonoidAlgebra.coeff · u) e4
      rwa [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hu
    refine ⟨c, ?_⟩
    have e5 := congrArg (AddMonoidAlgebra.coeff · u) hβ
    rw [coeff_map, ← hc, map_mul] at e5
    change _ = algebraMap O K w ^ (n + 1) * AddMonoidAlgebra.coeff b u at e5
    change algebraMap O K c = algebraMap O K w ^ n * AddMonoidAlgebra.coeff b u
    apply mul_right_cancel₀ hW0
    rw [e5]
    ring
  obtain ⟨n, hn⟩ := ta_exists_pow w hw b
  induction n with
  | zero => simpa using hn
  | succ n ih => exact ih (step n hn)

end Sat

section Act

variable {K : Type} [Field K] {m : ℕ}

theorem ta_Psi_gl_alt (g' : GL (Fin (m + 1)) K) (a : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (glAct g' (rename Sum.inl a)) =
      blockEmb K true (rowAct K (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (rename (fun i => (i, (0 : Fin (m + 1)))) a)) := by
  have key : (PsiXY K m).comp ((Formalism.CountingSumsFrames.glAct g').comp (rename Sum.inl)) =
      (blockEmb K true).comp ((rowAct K (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).comp
        (rename fun i => (i, (0 : Fin (m + 1))))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [PsiXY, Formalism.CountingSumsFrames.glAct, blockEmb, rowAct, algebraMap_eq]
  exact DFunLike.congr_fun key a

theorem ta_Psi_gl_y (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) K)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g⁻¹) (b : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (glAct g' (rename Sum.inr b)) =
      blockEmb K false (aeval (fun i => C g.det * rowAct K g⁻¹ (covY K m i)) b) := by
  have hinv : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
  have hd0 : g.det ≠ 0 := hg.ne_zero
  have key : (PsiXY K m).comp ((Formalism.CountingSumsFrames.glAct g').comp (rename Sum.inr)) =
      (blockEmb K false).comp (aeval fun i => C g.det * rowAct K g⁻¹ (covY K m i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    have h5 := Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_cofactor_transform K m g⁻¹ i hinv
    rw [covY_eq] at h5
    have hgg : ((g'⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g := by
      rw [Matrix.coe_units_inv, hg', Matrix.nonsing_inv_nonsing_inv g hg]

    simp only [AlgHom.comp_apply, rename_X, aeval_X, Formalism.CountingSumsFrames.glAct, Sum.elim_inr, map_sum, map_mul, hgg]

    rw [h5, ← map_mul, ← mul_assoc, ← C_mul, Matrix.nonsing_inv_nonsing_inv g hg, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', mul_inv_cancel₀ hd0, C_1, one_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    unfold PsiXY blockEmb
    rw [aeval_C, aeval_X, Sum.elim_inr, rename_C, algebraMap_eq]
  exact DFunLike.congr_fun key b

theorem ta_aeval_scale {τ : Type} {k Q : ℕ} (d : K) (z : Fin k → MvPolynomial τ K) (b : MvPolynomial (Fin k) K)
    (hb : b.IsHomogeneous Q) : aeval (fun i => C d * z i) b = d ^ Q • aeval z b := by
  classical
  conv_lhs => rw [b.as_sum]
  conv_rhs => rw [b.as_sum]

  simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hdeg := hb (mem_support_iff.mp hu)
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [smul_eq_C_mul, ← map_pow]
  have hQ : ∑ i ∈ u.support, u i = Q := by
    rw [← hdeg]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hQ]
  ring

theorem ta_aeval_rowAct (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (b : MvPolynomial (Fin (m + 1)) K) :
    aeval (fun i => rowAct K h (covY K m i)) b = rowAct K h (aeval (covY K m) b) := by
  exact (DFunLike.congr_fun (comp_aeval (covY K m) (rowAct K h)) b).symm

theorem ta_Psi_gl (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) K)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g⁻¹) (Q : ℕ) (a b : MvPolynomial (Fin (m + 1)) K)
    (hb : b.IsHomogeneous Q) :
    PsiXY K m (glAct g' (rename Sum.inl a * rename Sum.inr b)) =
      blockEmb K true (rowAct K g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a)) *
        blockEmb K false (g.det ^ Q • rowAct K g⁻¹ (aeval (covY K m) b)) := by
  rw [map_mul, map_mul, ta_Psi_gl_alt, ta_Psi_gl_y g hg g' hg', hg', ta_aeval_scale g.det _ b hb, ta_aeval_rowAct]

end Act

end Formalism.MainNotions.flipOneThree.Pf

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TwoLetterLatticeGaussInverse

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem ta_last_ne (m : ℕ) (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have h2 := congrArg Fin.val h
  simp at h2
  omega

section L

variable {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (hg : IsUnit g.det)

include hm hg

theorem ta_vec_mem (P : ℕ) (a : MvPolynomial (Fin (m + 1)) R.Kf) (ha : a.IsHomogeneous P) (hI : ta_Int R.O a) :
    rowAct R.Kf g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a) ∈ H0 R.O m (letterWt m P true) (colSpan R.O g) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  refine (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).2 ?_
  have h0 : letterWt m P true (Fin.last m) = 0 := by simp [letterWt, ta_last_ne m hm]
  rw [h0, zpow_zero, one_smul, rowAct_inv_cancel g hg]
  refine intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_rename _ hI) u)
  rw [ta_nuOf_vec m P hm]
  exact (ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).2 ⟨a, ha, rfl⟩

theorem ta_cov_mem (Q : ℕ) (b : MvPolynomial (Fin (m + 1)) R.Kf) (hb : b.IsHomogeneous Q) (hI : ta_Int R.O b) :
    g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) b) ∈ H0 R.O m (letterWt m Q false) (colSpan R.O g) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  refine (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).2 ?_
  have h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ) := by simp [letterWt]
  rw [h0, map_smul, rowAct_inv_cancel g hg, smul_smul, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]
  refine intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_aeval m hI) u)
  rw [ta_nuOf_cov m Q]
  exact (ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).2 ⟨b, hb, rfl⟩

theorem ta_vec_of (P : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
    (hF : F ∈ H0 R.O m (letterWt m P true) (colSpan R.O g)) :
    ∃ a : MvPolynomial (Fin (m + 1)) R.Kf, a.IsHomogeneous P ∧ ta_Int R.O a ∧
      F = rowAct R.Kf g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have h1 := (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).1 hF
  have h0 : letterWt m P true (Fin.last m) = 0 := by simp [letterWt, ta_last_ne m hm]
  rw [h0, zpow_zero, one_smul] at h1
  have h2 := intO_le _ _ _ h1
  rw [ta_nuOf_vec m P hm] at h2
  obtain ⟨a, ha, e⟩ := (ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).1 h2
  refine ⟨a, ha, ta_Int_of_rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1)))) ?_ ?_, ?_⟩
  · intro i j hij
    exact (Prod.mk.inj hij).1
  · rw [e]
    obtain ⟨f, -, hf⟩ := h1
    exact ⟨f, hf⟩
  · rw [e, rowAct_cancel_inv g hg]

theorem ta_cov_of (Q : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
    (hF : F ∈ H0 R.O m (letterWt m Q false) (colSpan R.O g)) :
    ∃ b : MvPolynomial (Fin (m + 1)) R.Kf, b.IsHomogeneous Q ∧ ta_Int R.O b ∧
      F = g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) b) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have h1 := (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).1 hF
  have h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ) := by simp [letterWt]
  rw [h0] at h1
  have h2 := intO_le _ _ _ h1
  rw [ta_nuOf_cov m Q] at h2
  obtain ⟨b, hb, e⟩ := (ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).1 h2
  rw [covY_eq] at e
  refine ⟨b, hb, ta_sat R.w R.std.2.1 m hm b ?_, ?_⟩
  · rw [e]
    obtain ⟨f, -, hf⟩ := h1
    exact ⟨f, hf⟩
  · rw [e, map_smul, rowAct_cancel_inv g hg, smul_smul, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]

end L

theorem two_letter_lattice_gauss_inverse : TwoLetterLatticeGaussInverse := by
  intro p n' R m hm g hg g' hg' P Q f hf
  constructor
  · intro hx
    have key : ∀ x ∈ twoLat R.O m P Q (colSpan R.O g),
        ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x := by
      intro x hx
      unfold twoLat tensorLat at hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x) ?_ ?_ ?_ ?_ hx
      · rintro y ⟨F, hF, rfl⟩
        have ht := hF true
        have hf' := hF false
        simp only [ite_true, Bool.false_eq_true, ite_false] at ht hf'
        obtain ⟨a, ha, hIa, ea⟩ := ta_vec_of R m hm g hg P _ ht
        obtain ⟨b, hb, hIb, eb⟩ := ta_cov_of R m hm g hg Q _ hf'
        refine ⟨rename Sum.inl a * rename Sum.inr b, ta_Int_mul (ta_Int_rename _ hIa) (ta_Int_rename _ hIb), ?_⟩
        rw [ta_Psi_gl g hg g' hg' Q a b hb, ← ea, ← eb, Fintype.prod_bool]
      · exact ⟨0, ⟨0, map_zero _⟩, by simp⟩
      · rintro x y _ _ ⟨f1, h1, rfl⟩ ⟨f2, h2, rfl⟩
        exact ⟨f1 + f2, ta_Int_add h1 h2, by rw [map_add (f := _), map_add (f := _)]⟩
      · rintro c x _ ⟨f1, h1, rfl⟩
        exact ⟨algebraMap R.O R.Kf c • f1, ta_Int_smul c h1, by rw [map_smul, map_smul, algebraMap_smul]⟩
    obtain ⟨f₀, hI, he⟩ := key _ hx
    have h1 := explicit_map_injective R.Kf m hm he
    refine ⟨f₀, fun u => ?_, h1⟩
    obtain ⟨c, hc⟩ := ta_Int_coeff hI u
    rw [← hc]
    exact R.mem_Ov c
  · rintro ⟨f₀, hG, rfl⟩
    have hf₀ : f₀ ∈ PolAB R.Kf (m + 1) P Q := by
      have := glAct_mem_PolAB g'⁻¹ _ hf
      rwa [glAct_inv_glAct] at this

    rw [f₀.as_sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    obtain ⟨c, hc⟩ : ∃ c : R.O, algebraMap R.O R.Kf c = AddMonoidAlgebra.coeff f₀ v := hG v
    rw [ta_monomial_split, map_smul, map_smul, ← hc, algebraMap_smul]
    refine Submodule.smul_mem _ _ ?_
    have hP : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i)).IsHomogeneous P := by
      have := ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inl i))
      rwa [show ∑ i : Fin (m + 1), v (Sum.inl i) = P from (hf₀ v hv).1] at this
    have hQ : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)).IsHomogeneous Q := by
      have := ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inr i))
      rwa [show ∑ i : Fin (m + 1), v (Sum.inr i) = Q from (hf₀ v hv).2] at this
    rw [ta_Psi_gl g hg g' hg' Q _ _ hQ]
    refine Submodule.subset_span ⟨fun b : Bool => (cond b
      (rowAct R.Kf g⁻¹ (rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1))))
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i))))
      (g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m)
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf), ?_, ?_⟩
    · intro b
      cases b
      · simp only [Bool.false_eq_true, ite_false, Bool.cond_false]
        exact ta_cov_mem R m hm g hg Q _ hQ (ta_Int_prodX _)
      · simp only [ite_true, Bool.cond_true]
        exact ta_vec_mem R m hm g hg P _ hP (ta_Int_prodX _)
    · rw [Fintype.prod_bool]
      rfl

end Formalism.MainNotions.flipOneThree.Pf

end
end
end
