module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeFrobeniusSolutionsPowDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDiscStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEqOfPowSmulComparisonMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixPhiEquationToFamilyEquationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturatedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDiscStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdGaloisComparisonMatrix

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_dvd_map_of_smul_eq {A D W : Type} [CommRing A] [CommRing D] [CommRing W] {n : Type} [Fintype n]
    [DecidableEq n] (i : A →+* D) (hi : Function.Injective i) (j : A →+* W) (t t' : A) (N l k : ℕ)
    (M Y y : Matrix n n A) (ε : Matrix n n D) (h : i t ^ N • M.map i = i t' ^ N • (Y.map i * ε))
    (hy : y.map i = (l : D) ^ k • ε) (ht : IsUnit (j t')) (hY : IsUnit (Y.map j)) (a b : n) :
    (l : W) ^ k ∣ j (y a b) := by
  have h1 : ((l : A) ^ k * t ^ N) • M = t' ^ N • (Y * y) := by
    apply Matrix.map_injective hi
    change (((l : A) ^ k * t ^ N) • M).map i = (t' ^ N • (Y * y)).map i
    have e1 : (((l : A) ^ k * t ^ N) • M).map i = (l : D) ^ k • (i t ^ N • M.map i) := by
      ext p q; simp [mul_assoc]
    have e2 : (t' ^ N • (Y * y)).map i = i t' ^ N • (Y.map i * y.map i) := by
      rw [← Matrix.map_mul]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    rw [e1, e2, h, hy, Matrix.mul_smul, smul_comm]
  have h2 : (l : W) ^ k • (j t ^ N • M.map j) = j t' ^ N • (Y.map j * y.map j) := by
    have e := congrArg (fun Z : Matrix n n A => Z.map j) h1
    rw [← Matrix.map_mul]
    ext p q
    have := congrFun (congrFun e p) q
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, mul_assoc]
      using this
  obtain ⟨u, hu⟩ := hY
  obtain ⟨v, hv⟩ := ht.pow N
  have h3 : y.map j = (l : W) ^ k • ((↑v⁻¹ : W) • ((↑u⁻¹ : Matrix n n W) * (j t ^ N • M.map j))) := by
    rw [smul_comm, ← Matrix.mul_smul, h2, ← hu, ← hv, Matrix.mul_smul, ← mul_assoc, Units.inv_mul, one_mul,
      smul_smul, Units.inv_mul, one_smul]
  exact ⟨_, congrFun (congrFun h3 a) b⟩

theorem pow_dvd_of_rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → ∀ (k : ℕ) (y : Matrix (Fin d) (Fin d) (Ainf l)), y.map bk.iA = ((l : ℕ) : bk.DA bk.ρ₀) ^ k • ε → ∀ i j, ((l : ℕ) : Ainf l) ^ k ∣ y i j := by
  intro l _ K bk d ρ τ s ht hτ _ g ε hε k y hy i j
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨-, hu, hsat⟩ := GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ
  exact hsat k _ (pow_dvd_map_of_smul_eq bk.iA (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1 (inclW l) τ _ s.N l k
    _ ht.Y y ε (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g ε hε) hy (hu g) ht.unit i j)

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdGaloisComparisonMatrixStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.pow_dvd_galoisComparison_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → ∀ (k : ℕ) (y : Matrix (Fin d) (Fin d) (Ainf l)), y.map bk.iA = ((l : ℕ) : bk.DA bk.ρ₀) ^ k • ε → ∀ i j, ((l : ℕ) : Ainf l) ^ k ∣ y i j := by
  first | exact @GlobalTheory.BSP.pow_dvd_of_rel_gal | exact GlobalTheory.BSP.pow_dvd_of_rel_gal | (intros; apply GlobalTheory.BSP.pow_dvd_of_rel_gal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDisc

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem comparisonMatrix_bounded : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  intro l _ K bk d ρ τ s ht hper B f g ι tb ε hrel
  have hnorm := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f g
  let Φ : Disc l (BK.hf f X) bk.ρ₀ →+* Disc l (BK.hf f X) bk.ρ₀ := Disc.map B.D.φ hnorm.2
  have hΦ : IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ := isDiscMap_map _ _
  have hreg := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f) ι tb
  have hpair := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  have heq := GlobalTheory.T.comparisonMatrix_frobenius_disc l K bk d ρ τ s ht hper B f hreg.2.1 f g ε hrel Φ hΦ
  have hQ : ht.A.map (BK.hf g) * ht.A'.map (BK.hf g) =
      BK.hf g bk.E ^ ht.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
    rw [← Matrix.map_mul (f := BK.hf g), ht.A_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  obtain ⟨h, c, hc⟩ := GlobalTheory.T.matrix_phi_equation_to_family_equation B.A (Disc l (BK.hf f X) bk.ρ₀) (toDisc l (BK.hf f X) bk.ρ₀) Φ
    (BK.hf f bk.E) (BK.hf g bk.E) hpair.2.1 d d (ht.a + s.N) (ht.a + s.N) ht.b (ht.A.map (BK.hf f))
    (ht.A.map (BK.hf g)) (ht.A'.map (BK.hf g)) hQ ε heq
  have hφX : B.D.φ (BK.hf f X) = BK.hf f X ^ l := by
    have h1 : B.D.φ (f.f X) = f.f (bk.prism.D.φ X) := (f.f_φ X).symm
    have h2 : bk.prism.D.φ X = X ^ l := frobS_X l bk.a
    exact h1.trans ((congrArg f.f h2).trans (map_pow f.f _ l))
  have key := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk B.A (BK.hf f) ι tb B.D.φ hφX Φ hΦ (Fin d × Fin d) c
    (fun _ _ => Set.toFinite _) h (fun j => ε j.1 j.2)
  have htend : Filter.Tendsto (fun j : Fin d × Fin d => ε j.1 j.2) Filter.cofinite
      (nhds (0 : Disc l (BK.hf f X) bk.ρ₀)) := by
    simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  have hsum : ∀ j : Fin d × Fin d, HasSum (fun i => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
      (toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2) := fun j => by
    have hs := hasSum_fintype (fun i : Fin d × Fin d => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
    have e : toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2 =
        ∑ k : Fin d × Fin d, Φ (ε k.1 k.2) * toDisc l (BK.hf f X) bk.ρ₀ (c k j) := hc j
    convert hs using 1
  have k2 := key htend hsum
  obtain ⟨k, v, hv, -⟩ := k2
  refine ⟨k, Matrix.of fun i j => v (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact hv (i, j)

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDiscStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prism_comparisonMatrix_pow_smul_bounded_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  first | exact @GlobalTheory.BSP.comparisonMatrix_bounded | exact GlobalTheory.BSP.comparisonMatrix_bounded | (intros; apply GlobalTheory.BSP.comparisonMatrix_bounded <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproduct

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem map_toDisc_eq_of_dvd {l : ℕ} {A : Type} [CommRing A] (u : A) (r : ℝ≥0) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε)
    (h : ∀ j : n × n, ((l : ℕ) : A) ^ k ∣ x j.1 j.2) : ∃ y : Matrix n n A, y.map (toDisc l u r) = ε := by
  choose y hy using h
  refine ⟨Matrix.of fun i j => y (i, j), ?_⟩
  ext i j
  have e := congrFun (congrFun hx i) j
  have e2 : x i j = _ := hy (i, j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, e2, map_mul, map_pow, map_natCast] at e
  exact ((isUnit_l_disc l _ _).pow k).mul_left_cancel e

theorem IsDiscMap.map_eq_smul {l : ℕ} {A A' : Type} [CommRing A] [CommRing A'] {u : A} {u' : A'} {r r' : ℝ≥0}
    {f : A →+* A'} {F : Disc l u r →+* Disc l u' r'} (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε) :
    (x.map f).map (toDisc l u' r') = ((l : ℕ) : Disc l u' r') ^ k • ε.map F := by
  ext i j
  have e := congrArg F (congrFun (congrFun hx i) j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast] at e ⊢
  rw [← e, hF.ext]

theorem map_mul_map_eq_smul_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (A A' : Matrix (Fin d) (Fin d) R) (e : R) (b : ℕ) (h : A * A' = e ^ b • (1 : Matrix (Fin d) (Fin d) R)) :
    A.map f * A'.map f = f e ^ b • (1 : Matrix (Fin d) (Fin d) S) := by
  rw [← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]

theorem Height.dvd_at_section (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (B : Obj l ↥(OL K)) (f f' : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)) (hε : ht.Rel (BK.hf f X) f f' ε) (k : ℕ)
    (x : Matrix (Fin d) (Fin d) B.A)
    (hx : x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε)
    (g : ↥(GK K)) (σ : Hom B (ainfObj K)) (h1 : σ.comp f = bk.ι) (h2 : σ.comp f' = (ainfHom K g).comp bk.ι)
    (j : Fin d × Fin d) : ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j.1 j.2) := by
  obtain ⟨⟨F, hF⟩, hrel⟩ := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht B (ainfObj K) f f f' bk.ι σ ε hε
  have hr := hrel F hF
  rw [h1, h2] at hr
  exact GlobalTheory.T.pow_dvd_galoisComparison_matrix l K bk d ρ τ s ht hτ hρ g (ε.map F) hr k (x.map σ.f) (hF.map_eq_smul k x ε hx) j.1 j.2

theorem matrix_phi_eq_entries {R : Type} [CommRing R] (φ : R →+* R) (e e' : R) (he : Associated e e') (d a b : ℕ)
    (P Q Q' : Matrix (Fin d) (Fin d) R) (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R))
    (x : Matrix (Fin d) (Fin d) R) (hx : e' ^ a • (P * x.map φ) = e ^ a • (x * Q)) :
    ∃ (h : ℕ) (c : Fin d × Fin d → Fin d × Fin d → R),
      ∀ j : Fin d × Fin d, e ^ h * x j.1 j.2 = ∑ i : Fin d × Fin d, φ (x i.1 i.2) * c i j :=
  GlobalTheory.T.matrix_phi_equation_to_family_equation R R (RingHom.id R) φ e e' he d d a a b P Q Q' hQ x hx

theorem Height.exists_rel_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) :
    ∃ ε : Matrix (Fin d) (Fin d) En.Q.A,
      ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  have tb : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have h₁ := GlobalTheory.T.comparisonMatrix_exists_on_disc l K bk d ρ τ s ht En.Q (BK.hf En.inl X) En.inl En.inr
  obtain ⟨εD, hεD⟩ := h₁
  have h₂ := GlobalTheory.T.prism_comparisonMatrix_pow_smul_bounded_on_disc l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb εD hεD
  obtain ⟨k, x, hx⟩ := h₂
  have hφ := GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb k x εD hεD hx
  have h₃ := matrix_phi_eq_entries En.Q.D.φ (BK.hf En.inl bk.E) (BK.hf En.inr bk.E)
    (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk En.Q En.inl En.inr).2.1 d (ht.a + s.N) ht.b (ht.A.map (BK.hf En.inl))
    (ht.A.map (BK.hf En.inr)) (ht.A'.map (BK.hf En.inr))
    (map_mul_map_eq_smul_one (BK.hf En.inr) _ _ _ _ ht.A_mul) x hφ
  obtain ⟨h, c, hc⟩ := h₃
  have hdiv := GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd l K bk En (Fin d × Fin d) c h k (fun j => x j.1 j.2) hc
    (Height.dvd_at_section l K bk d ρ τ s ht hτ hρ En.Q En.inl En.inr εD hεD k x hx)
  have h₄ := map_toDisc_eq_of_dvd (BK.hf En.inl X) bk.ρ₀ k x εD hx hdiv
  obtain ⟨y, hy⟩ := h₄
  subst hy
  exact ⟨y, hεD⟩

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproductStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_comparison_matrix_prismCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)), ∃ ε : Matrix (Fin d) (Fin d) En.Q.A, ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  first | exact @GlobalTheory.BSP.Height.exists_rel_env | exact GlobalTheory.BSP.Height.exists_rel_env | (intros; apply GlobalTheory.BSP.Height.exists_rel_env <;> assumption)
end
end
