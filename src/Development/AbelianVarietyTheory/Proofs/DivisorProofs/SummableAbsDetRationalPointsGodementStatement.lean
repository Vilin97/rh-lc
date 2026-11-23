module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SummableOfCount
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRationalPointsFixerTorusClassesLeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZeroStatement
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinityStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBoundDiagonalExponentsRationalPoint

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem exists_bound_exponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set P : Matrix (Fin j) (Fin n) (AF F ⊗[F] E) := adMat F (cT (σ : E →+* E) C * J) with hP
  have hq : ∀ q ∈ fixG σ J C, P * (matHom _ σ J q).1 = P := by
    intro q hq
    have h1 : (matHom _ σ J q⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact inv_mem hq
    have h := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h
  have hl : ∀ α, P * (matHom _ σ J (lv α)).1 = cT (sigR (AF F) σ) (α⁻¹).1 * P := by
    intro α
    have h := form_mul_of_mul_cols (hlv.onC α⁻¹)
    rwa [map_inv lv α, inv_inv] at h
  have hc : Continuous fun w : GAd σ J => P * (matHom _ σ J w).1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous)
  have hb : GlobalTheory.Eis.Conv.Bdd fun w : W => (w : GAd σ J) := ⟨W, hW, fun w => w.2⟩
  obtain ⟨Ω, hΩ, hΩw⟩ := GlobalTheory.Eis.Conv.Bdd.entries (GlobalTheory.Eis.Conv.Bdd.map hb hc)
  obtain ⟨m₀, hm₀⟩ := (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero F E Ω hΩ).2
  refine ⟨m₀, fun q hqm l w hw hg i => ?_⟩
  have ht : cT (sigR (AF F) σ) (tor F E l)⁻¹.1 = (tor F E l)⁻¹.1 :=
    congrArg Units.val (GlobalTheory.Eis.Conv.cti_dg (GlobalTheory.Eis.Conv.sigR_halfE σ) l)
  have h1 : P * (matHom _ σ J (q * lv (tor F E l) * w)).1 = (tor F E l)⁻¹.1 * (P * (matHom _ σ J w).1) := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq q hqm, hl, ht,
      Matrix.mul_assoc]
  generalize q * lv (tor F E l) * w = g at hg h1
  have hg' : matHom _ σ J g ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.1 hg
  obtain ⟨γ, -, e⟩ := Subgroup.mem_map.1 hg'
  have hm : (matHom _ σ J g).1 = γ.1.map (inclR (F := F) (AF F)) := by
    rw [← e]; rfl
  have hy : (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) = P * (matHom _ σ J g).1 := by
    rw [hm, Matrix.map_mul]
  have hrow : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1) i x = 0 :=
    GlobalTheory.GodementSectionReduction.row_ne_zero (N := γ⁻¹.1 * D) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ.1, Units.mul_inv, Matrix.one_mul, hF.cd]) i
  have hrow' : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) i x = 0 := fun h =>
    hrow fun x => by
      have := h x
      rwa [Matrix.map_apply, map_eq_zero_iff _ GlobalTheory.AutFunCompare.inclA_injective] at this
  exact GlobalTheory.GodementSectionReduction.bound_aux (inclR (F := F) (AF F)) hm₀ (fun i x => hΩw ⟨w, hw⟩ i x) (hy.trans h1) i hrow'

end GlobalTheory.SphEis

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBoundDiagonalExponentsRationalPointStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.exists_lowerBound_diagonalExponents_rationalPoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  first | exact @GlobalTheory.SphEis.exists_bound_exponents | exact GlobalTheory.SphEis.exists_bound_exponents | (intros; apply GlobalTheory.SphEis.exists_bound_exponents <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionLeviGLIsotropicFrame

section

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem reduce_gl_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) (j : ℕ) : ∃ (L : Set (GL (Fin j) (AF F ⊗[F] E))) (B : ℝ), IsCompact L ∧
    ∀ α : GL (Fin j) (AF F ⊗[F] E), ∃ (δ : GL (Fin j) E) (l : Fin j → ℤ), ∃ c ∈ L,
      bc (inclR (F := F) (AF F)) δ * α = tor F E l * c ∧
      (absE F E (Matrix.GeneralLinearGroup.det α) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ :=
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := F)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  GlobalTheory.GodementSectionReduction.reduction_GL_diagonalUnitPowers_compact (inclR (F := F) (AF F)) GlobalTheory.Doubling.continuous_absE
    (fun u => GlobalTheory.Doubling.absE_inclR u) (by positivity)
    (by rw [GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity _ _ _ hc]; simp) (GlobalTheory.Eis.Conv.red_gl _ _ _ hc j)

theorem reduce_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hl
  obtain ⟨L, B, hL, hR⟩ := reduce_gl_cm hF.cm j
  refine ⟨lv '' L, B, hL.image hl.cont, fun p β hp => ?_⟩
  obtain ⟨δ, l, c, hc, hred, hle⟩ := hR β
  have h1 := hl.rat δ
  generalize bc (inclR (F := F) (AF F)) δ = u at h1 hred
  refine ⟨lv u, h1, ⟨⟨u.1, fun _ _ h => absurd h (lt_irrefl _), hl.onC u⟩,
    (u⁻¹).1, fun _ _ h => absurd h (lt_irrefl _), by rw [← map_inv]; exact hl.onC u⁻¹⟩,
    lv u * p * lv (u * β)⁻¹, ?_, l, lv c, ⟨c, hc, rfl⟩, ?_, hle⟩
  · change _ * _ = _
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hl.onC, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ (adMat F C), hp, ← Matrix.mul_assoc, hl.onC, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc u.1, ← Units.val_mul, Units.mul_inv, Matrix.mul_one]
  · rw [mul_assoc _ (lv _) (lv c), ← map_mul, ← hred, map_inv, inv_mul_cancel_right]

end GlobalTheory.SphEis

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionLeviGLIsotropicFrameStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.reduction_leviGL_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  first | exact @GlobalTheory.SphEis.reduce_levi | exact GlobalTheory.SphEis.reduce_levi | (intros; apply GlobalTheory.SphEis.reduce_levi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

noncomputable section

namespace GlobalTheory.SphEis.Summ

theorem tor_add (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {j : ℕ}
    (μ : Fin j → ℕ) (m₀ : ℕ) :
    tor F E (fun i => (μ i : ℤ) + -(m₀ : ℤ)) = tor F E (fun i => (μ i : ℤ)) * tor F E (fun _ => -(m₀ : ℤ)) :=
  Units.ext (by
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => congrArg Units.val (_root_.zpow_add _ _ _)))

theorem summable_absDet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv ι x p k β K hK hx e hk hβ hi t ht
  classical
  have hb : 1 < bse F := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero
  have hb0 : 0 < bse F := one_pos.trans hb
  have hfp : fixG σ J C ≤ parFlag σ J C (fun _ => 0) := fun g hg =>
    ⟨⟨1, Matrix.blockTriangular_one, by rw [Matrix.mul_one]; exact hg⟩, 1, Matrix.blockTriangular_one, by
      rw [Matrix.mul_one]; exact inv_mem hg⟩
  obtain ⟨W, B, hW, hR⟩ := GlobalTheory.T.reduction_leviGL_isotropicFrame F E σ n J j m C D Z J₀ hF lv hlv
  choose γ hγ hγP q hq l w hw hred hle using fun i => hR (p i) (β i) (hβ i)
  have hWK : IsCompact (W * K) := hW.mul hK
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.exists_lowerBound_diagonalExponents_rationalPoint F E σ n J j m C D Z J₀ hF lv hlv (W * K) hWK
  have hl : ∀ i r, -(m₀ : ℤ) ≤ l i r := fun i =>
    hm₀ (q i) (hq i) (l i) (w i * k i) (Set.mul_mem_mul (hw i) (hk i)) (by
      have := mul_mem (hγ i) (hx i)
      rwa [e, ← mul_assoc, hred, mul_assoc _ (w i)] at this)
  obtain ⟨μ, hμ⟩ : ∃ μ : ι → Fin j → ℕ, ∀ i, l i = fun r => (μ i r : ℤ) + -(m₀ : ℤ) :=
    ⟨fun i r => (l i r + m₀).toNat, fun i => funext fun r => by have := hl i r; beta_reduce; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, a = lv (tor F E fun _ => -(m₀ : ℤ)) := ⟨_, rfl⟩
  have hW' : IsCompact ((fun g => a * g) '' (W * K)) := hWK.image (continuous_const_mul a)
  obtain ⟨N, hN⟩ := GlobalTheory.T.card_rationalPoints_fixer_torusClasses_le F E σ n J j m C D Z J₀ hF lv hlv _ hW'
  have hz : ∀ i, γ i * x i = q i * lv (tor F E fun r => (μ i r : ℤ)) * (a * (w i * k i)) := fun i => by
    rw [e, ← mul_assoc, hred, hμ, tor_add, map_mul, ← ha]
    simp only [mul_assoc]
  have hinj : ∀ i i', γ i' * x i' * (γ i * x i)⁻¹ ∈ fixG σ J C → i = i' := fun i i' h => hi i i' (by
    have h2 : x i' * (x i)⁻¹ = (γ i')⁻¹ * (γ i' * x i' * (γ i * x i)⁻¹) * γ i := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem (hγP i')) (hfp h)) (hγP i))
  refine GlobalTheory.GodementSectionReduction.summable_of_count ι j (m + j) (bse F) (max (B * bse F ^ (m₀ * j)) N) t μ _ hb ht
    (fun i => ⟨NNReal.coe_nonneg _, ?_⟩) fun μ' S hS => ?_
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine (hle i).trans (le_of_eq ?_)
    rw [mul_assoc, hμ]
    simp only [zpow_add₀ hb0.ne', _root_.zpow_neg, zpow_natCast, mul_inv, inv_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [mul_comm (∏ _, _)]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have hc : (S.image fun i => γ i * x i).card = S.card :=
      Finset.card_image_of_injOn fun i _ i' _ h => hinj i i' (by
        rw [← h, mul_inv_cancel]
        exact one_mem _)
    rw [← hc]
    refine hN μ' _ ?_ ?_ ?_
    · intro s hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      exact mul_mem (hγ i) (hx i)
    · intro s hs s' hs' h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hs'
      rw [hinj i i' h]
    · intro s hs
      obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hs
      exact ⟨q i, hq i, a * (w i * k i), ⟨w i * k i, Set.mul_mem_mul (hw i) (hk i), rfl⟩, by rw [hz, hS i hi']⟩

end GlobalTheory.SphEis.Summ

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodementStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.summable_absDet_rational_points_godement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  first | exact @GlobalTheory.SphEis.Summ.summable_absDet | exact GlobalTheory.SphEis.Summ.summable_absDet | (intros; apply GlobalTheory.SphEis.Summ.summable_absDet <;> assumption)
end
end
