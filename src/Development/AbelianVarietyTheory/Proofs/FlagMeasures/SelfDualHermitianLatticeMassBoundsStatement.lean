module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentBiUnion
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizer
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMatrixCongruenceContentJacobianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesHermitianGramCosetContent
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometryStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteClasses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassEqConstMulContent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThickOrbitSelfDualUnramifiedLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupOrthogonalComplementUnimodular
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesHermitianGramCosetContentStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.primitiveTuples_hermitianGram_coset_content : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ m : ℕ, 2 * m + 3 ≤ n → ∀ B : Set (Matrix (Fin m) (Fin m) E), (∀ X ∈ B, X ∈ hermLat L m) → IsCO (hermLat L m) B → IsCO (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (hermLat L m) B ≤ 2 * cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ≤ 2 * cont (hermLat L m) B := by
  first | exact @GlobalTheory.HL.PrimVol.cont_primitive_tuples | exact GlobalTheory.HL.PrimVol.cont_primitive_tuples | (intros; apply GlobalTheory.HL.PrimVol.cont_primitive_tuples <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjInt

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.PrimScale

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sum_left (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm (∑ i, c i • x i) y = ∑ i, c i * hf L Hm (x i) y := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem hf_cj (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by

  simp only [hf, map_sum, map_mul, L.cj_cj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : L.cj (Hm b a) = Hm a b := congrFun (congrFun h a) b
  rw [this]; ring

theorem gramT_rmul (L : LocE F E) {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  have h1 : ∀ y, hf L Hm y (∑ i, A i a • x i) = ∑ i, L.cj (A i a) * hf L Hm y (x i) := by
    intro y
    rw [← hf_cj L h, hf_sum_left]

    simp only [map_sum, map_mul, hf_cj L h]
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_left, h1, Matrix.mul_apply, cT]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem isHerm_gramT (L : LocE F E) {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x : Fin m → Fin n → E) : IsHerm L (gramT L Hm x) := by
  ext a b
  exact hf_cj L h _ _

theorem cT_mul (L : LocE F E) {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext a b

  simp only [cT, Matrix.mul_apply, map_sum, map_mul, mul_comm]

theorem cT_one (L : LocE F E) {m : ℕ} : cT L (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  ext a b
  simp only [cT, Matrix.one_apply, eq_comm (a := b)]
  split_ifs <;> simp

theorem rmul_rmul {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]

theorem rmul_one {n m : ℕ} (x : Fin m → Fin n → E) : rmul x 1 = x := by
  funext j
  simp [rmul, Matrix.one_apply]

theorem isIntM_mul (L : LocE F E) {m : ℕ} {A B : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A)
    (hB : IsIntM L B) : IsIntM L (A * B) := fun a b => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hA a i) (hB i b)

variable [IsNonarchimedeanLocalField F]

theorem exists_pow_mul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (e : E) :
    ∃ k : ℕ, ∀ i ≥ k, algebraMap F E ((ϖ : F) ^ i) * e ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  have he : IsIntegral F e := Algebra.IsIntegral.isIntegral e
  obtain ⟨⟨c, hc⟩, hce⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors 𝒪[F]) e he
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hc) hϖ
  refine ⟨k, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [L.O_def]
  have h1 : IsIntegral 𝒪[F] (((u⁻¹ : (𝒪[F])ˣ) * ϖ ^ j : 𝒪[F]) • (((u : 𝒪[F]) * ϖ ^ k) • e)) :=
    IsIntegral.smul _ hce
  have h2 : ((u⁻¹ : (𝒪[F])ˣ) * ϖ ^ j : 𝒪[F]) * ((u : 𝒪[F]) * ϖ ^ k) = ϖ ^ (k + j) := by
    rw [pow_add]
    linear_combination (ϖ ^ j * ϖ ^ k) * u.inv_mul
  rw [smul_smul, h2, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E] at h1
  exact h1

theorem exists_conj_int (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) E) (hA : IsUnit A.det) :
    ∃ k : ℕ, ∀ i ≥ k, ∀ K ∈ congK L ϖ m i, IsIntM L (A * K * A⁻¹) := by
  choose k hk using fun p : Fin m × Fin m × Fin m × Fin m =>
    exists_pow_mul_mem L hϖ (A p.1 p.2.1 * A⁻¹ p.2.2.1 p.2.2.2)
  refine ⟨Finset.univ.sup k, fun i hi K hK a b => ?_⟩
  have h1 : A * K * A⁻¹ = 1 + A * (K - 1) * A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hA]; abel
  rw [h1, Matrix.add_apply]
  refine Subring.add_mem _ ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun s _ => Subring.sum_mem _ fun r _ => ?_
    obtain ⟨c, hc, h⟩ := hK r s
    rw [Matrix.sub_apply, h]
    have := Subring.mul_mem _ (hk (a, r, s, b) i
      (le_trans (Finset.le_sup (Finset.mem_univ _)) hi)) hc
    convert this using 1
    ring

theorem cont_prim_scale : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → 2 * m + 3 ≤ n → ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → IsIntM L (gramT L Hm (rmul x A⁻¹)) → ∃ i0 : ℕ, ∀ i ≥ i0, (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m))) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) ≤ 2 * cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs (rmul z A⁻¹) ∧ gramT L Hm z ∈ horb L ϖ (gramT L Hm x) i} ∧ cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs (rmul z A⁻¹) ∧ gramT L Hm z ∈ horb L ϖ (gramT L Hm x) i} ≤ 2 * ((resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m))) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) i)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛ m x hx hmn A hA hint
  obtain ⟨k, hk⟩ := exists_conj_int L hϖ A hA
  refine ⟨max k 1, fun i hi => ?_⟩
  have hO := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hq : (0 : ℝ) < resQ ϖ := by
    have := hO.2.2.2.2.2.2.1
    exact_mod_cast (by omega : 0 < resQ ϖ)
  have hAi : IsUnit (A⁻¹).det := Matrix.isUnit_nonsing_inv_det A hA
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  have hcA : cT L A * cT L A⁻¹ = 1 := by rw [← cT_mul, hAA', cT_one]
  have hcA' : cT L A⁻¹ * cT L A = 1 := by rw [← cT_mul, hAA, cT_one]
  have hΓ := isHerm_gramT L hH.1 x
  set O := horb L ϖ (gramT L Hm x) i with hOdef
  have hOco : IsCO (hermLat L m) O :=
    ((GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i (le_of_max_le_right hi)).2.2 _ hΓ hx).1
  set B := (fun X => cT L A⁻¹ * X * A⁻¹) '' O with hBdef
  have hBco : IsCO (hermLat L m) B := ((GlobalTheory.T.hermitianMatrix_congruence_content_jacobian L ϖ hϖ m A⁻¹ hAi).2 O hOco).1
  have hback : ∀ X : Matrix (Fin m) (Fin m) E, cT L A * (cT L A⁻¹ * X * A⁻¹) * A = X := by
    intro X
    calc _ = (cT L A * cT L A⁻¹) * X * (A⁻¹ * A) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hcA, hAA', Matrix.one_mul, Matrix.mul_one]
  have hforth : ∀ X : Matrix (Fin m) (Fin m) E, cT L A⁻¹ * (cT L A * X * A) * A⁻¹ = X := by
    intro X
    calc _ = (cT L A⁻¹ * cT L A) * X * (A * A⁻¹) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hcA', hAA, Matrix.one_mul, Matrix.mul_one]
  have hOB : (fun X => cT L A * X * A) '' B = O := by
    rw [hBdef, Set.image_image]
    simp only [hback, Set.image_id']
  have hcO := ((GlobalTheory.T.hermitianMatrix_congruence_content_jacobian L ϖ hϖ m A hA).2 B hBco).2
  rw [hOB] at hcO
  have hBint : ∀ X ∈ B, X ∈ hermLat L m := by
    rintro _ ⟨_, ⟨K, hK, rfl⟩, rfl⟩
    have hK' := hk i (le_of_max_le_left hi) K hK
    have h1 : cT L A⁻¹ * (cT L K * gramT L Hm x * K) * A⁻¹
        = cT L (A * K * A⁻¹) * gramT L Hm (rmul x A⁻¹) * (A * K * A⁻¹) := by
      rw [gramT_rmul L hH.1, cT_mul, cT_mul]
      conv_lhs => rw [← hback (gramT L Hm x)]
      simp only [Matrix.mul_assoc]
    refine AddSubgroup.subset_closure ⟨?_, ?_⟩
    · change IsHerm L (cT L A⁻¹ * (cT L K * gramT L Hm x * K) * A⁻¹)
      rw [← gramT_rmul L hH.1, ← gramT_rmul L hH.1]
      exact isHerm_gramT L hH.1 _
    · change IsIntM L (cT L A⁻¹ * (cT L K * gramT L Hm x * K) * A⁻¹)
      rw [h1]
      exact isIntM_mul L (isIntM_mul L (fun a b => (hO.2.1 _ (hK' b a)).1) hint) hK'
  obtain ⟨hTco, hT1, hT2⟩ := GlobalTheory.T.primitiveTuples_hermitianGram_coset_content L ϖ hϖ Hm hH Λs hΛ m hmn B hBint hBco
  have hS : {z : Fin m → Fin n → E | IsPrimT L Hm Λs (rmul z A⁻¹) ∧ gramT L Hm z ∈ O}
      = (fun x => rmul x A) ''
        {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨rmul z A⁻¹, ⟨h1, _, h2, (gramT_rmul L hH.1 _ _).symm⟩, ?_⟩
      simp only [rmul_rmul, hAA', rmul_one]
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      refine ⟨by simpa only [rmul_rmul, hAA, rmul_one] using h1, ?_⟩
      rw [← hOB]
      exact ⟨_, h2, (gramT_rmul L hH.1 _ _).symm⟩
  have hcS := ((GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λs hΛ m).1 A hA _ hTco).2
  rw [hS, hcS, hcO, ← mul_assoc, ← zpow_add₀ hq.ne']
  have he : -(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)) + -(vE L ϖ (A.det * L.cj A.det) * m)
      = -(vE L ϖ (A.det * L.cj A.det) * n) := by ring
  rw [he]
  have hp := (zpow_pos hq (-(vE L ϖ (A.det * L.cj A.det) * n))).le
  constructor
  · have := mul_le_mul_of_nonneg_left hT1 hp
    linarith
  · have := mul_le_mul_of_nonneg_left hT2 hp
    linarith

end GlobalTheory.PrimScale
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassBounds

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Unfold

open GlobalTheory.HL.TracePart

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem smul_inf_eq {Y : Submodule E (Fin n → E)} {h : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hh : h ∈ fixG L Hm Y) (Λ : Submodule L.O (Fin n → E)) :
    (h • Λ) ⊓ Y.restrictScalars L.O = Λ ⊓ Y.restrictScalars L.O := by
  have hi := ((fixG L Hm Y).inv_mem hh).2.2
  ext v
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]
  refine and_congr_left fun hv => ?_
  have := hi v hv
  rw [Submodule.mem_bot, sub_eq_zero] at this
  rw [this]

theorem image_thick (ϖ : 𝒪[F]) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ isomG L Hm)
    (Λ : Submodule L.O (Fin n → E)) (x : Fin m → Fin n → E) (i : ℕ) :
    (fun x a => g (x a)) '' thick L ϖ (torb (isomG L Hm ⊓ stabL L Λ) fun a => g⁻¹ (x a)) i =
      thick L ϖ (torb (isomG L Hm ⊓ stabL L (g • Λ)) x) i := by
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩
    refine ⟨_, ⟨g * k * g⁻¹, ⟨?_, ?_⟩, rfl⟩, A, hA, ?_⟩
    · exact (isomG L Hm).mul_mem ((isomG L Hm).mul_mem hg hk.1) ((isomG L Hm).inv_mem hg)
    · have h2 : k • Λ = Λ := hk.2
      show (g * k * g⁻¹) • g • Λ = g • Λ
      rw [mul_smul, mul_smul, inv_smul_smul, h2]
    · exact map_rmul g _ A
  · rintro ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩
    refine ⟨_, ⟨_, ⟨g⁻¹ * k * g, ⟨?_, ?_⟩, rfl⟩, A, hA, rfl⟩, ?_⟩
    · exact (isomG L Hm).mul_mem ((isomG L Hm).mul_mem ((isomG L Hm).inv_mem hg) hk.1) hg
    · have h2 : k • g • Λ = g • Λ := hk.2
      show (g⁻¹ * k * g) • Λ = Λ
      rw [mul_smul, mul_smul, h2, inv_smul_smul]
    · refine (map_rmul g _ A).trans ?_
      congr 1
      funext a
      have e1 : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
      show g (g⁻¹ (k (g (g⁻¹ (x a))))) = k (x a)
      rw [e1, e1]

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem sigMass_eq_sum (hH : IsHermND L Hm) {Λs : Submodule L.O (Fin n → E)} (hs : IsSD L Hm Λs)
    (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det) {Λ0 : Submodule L.O (Fin n → E)}
    (h0 : IsLat L Λ0) (Mh : Submodule L.O (Fin n → E))
    (s : Finset ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    (h1 : ∀ g ∈ s, g ∈ isomG L Hm ∧
      (g • Λs) ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Mh)
    (h2 : ∀ Λ, IsSD L Hm Λ → Λ ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Mh →
      ∃! g, g ∈ s ∧ ∃ h ∈ fixG L Hm (Submodule.span E (Set.range x)), Λ = h • g • Λs) :
    sigMass L Hm (Submodule.span E (Set.range x)) Λ0 Mh =
      ENNReal.ofReal (∑ g ∈ s, invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0)
        (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (g • Λs))) := by
  set Y := Submodule.span E (Set.range x) with hY
  let φ : ((Fin n → E) ≃ₗ[E] (Fin n → E)) →
      MulAction.orbitRel.Quotient (fixG L Hm Y) (Submodule L.O (Fin n → E)) :=
    fun g => Quotient.mk _ (g • Λs)
  have hout : ∀ g, ∃ h ∈ fixG L Hm Y, (φ g).out = h • g • Λs := by
    intro g
    have : (MulAction.orbitRel (fixG L Hm Y) (Submodule L.O (Fin n → E))) (φ g).out (g • Λs) :=
      Quotient.mk_out (s := MulAction.orbitRel (fixG L Hm Y) (Submodule L.O (Fin n → E))) (g • Λs)
    obtain ⟨h, hh⟩ := MulAction.orbitRel_apply.1 this
    exact ⟨h.1, h.2, hh.symm⟩
  have hinj : ∀ g ∈ s, ∀ g' ∈ s, φ g = φ g' → g = g' := by
    intro g hg g' hg' e
    obtain ⟨h, hh, e1⟩ := hout g
    obtain ⟨h', hh', e2⟩ := hout g'
    have hsd : IsSD L Hm (φ g).out := by
      rw [e1]; exact isSD_smul hh.1 (isSD_smul (h1 g hg).1 hs)
    have htr : (φ g).out ⊓ Y.restrictScalars L.O = Mh := by
      rw [e1, smul_inf_eq hh, (h1 g hg).2]
    exact (h2 _ hsd htr).unique ⟨hg, h, hh, e1⟩ ⟨hg', h', hh', e ▸ e2⟩
  rw [ENNReal.ofReal_sum_of_nonneg (fun g _ => by unfold invVol; positivity)]
  unfold sigMass
  rw [tsum_eq_sum (s := s.image φ), Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun g hg => ?_
    obtain ⟨h, hh, e1⟩ := hout g
    have hsd := isSD_smul (h1 g hg).1 hs
    rw [e1, if_pos ⟨isSD_smul hh.1 hsd, by rw [smul_inf_eq hh, (h1 g hg).2]⟩,
      GlobalTheory.HL.Unimod.unimodular L Hm hH m x hx Λ0 _ h0 hsd.1 h hh]
  · intro o ho
    rw [if_neg]
    rintro ⟨hsd, htr⟩
    obtain ⟨g, ⟨hg, h, hh, e⟩, -⟩ := h2 _ hsd htr
    refine ho (Finset.mem_image.2 ⟨g, hg, ?_⟩)
    rw [← Quotient.out_eq o]
    refine (Quotient.sound ?_).symm
    exact MulAction.orbitRel_apply.2 ⟨⟨h, hh⟩, e.symm⟩

theorem mass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → 2 * m + 3 ≤ n → ∀ Λ0, IsLat L Λ0 → ∃ κ : ℝ, 0 < κ ∧ ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → IsIntM L (gramT L Hm (rmul x A⁻¹)) → ENNReal.ofReal (κ / 2 * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) ≤ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ∧ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ≤ ENNReal.ofReal (2 * κ * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hs m x hx hmn Λ0 h0
  obtain ⟨κ, hκ, hk⟩ := GlobalTheory.HL.QuotMass.mass_eq_const_mul_content L ϖ hϖ Hm hH Λs hs m x hx Λ0 h0
  refine ⟨κ, hκ, fun A hA hint => ?_⟩
  obtain ⟨s, h1, h2, i1, h3⟩ := trace_partition L ϖ hϖ Hm hH Λs hs m x hx A hA
  obtain ⟨i2, h4⟩ := GlobalTheory.PrimScale.cont_prim_scale L ϖ hϖ Hm hH Λs hs m x hx hmn A hA hint
  rw [sigMass_eq_sum hH hs x hx h0 _ s h1 h2]
  have hg : ∀ g, ∃ j : ℕ, g ∈ s → ∀ i ≥ j,
      IsCO (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) ∧
      invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0)
        (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (g • Λs)) *
        cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) = κ * cont (tupLat L Λs m)
          (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) := by
    intro g
    by_cases hgs : g ∈ s
    swap
    · exact ⟨0, fun h => absurd h hgs⟩
    have hgi := (h1 g hgs).1
    obtain ⟨j1, hj1⟩ := hk _ (isSD_smul hgi hs)
    obtain ⟨e, he⟩ := GlobalTheory.HL.QuotMass.exists_pow_smul L ϖ hϖ hs.1 (fun a => g⁻¹ (x a))
    obtain ⟨j2, -, hj2⟩ := GlobalTheory.ThickOrbit.main L ϖ hϖ Hm hH Λs hs Λs hs m _ hx 1 e
    refine ⟨max j1 j2, fun _ i hi => ?_⟩
    have hco := (hj2 i (le_of_max_le_right hi) (isomG L Hm ⊓ stabL L Λs) le_rfl
      (fun k hk hk' => ⟨hk, (GlobalTheory.HL.congruence_subgroup_facts L ϖ hϖ Λs hs.1 1).2.1 le_rfl k hk'⟩)
      (fun a => g⁻¹ (x a)) he (gramT_isom ((isomG L Hm).inv_mem hgi) x)).1
    refine ⟨hco, ?_⟩
    rw [hj1 i (le_of_max_le_left hi), ← image_thick ϖ hgi,
      ((GlobalTheory.HL.TupleJac.tuple_jacobian L ϖ hϖ Hm hH Λs hs m).2 g hgi _ hco).2]
  choose j hj using hg
  set i := max (max (max i1 i2) 1) (s.sup j) with hi
  have hij : ∀ g ∈ s, j g ≤ i := fun g hg => (Finset.le_sup hg).trans (le_max_right _ _)
  obtain ⟨hU, hD⟩ := h3 i (by omega)
  obtain ⟨hl, hu⟩ := h4 i (by omega)
  have hherm : IsHerm L (gramT L Hm x) := by
    funext a b
    exact (GlobalTheory.HL.Unimod.hf_swap L hH.1 _ _).symm
  have hpos := ((GlobalTheory.CongGrp.congK_group L ϖ hϖ m i (by omega)).2.2 _ hherm hx).2
  have hsum := (GlobalTheory.HL.cont_biUnion (tupLat L Λs m) s _
    (fun g hg => (hj g hg i (hij g hg)).1)).2 hD
  rw [hU, hsum] at hl hu
  have key := Finset.sum_congr rfl fun g (hg : g ∈ s) => (hj g hg i (hij g hg)).2
  rw [← Finset.sum_mul, ← Finset.mul_sum] at key
  constructor
  · refine ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right ?_ hpos)
    rw [key]
    have := mul_le_mul_of_nonneg_left hl hκ.le
    linarith
  · refine ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right ?_ hpos)
    rw [key]
    have := mul_le_mul_of_nonneg_left hu hκ.le
    linarith

end GlobalTheory.HL.Unfold
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassBoundsStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.selfDual_hermitianLattice_mass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → 2 * m + 3 ≤ n → ∀ Λ0, IsLat L Λ0 → ∃ κ : ℝ, 0 < κ ∧ ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → IsIntM L (gramT L Hm (rmul x A⁻¹)) → ENNReal.ofReal (κ / 2 * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) ≤ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ∧ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ≤ ENNReal.ofReal (2 * κ * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) := by
  first | exact @GlobalTheory.HL.Unfold.mass_bounds | exact GlobalTheory.HL.Unfold.mass_bounds | (intros; apply GlobalTheory.HL.Unfold.mass_bounds <;> assumption)
end
end
