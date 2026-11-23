module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TransferenceA
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MinkowskiDetBoundGramOfDetNeZero

section

@[expose] public section

open Matrix

namespace GlobalTheory

theorem minkowski_det_bound_gram_of_det_ne_zero (m : ℕ) (hm : 0 < m) (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.det ≠ 0)
    (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ (B * Bᵀ) *ᵥ (fun i => (z i : ℝ))) :
    a ^ m ≤ (m : ℝ) ^ m * (B * Bᵀ).det := by
  classical
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (Ne.isUnit hB)
  have hli : LinearIndependent ℝ B.row := Matrix.linearIndependent_rows_iff_isUnit.2 hu
  let b : Module.Basis (Fin m) ℝ (Fin m → ℝ) := basisOfPiSpaceOfLinearIndependent hli
  have hb : (b : Fin m → Fin m → ℝ) = B.row := coe_basisOfPiSpaceOfLinearIndependent hli
  have hpos : 0 < |B.det| := abs_pos.2 hB
  set t : ℝ := |B.det| ^ ((m : ℝ)⁻¹) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hpos _
  have htm : t ^ m = |B.det| := Real.rpow_inv_natCast_pow hpos.le hm.ne'
  obtain ⟨x, hx, hx0, hxt⟩ := ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_le hm b ht0 (by
    rw [htm, hb]; exact le_of_eq rfl)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hx0
  have hx' : ∑ i, c i • b i = (fun i => (c i : ℝ)) ᵥ* B := by
    ext j
    simp [hb, Matrix.vecMul, dotProduct, Finset.sum_apply]
  rw [hx'] at hxt
  have h1 := h c hc
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at h1
  set y := (fun i => (c i : ℝ)) ᵥ* B
  have h2 : y ⬝ᵥ y ≤ m * t ^ 2 := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin m)), y i * y i ≤ t ^ 2 := by
      intro i _
      have h3 : |y i| ≤ t := (norm_le_pi_norm y i).trans hxt
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have h4 := Finset.sum_le_sum this
    simpa [dotProduct] using h4
  calc a ^ m ≤ (m * t ^ 2) ^ m := pow_le_pow_left₀ ha (h1.trans h2) m
    _ = (m : ℝ) ^ m * (B * Bᵀ).det := by
      rw [mul_pow, ← pow_mul, mul_comm 2 m, pow_mul, htm, sq_abs, det_mul, det_transpose, sq]

theorem minkowski_det_bound_posDef (m : ℕ) (hm : 0 < m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosDef) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (z i : ℝ))) :
    a ^ m ≤ (m : ℝ) ^ m * G.det := by
  open MatrixOrder in
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hG.posSemidef.nonneg
  have hC' : G = Cᵀ * Cᵀᵀ := by
    rw [hC, transpose_transpose, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hd := hG.det_pos
  have hB : (Cᵀ).det ≠ 0 := by
    intro h0
    rw [hC', det_mul, h0, zero_mul] at hd
    exact lt_irrefl _ hd
  rw [hC'] at h ⊢
  exact minkowski_det_bound_gram_of_det_ne_zero m hm _ hB a ha h

theorem minkowski_det_bound_posSemidef :
    ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → ∀ a : ℝ, 0 ≤ a →
      (∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (z i : ℝ))) →
      a ^ m ≤ (m : ℝ) ^ m * G.det := by
  intro m G hG a ha h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have key : ∀ ε : ℝ, 0 < ε →
      a ^ m ≤ (m : ℝ) ^ m * (G + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det := by
    intro ε hε
    refine minkowski_det_bound_posDef m hm _
      (Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.one.smul hε)) a ha ?_
    intro z hz
    refine (h z hz).trans ?_
    rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul]
    have : 0 ≤ (fun i => (z i : ℝ)) ⬝ᵥ (fun i => (z i : ℝ)) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have := mul_nonneg hε.le this
    simpa using this
  have hc : Continuous fun ε : ℝ =>
      (m : ℝ) ^ m * (G + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det :=
    continuous_const.mul (Continuous.matrix_det (by fun_prop))
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  simpa using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefRealDetLeProdDiag

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory

theorem posSemidef_real_det_le_prod_diag :
    ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → G.det ≤ ∏ i, G i i :=
  fun _ _ hG => GlobalTheory.posSemidef_det_le_prod_diag hG

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefRealDetLeProdDiagStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.posSemidef_det_le_prod_diag' : ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → G.det ≤ ∏ i, G i i := by
  first | exact @GlobalTheory.posSemidef_real_det_le_prod_diag | exact GlobalTheory.posSemidef_real_det_le_prod_diag | (intros; apply GlobalTheory.posSemidef_real_det_le_prod_diag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSqMulPowLeProdBilinFormLatticeBasis

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.LatIndex

open Matrix

theorem cast_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    (((z ⬝ᵥ M *ᵥ z : ℤ)) : ℝ) =
      (fun i => (z i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (z i : ℝ)) := by
  simp [dotProduct, mulVec, Int.cast_sum, Int.cast_mul]

theorem gram_quad {n : ℕ} {Y : Type} [AddCommGroup Y] (β : LinearMap.BilinForm ℤ Y)
    (v : Fin n → Y) (z : Fin n → ℤ) :
    z ⬝ᵥ (Matrix.of fun i j => β (v i) (v j)) *ᵥ z = β (∑ i, z i • v i) (∑ i, z i • v i) := by

  simp [dotProduct, mulVec, map_sum, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem posSemidef_map_intCast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hs : Mᵀ = M)
    (h : ∀ z : Fin n → ℤ, 0 ≤ z ⬝ᵥ M *ᵥ z) : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    have := congrFun (congrFun hs i) j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢
    rw [this]
  · simp only [star_trivial]
    have hcl : IsClosed {x : Fin n → ℝ | 0 ≤ x ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ x} :=
      isClosed_le continuous_const (by fun_prop)
    refine (DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl
      fun q => ?_
    show 0 ≤ (fun i => ((q i : ℚ) : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => ((q i : ℚ) : ℝ))
    set d : ℕ := ∏ i, (q i).den with hd
    have hd0 : (0 : ℝ) < d := by
      rw [hd]; exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    have hc : ∀ i, ∃ c : ℕ, d = (q i).den * c := fun i =>
      Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)
    choose c hc using hc
    let z : Fin n → ℤ := fun i => (q i).num * c i
    have hz : ∀ i, ((q i : ℚ) : ℝ) = (d : ℝ)⁻¹ * (z i : ℝ) := by
      intro i
      have h1 : ((z i : ℤ) : ℚ) = q i * d := by
        simp only [z, hc i, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
        rw [← Rat.mul_den_eq_num]; ring
      have h2 : ((z i : ℤ) : ℝ) = ((q i : ℚ) : ℝ) * d := by
        have := congrArg (fun t : ℚ => (t : ℝ)) h1
        simpa using this
      rw [h2]; field_simp
    have hfun : (fun i => ((q i : ℚ) : ℝ)) = (d : ℝ)⁻¹ • (fun i => (z i : ℝ)) := by
      ext i; simp [hz i]
    rw [hfun, smul_dotProduct, mulVec_smul, dotProduct_smul, ← cast_quad]
    have := h z
    have h3 : (0 : ℝ) ≤ ((z ⬝ᵥ M *ᵥ z : ℤ) : ℝ) := by exact_mod_cast this
    simp only [smul_eq_mul]
    positivity

theorem det_sq_mul_pow_le_prod :
    ∀ (r : ℕ) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (X : Type)
      [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (b : Module.Basis (Fin r) ℤ X₀)
      (ε : X ≃ₗ[ℤ] X₀) (k : X₀ →ₗ[ℤ] X) (β : LinearMap.BilinForm ℤ X),
      (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ lam : ℝ, 0 ≤ lam →
      (∀ x, x ≠ 0 → lam ≤ β x x) →
      ((LinearMap.det (ε.toLinearMap ∘ₗ k) : ℤ) : ℝ) ^ 2 * lam ^ r ≤
        (r : ℝ) ^ r * ∏ j, (β (k (b j)) (k (b j)) : ℝ) := by
  intro r X₀ _ _ _ X _ _ _ b ε k β hsym hpos lam hlam hmin
  classical
  let e : Module.Basis (Fin r) ℤ X := b.map ε.symm
  have he : ∀ i, e i = ε.symm (b i) := fun i => by simp [e]
  let Gz : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => β (e i) (e j)
  let A : Matrix (Fin r) (Fin r) ℤ := LinearMap.toMatrix b b (ε.toLinearMap ∘ₗ k)
  let Mz : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => β (k (b i)) (k (b j))
  have hkb : ∀ j, k (b j) = ∑ i, A i j • e i := by
    intro j
    have h1 : ε (k (b j)) = ∑ i, A i j • b i := by
      simp only [A, LinearMap.toMatrix_apply]
      exact (b.sum_repr _).symm
    have h2 := congrArg ε.symm h1

    simp only [LinearEquiv.symm_apply_apply, map_sum, map_zsmul] at h2
    rw [h2]; simp [he]
  have hM : Mz = Aᵀ * Gz * A := by
    ext j l
    simp only [Mz, Gz, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hkb]

    simp [map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm]
  have hdetA : A.det = LinearMap.det (ε.toLinearMap ∘ₗ k) := LinearMap.det_toMatrix b _
  have hGs : Gzᵀ = Gz := by ext i j; simp [Gz, hsym]
  have hMs : Mzᵀ = Mz := by ext i j; simp [Mz, hsym]
  have hGq : ∀ z, 0 ≤ z ⬝ᵥ Gz *ᵥ z := fun z => by rw [gram_quad]; exact hpos _
  have hMq : ∀ z, 0 ≤ z ⬝ᵥ Mz *ᵥ z := fun z => by rw [gram_quad]; exact hpos _
  have hG := posSemidef_map_intCast Gz hGs hGq
  have hMp := posSemidef_map_intCast Mz hMs hMq
  have hmink : lam ^ r ≤ (r : ℝ) ^ r * (Gz.map (Int.cast : ℤ → ℝ)).det := by
    refine GlobalTheory.minkowski_det_bound_posSemidef r _ hG lam hlam fun z hz => ?_
    rw [← cast_quad, gram_quad]
    apply hmin
    intro h0
    apply hz
    have : e.equivFun.symm z = e.equivFun.symm 0 := by
      rw [map_zero, Module.Basis.equivFun_symm_apply]; exact h0
    exact e.equivFun.symm.injective this
  have hhad := GlobalTheory.T.posSemidef_det_le_prod_diag' r _ hMp
  have hdetM : (Mz.map (Int.cast : ℤ → ℝ)).det =
      ((A.det : ℤ) : ℝ) ^ 2 * (Gz.map (Int.cast : ℤ → ℝ)).det := by
    have h1 : ∀ N : Matrix (Fin r) (Fin r) ℤ, (N.map (Int.cast : ℤ → ℝ)).det = ((N.det : ℤ) : ℝ) :=
      fun N => by
        rw [show (N.map (Int.cast : ℤ → ℝ)) = (Int.castRingHom ℝ).mapMatrix N from rfl,
          ← RingHom.map_det]; rfl
    rw [h1, h1, hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    push_cast; ring
  have hdiag : ∀ j, (Mz.map (Int.cast : ℤ → ℝ)) j j = (β (k (b j)) (k (b j)) : ℝ) := by
    intro j; simp [Mz]
  simp only [hdiag] at hhad
  rw [← hdetA]
  calc ((A.det : ℤ) : ℝ) ^ 2 * lam ^ r
      ≤ ((A.det : ℤ) : ℝ) ^ 2 * ((r : ℝ) ^ r * (Gz.map (Int.cast : ℤ → ℝ)).det) :=
        mul_le_mul_of_nonneg_left hmink (sq_nonneg _)
    _ = (r : ℝ) ^ r * (Mz.map (Int.cast : ℤ → ℝ)).det := by rw [hdetM]; ring
    _ ≤ (r : ℝ) ^ r * ∏ j, (β (k (b j)) (k (b j)) : ℝ) :=
        mul_le_mul_of_nonneg_left hhad (by positivity)

end GlobalTheory.LatIndex
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSqMulPowLeProdBilinFormLatticeBasisStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.det_sq_mul_pow_le_prod_bilinForm_lattice_basis : ∀ (r : ℕ) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (b : Module.Basis (Fin r) ℤ X₀) (ε : X ≃ₗ[ℤ] X₀) (k : X₀ →ₗ[ℤ] X) (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ lam : ℝ, 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ β x x) → ((LinearMap.det (ε.toLinearMap ∘ₗ k) : ℤ) : ℝ) ^ 2 * lam ^ r ≤ (r : ℝ) ^ r * ∏ j, (β (k (b j)) (k (b j)) : ℝ) := by
  first | exact @GlobalTheory.LatIndex.det_sq_mul_pow_le_prod | exact GlobalTheory.LatIndex.det_sq_mul_pow_le_prod | (intros; apply GlobalTheory.LatIndex.det_sq_mul_pow_le_prod <;> assumption)
end
end
