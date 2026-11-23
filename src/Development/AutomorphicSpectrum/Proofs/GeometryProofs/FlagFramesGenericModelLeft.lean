module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisChangeIntegralStatement
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrix
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagChartGenericField

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem inChart_flagCoord_ratios : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (p' : Cpt ξ') (c₁ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), InChart ξ' (flagCoord κ x φ c) ((c₁, J) : FlagIx κ n r) p' → algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 ∧ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p' ∧ ∀ q : Σ s, Fin (r s), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 ∧ ∀ l j, ((flagMat φ c q.1).submatrix (Function.update (J q) l j) (Fin.castLE q.2.2)).det / ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ∈ regAt ξ' p' := by
  intro Ω _ E _ _ κ x S _ r n φ c X' ξ' p' c₁ J h
  classical
  simp only [InChart] at h ⊢
  obtain ⟨hne, hreg⟩ := h
  have hF : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      flagCoord κ x φ c ((k, J') : FlagIx κ n r) = algebraMap Ω (GenField Ω r) (x k) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J' q) (Fin.castLE q.2.2)).det :=
    fun _ _ => rfl
  rw [hF] at hne
  have hx : algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 := left_ne_zero_of_mul hne
  have hP : ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 :=
    right_ne_zero_of_mul hne
  refine ⟨hx, ⟨hx, fun k => ?_⟩, fun q => ⟨?_, fun l j => ?_⟩⟩
  · have hq := hreg ((k, J) : FlagIx κ n r)
    rw [hF, hF] at hq
    rwa [mul_div_mul_right _ _ hP] at hq
  · exact (Finset.prod_ne_zero_iff.mp hP) q (Finset.mem_univ q)
  · have hsplit : ∀ J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1),
        ∏ q' : (Σ s, Fin (r s)), ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det =
        ((flagMat φ c q.1).submatrix (J' q) (Fin.castLE q.2.2)).det *
          ∏ q' ∈ Finset.univ.erase q, ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det := by
      intro J'
      rw [← Finset.mul_prod_erase Finset.univ
        (fun q' : (Σ s, Fin (r s)) => ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det)
        (Finset.mem_univ q)]
    have hrest : ∏ q' ∈ Finset.univ.erase q,
          ((flagMat φ c q'.1).submatrix (Function.update J q (Function.update (J q) l j) q')
            (Fin.castLE q'.2.2)).det =
        ∏ q' ∈ Finset.univ.erase q, ((flagMat φ c q'.1).submatrix (J q') (Fin.castLE q'.2.2)).det :=
      Finset.prod_congr rfl fun q' hq' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
    have hR : ∏ q' ∈ Finset.univ.erase q,
        ((flagMat φ c q'.1).submatrix (J q') (Fin.castLE q'.2.2)).det ≠ 0 := by
      intro h0
      apply hP
      rw [hsplit J, h0, mul_zero]
    have hq := hreg ((c₁, Function.update J q (Function.update (J q) l j)) : FlagIx κ n r)
    rw [hF, hF, hsplit (Function.update J q (Function.update (J q) l j)), hsplit J, hrest,
      Function.update_self] at hq
    rwa [mul_div_mul_left _ _ hx, mul_div_mul_right _ _ hR] at hq

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagChartGenericFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.flag_chart_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (p' : Cpt ξ') (c₁ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), InChart ξ' (flagCoord κ x φ c) ((c₁, J) : FlagIx κ n r) p' → algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 ∧ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p' ∧ ∀ q : Σ s, Fin (r s), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 ∧ ∀ l j, ((flagMat φ c q.1).submatrix (Function.update (J q) l j) (Fin.castLE q.2.2)).det / ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ∈ regAt ξ' p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios | exact GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrixStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.frame_change_by_unit_matrix : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ) (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det → L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb | exact GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.frame_coeffs_regular_in_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m n r : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x L m φ → ∀ (p : Cpt ξ) (c₁ : κ), InChart ξ x c₁ p → ∀ β : Fin r → E, L.IsFrameAt β p → ∃ B : Matrix (Fin r) (Fin n) Ω, (∀ a j, B a j ∈ regAt ξ p) ∧ (∀ j a, φ j (β a) / x c₁ ^ m ∈ regAt ξ p) ∧ B * Matrix.of (fun j a => φ j (β a) / x c₁ ^ m) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse | exact GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MinorRatioRegularOfInvertible

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

theorem mul_inv_apply_eq_det_div {K : Type} [Field K] {n r m : ℕ} (F : Matrix (Fin n) (Fin r) K)
    (J : Fin m → Fin n) (c : Fin m → Fin r) (j : Fin n) (l : Fin m) :
    ((F.submatrix id c) * (F.submatrix J c)⁻¹) j l =
      (F.submatrix (Function.update J l j) c).det / (F.submatrix J c).det := by
  have hrow : F.submatrix (Function.update J l j) c =
      (F.submatrix J c).updateRow l (fun k => F j (c k)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.updateRow_apply, Function.update_apply]
    split_ifs <;> rfl
  have key : (F.submatrix (Function.update J l j) c).det =
      ∑ k, F j (c k) * (F.submatrix J c).adjugate k l := by
    rw [hrow, ← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [key, Matrix.mul_apply, Matrix.inv_def, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.submatrix_apply, id_eq, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  ring

theorem split_of_regular_ratios (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K)
    (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r)
    (J : Fin ((k : ℕ) + 1) → Fin n) (hA : ∀ j l, A j l ∈ R) (hB : ∀ l j, B l j ∈ R) (hBA : B * A = 1)
    (_ha : a ≠ 0) (hdet : ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0)
    (hR : ∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det /
      ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) :
    ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧
      (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧
      ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  have hN' : (a • (A * G)).submatrix id (Fin.castLE k.2) = A * (a • G.submatrix id (Fin.castLE k.2)) := by
    ext i l
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.mul_apply, id_eq, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin r) (Fin ((k : ℕ) + 1)) K,
      Q = (a • G.submatrix id (Fin.castLE k.2)) * ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ :=
    ⟨_, rfl⟩
  have hAQ : A * Q = (a • (A * G)).submatrix id (Fin.castLE k.2) *
      ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ := by
    rw [hQ, ← Matrix.mul_assoc, ← hN']
  have hBQ : Q = B * (A * Q) := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hPR : ∀ j l, (A * Q) j l ∈ R := by
    intro j l
    rw [hAQ, mul_inv_apply_eq_det_div]
    exact hR l j
  refine ⟨fun l i => Q i l, fun l i => A (J l) i, ?_, ?_, ?_, ?_⟩
  · intro l i
    show Q i l ∈ R
    rw [hBQ, Matrix.mul_apply]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hB i j) (hPR j l)
  · intro l i
    exact hA (J l) i
  · intro l l'
    change (A * Q) (J l) l' = _
    rw [hAQ]
    change (((a • (A * G)).submatrix J (Fin.castLE k.2)) *
      ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹) l l' = _
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_apply]
  · intro l
    have hD : (fun i => Q i l) = ∑ c : Fin ((k : ℕ) + 1),
        (a * ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ c l) • (fun i => G i (Fin.castLE k.2 c)) := by
      funext i
      rw [hQ]
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.submatrix_apply, id_eq, smul_eq_mul,
        Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun c _ => by ring
    show (fun i => Q i l) ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1)
    rw [hD]
    refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_image_of_mem (fun c i => G i c)
        (show (Fin.castLE k.2 c : Fin r) ∈ {c' : Fin r | (c' : ℕ) < (k : ℕ) + 1} from c.2)))

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MinorRatioRegularOfInvertibleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.minor_ratio_regular_of_invertible : ∀ (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K) (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r) (J : Fin ((k : ℕ) + 1) → Fin n), (∀ j l, A j l ∈ R) → (∀ l j, B l j ∈ R) → B * A = 1 → a ≠ 0 → ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0 → (∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det / ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) → ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | exact GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelLeft

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Flags

theorem isExtOver_mk (Ω K E : Type) [Field Ω] [Field K] [Algebra Ω K] [AddCommGroup E] [Module Ω E] :
    IsExtOver (algebraMap Ω K) (TensorProduct.mk Ω K E 1).toAddMonoidHom := by
  refine ⟨fun a e => ?_, fun n b hb => ?_⟩
  · show (1 : K) ⊗ₜ[Ω] (a • e) = algebraMap Ω K a • ((1 : K) ⊗ₜ[Ω] e)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · exact Module.Flat.linearIndependent_one_tmul hb

theorem pull_isFlagVB_genB : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom).IsFlagVBOn Set.univ (genB c s) := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hx hgen hVB hTw hc hx' hgen' hd hch s p' _
  classical
  obtain ⟨⟨c₁, J⟩, hcJ⟩ := hx'.cover p'
  obtain ⟨hx0, hchart, hmin⟩ := GlobalTheory.T.flag_chart_generic_field Ω E κ x S r n φ c X' ξ' p' c₁ J hcJ
  obtain ⟨hfp, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' _ ξ' f _ hd p'
  have hInC : InChart ξ x c₁ ⟨f p'.1, hfp⟩ := (hch p' c₁ hfp).2 hchart
  obtain ⟨U, hU, β₀, hspan, hfr⟩ := hVB s ⟨f p'.1, hfp⟩ trivial
  have hfr0 := hfr ⟨f p'.1, hfp⟩ trivial hU
  obtain ⟨B₀, hBreg, hAreg, hBA⟩ := GlobalTheory.T.frame_coeffs_regular_in_chart X Ω ξ E κ x (L s) (m s) (n s) (r s) (φ s) (hTw s) _ c₁ hInC β₀ hfr0
  have hxΩ : x c₁ ≠ 0 := hInC.1
  have hCex : ∀ l, ∃ C : Fin (r s) → Ω, c s l = ∑ a, C a • β₀ a := by
    intro l
    have : c s l ∈ Submodule.span Ω (Set.range β₀) := by
      rw [hspan, ← (hc s).2]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
    exact ⟨C, hC.symm⟩
  choose C hC using hCex
  set ι := algebraMap Ω (GenField Ω r) with hι
  let A₀ : Matrix (Fin (n s)) (Fin (r s)) Ω := Matrix.of (fun j a => φ s j (β₀ a) / x c₁ ^ m s)
  let A : Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := A₀.map ι
  let B : Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := B₀.map ι
  let Cm : Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := Matrix.of (fun a l => ι (C l a))
  let G : Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := Cm * genU Ω r s
  let a : GenField Ω r := ι (x c₁ ^ m s)
  have ha : a ≠ 0 := by
    simpa [a] using pow_ne_zero (m s) hx0
  have hF : flagMat φ c s = a • (A * G) := by
    have h1 : (Matrix.of (fun j l => ι (φ s j (c s l))) : Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
        = a • (A * Cm) := by
      ext j l
      simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, A, Cm, A₀, Matrix.map_apply, smul_eq_mul,
        Finset.mul_sum]

      rw [hC l, map_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_smul, smul_eq_mul, a, ← map_mul]
      congr 1
      field_simp
    rw [flagMat, h1, Matrix.smul_mul, Matrix.mul_assoc]
  have hBA' : B * A = 1 := by
    have := congrArg (fun M : Matrix (Fin (r s)) (Fin (r s)) Ω => M.map ι) hBA
    simpa [B, A, A₀, Matrix.map_mul] using this
  haveI : IsLocalRing (regAt ξ' p') := EigSplit.isLocalRing_regAt p'
  obtain ⟨P, hPreg, hP0, hPinv, hPflag⟩ := GlobalTheory.T.flag_basis_change_integral (GenField Ω r) (regAt ξ' p') (r s) (fun c i => G i c) (fun k =>
    GlobalTheory.T.minor_ratio_regular_of_invertible (GenField Ω r) (regAt ξ' p') (n s) (r s) A B G a k (J ⟨s, k⟩)
      (fun j l => hreg _ (hAreg j l)) (fun l j => hreg _ (hBreg l j)) hBA' ha
      (by have := (hmin ⟨s, k⟩).1; rwa [show flagMat φ c (⟨s, k⟩ : Σ s, Fin (r s)).1 = a • (A * G) from hF] at this)
      (by have := (hmin ⟨s, k⟩).2; rwa [show flagMat φ c (⟨s, k⟩ : Σ s, Fin (r s)).1 = a • (A * G) from hF] at this))
  have hext := isExtOver_mk Ω (GenField Ω r) E
  let β : Fin (r s) → TensorProduct Ω (GenField Ω r) E := fun a => TensorProduct.mk Ω (GenField Ω r) E 1 (β₀ a)
  let T : (Fin (r s) → GenField Ω r) →ₗ[GenField Ω r] TensorProduct Ω (GenField Ω r) E :=
    Fintype.linearCombination (GenField Ω r) β
  have hTapp : ∀ v, T v = ∑ a, v a • β a := fun v => by simp [T, Fintype.linearCombination_apply]
  have hmap : ∀ (w : Fin (r s) → Fin (r s) → GenField Ω r) (i : ℕ),
      flagStep (GenField Ω r) (fun k => T (w k)) i = (flagStep (GenField Ω r) w i).map T := by
    intro w i
    simp only [flagStep, Submodule.map_span, Set.image_image]
  have hgenB : genB c s = fun k => T (fun a => G a k) := by
    funext k
    rw [hTapp]
    simp only [genB, G, Matrix.mul_apply, Cm, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_

    rw [hC l, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : TensorProduct.mk Ω (GenField Ω r) E 1 (C l b • β₀ b) = ι (C l b) • β b := hext.1 (C l b) (β₀ b)
    rw [h1, smul_smul, mul_comm]
  have hPfun : (fun k => ∑ a, P a k • β a) = fun k => T (fun a => P a k) := by
    funext k
    rw [hTapp]
  obtain ⟨U₁, hU₁, hq₁⟩ := EigSplit.exists_open_forall_mem_regAt p'
    (fun ab : Fin (r s) × Fin (r s) => P ab.1 ab.2) (fun ab => hPreg _ _)
  have hdetreg : P.det ∈ regAt ξ' p' := by
    rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hPreg _ _)
  obtain ⟨U₂, hU₂, hq₂⟩ := (regAt_unitAt_open X' _ ξ' p' P.det).2 ⟨hP0, hdetreg, hPinv⟩
  refine ⟨(f ⁻¹ᵁ U) ⊓ U₁ ⊓ U₂, ⟨⟨hU, hU₁⟩, hU₂⟩, fun k => ∑ a, P a k • β a, ?_, ?_⟩
  · intro i
    rw [hgenB, hPfun, hmap, hmap, hPflag]
  · rintro q - ⟨⟨hqU, hq1⟩, hq2⟩
    obtain ⟨hqf, -, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' _ ξ' f _ hd q
    have hfq := hfr ⟨f q.1, hqf⟩ trivial hqU
    have hpull := FlagPull.pull_isFrameAt hd hext q hqf hfq
    exact GlobalTheory.T.frame_change_by_unit_matrix X' _ ξ' _ _ _ β q P hpull (fun a b => hq₁ q hq1 (a, b)) (hq₂ q hq2)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Flags
end
end
end
