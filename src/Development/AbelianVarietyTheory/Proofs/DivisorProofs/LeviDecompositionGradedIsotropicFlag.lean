module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingPartNonLoweringUnitStatement
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicFlagLeviOfKeepsWeightsStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMemIsotropicFlagLeviStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFlagStabilizerNotLowerWeight

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.UAut.NoLower

theorem abstract_no_lower {A : Type} [CommRing A] {n r : ℕ} (st : Matrix (Fin n) (Fin n) A →+ Matrix (Fin n) (Fin n) A)
    (u : Fin r → Matrix (Fin n) (Fin n) A) (X Y : Matrix (Fin n) (Fin r) A) (L T : Matrix (Fin r) (Fin n) A)
    (hu : ∀ j, u j = X * single j j (1 : A) * L) (hs : ∀ j, st (u j) = Y * single j j (1 : A) * T)
    (hLX : L * X = 1) (hTX : T * X = 0) (hTY : T * Y = 1) (d : Fin r → ℕ) (M : ℕ) (hd : ∀ j, d j < M)
    (x : Matrix (Fin n) (Fin n) A) (B C : Matrix (Fin r) (Fin r) A) (hB : ∀ i j, d j < d i → B i j = 0)
    (hC : ∀ i j, d i < d j → C i j = 0) (eB : x * X = X * B) (eC : T * x = C * T) :
    ∀ a b, wt d M a < wt d M b → fam st u a * x * fam st u b = 0 := by
  have e0 : fam st u none = 1 - (X * L + Y * T) := by
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs]
    simp only [hu, ← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  have e1 : ∀ j, fam st u (some (.inl j)) = X * single j j (1 : A) * L := hu
  have e2 : ∀ j, fam st u (some (.inr j)) = Y * single j j (1 : A) * T := hs
  have k0 : fam st u none * X = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLX, hTX]; simp
  have k1 : T * fam st u none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTY, hTX]; simp
  have l1 : ∀ (e : Matrix (Fin n) (Fin n) A) (j : Fin r), e * x * (X * single j j (1 : A) * L) =
      e * X * B * single j j (1 : A) * L := fun e j => by
    rw [Matrix.mul_assoc e X, ← eB]; simp only [Matrix.mul_assoc]
  have l2 : ∀ (e : Matrix (Fin n) (Fin n) A) (j : Fin r), (Y * single j j (1 : A) * T) * x * e =
      Y * single j j (1 : A) * C * (T * e) := fun e j => by
    rw [Matrix.mul_assoc _ T, eC]; simp only [Matrix.mul_assoc]
  have sm : ∀ (D : Matrix (Fin r) (Fin r) A) (i j : Fin r), D i j = 0 →
      single i i (1 : A) * D * single j j (1 : A) = 0 := fun D i j h => by
    rw [Matrix.single_mul_mul_single, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp at hab
  · rw [e1, l1, k0]; simp
  · have := hd j; simp [wt] at hab; omega
  · have := hd i; simp [wt] at hab; omega
  · have h := sm B i j (hB i j (by simp [wt] at hab; omega))
    rw [e1, e1, l1, Matrix.mul_assoc _ L, hLX, Matrix.mul_one, Matrix.mul_assoc X, Matrix.mul_assoc X, h]; simp
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, l2, k1]; simp
  · rw [e1, e2, l1, Matrix.mul_assoc _ T, hTX]; simp
  · have h := sm C i j (hC i j (by simp [wt] at hab; omega))
    rw [e2, e2, l2, ← Matrix.mul_assoc T, ← Matrix.mul_assoc T, hTY, Matrix.one_mul, ← Matrix.mul_assoc,
      Matrix.mul_assoc Y, Matrix.mul_assoc Y, h]; simp

theorem parFlag_no_lower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J X d, ∀ a b, wt d M a < wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y d M hd hXX _ hXY p hp
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hcm
  have cc : ∀ {m q : Type} (A : Matrix m q E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have eC := form_mul_of_mul_cols eB'
  rw [inv_inv] at eC
  have hLX : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hXY
    rwa [cT_mul, cT_mul, cc, cT_form hJ, cT_one, ← Matrix.mul_assoc] at this
  refine abstract_no_lower _ _ (adMat F X) (adMat F Y) (adMat F (cT (σ : E →+* E) Y * J))
    (adMat F (cT (σ : E →+* E) X * J)) (fun j => idemA_eq _ _ j) (fun j => ?_) ?_ ?_ ?_ d M hd _ B _
    (fun i j h => hB h) (fun i j h => ?_) eB eC
  · have s : cT (σ : E →+* E) (single j j (1 : E) : Matrix (Fin r) (Fin r) E) = single j j 1 := by
      rw [cT, Matrix.map_single, Matrix.transpose_single, map_one]
    have e : J⁻¹ * cT (σ : E →+* E) (X * single j j (1 : E) * (cT (σ : E →+* E) Y * J)) * J =
        Y * single j j (1 : E) * (cT (σ : E →+* E) X * J) := by
      rw [cT_mul, cT_mul, cT_mul, cc, cT_form hJ, s, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]
      simp only [Matrix.mul_assoc]
    rw [idemA, adjA_map, e]
    exact idemA_eq Y _ j
  · rw [adMat, adMat, ← Matrix.map_mul, hLX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [adMat, adMat, ← Matrix.map_mul, hXX, Matrix.map_zero _ (map_zero _)]
  · rw [adMat, adMat, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' h, map_zero]

end GlobalTheory.UAut.NoLower
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFlagStabilizerNotLowerWeightStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

theorem _root_.GlobalTheory.T.isotropicFlagStabilizer_not_lower_weight : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J X d, ∀ a b, wt d M a < wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  first | exact @GlobalTheory.UAut.NoLower.parFlag_no_lower | exact GlobalTheory.UAut.NoLower.parFlag_no_lower | (intros; apply GlobalTheory.UAut.NoLower.parFlag_no_lower <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeIsotropicFlagStabilizerNotRaiseWeight

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut.OppFlagWeight

theorem weight_of_triangular {A : Type} [CommRing A] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) A}
    {L T : Matrix (Fin r) (Fin n) A} {x : Matrix (Fin n) (Fin n) A} {B B' : Matrix (Fin r) (Fin r) A}
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M)
    (hLX : L * X = 1) (hTY : T * Y = 1) (hLY : L * Y = 0)
    (hB : x * Y = Y * B) (hB' : L * x = B' * L) (tB : ∀ i j, d j < d i → B i j = 0) (tB' : ∀ i j, d i < d j → B' i j = 0)
    (ε : Option (Fin r ⊕ Fin r) → Matrix (Fin n) (Fin n) A)
    (e0 : ε none = 1 - (X * L + Y * T)) (e1 : ∀ j, ε (some (.inl j)) = X * single j j (1 : A) * L)
    (e2 : ∀ j, ε (some (.inr j)) = Y * single j j (1 : A) * T) :
    ∀ a b, wt d M b < wt d M a → ε a * x * ε b = 0 := by
  have k0 : ε none * Y = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLY, hTY]; simp
  have k1 : L * ε none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLY, hLX]; simp
  have k2 : ∀ (m : Matrix (Fin n) (Fin n) A) j, m * Y = 0 → m * x * ε (some (.inr j)) = 0 := fun m j h => by
    rw [e2, Matrix.mul_assoc Y, ← Matrix.mul_assoc, Matrix.mul_assoc m, hB, ← Matrix.mul_assoc m, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp [wt] at hab
  · have := hd j; simp [wt] at hab; omega
  · exact k2 _ j k0
  · rw [e1, Matrix.mul_assoc _ L, hB', ← Matrix.mul_assoc, Matrix.mul_assoc _ L, k1, Matrix.mul_zero]
  · rw [e1, e1, sandwich_eq_zero hLX, hB', Matrix.mul_assoc, hLX, Matrix.mul_one]
    exact tB' i j (by simp [wt] at hab; omega)
  · exact k2 _ j (by rw [e1, Matrix.mul_assoc, hLY, Matrix.mul_zero])
  · have := hd i; simp [wt] at hab; omega
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, e2, sandwich_eq_zero hTY, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hTY, Matrix.one_mul]
    exact tB i j (by simp [wt] at hab; omega)

theorem not_raise_of_mem_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J Y d, ∀ a b, wt d M b < wt d M a → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y d M hd _ hY hXY p hp
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => sigma_sigma h _
  have hYX : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hXY
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have f := form_mul_of_mul_cols eB'
  rw [inv_inv] at f
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have adj : ∀ Z : Matrix (Fin r) (Fin r) E, adjA σ J ((X * Z * (Formalism.UG.cT (σ : E →+* E) Y * J)).map φ) =
      Y.map φ * (Formalism.UG.cT (σ : E →+* E) Z).map φ * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun Z => by
    rw [adjA_map, ← Matrix.map_mul, ← Matrix.map_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J⁻¹, Matrix.nonsing_inv_mul _ (det_isUnit hJ), Matrix.one_mul]
  refine weight_of_triangular (X := X.map φ) (Y := Y.map φ) (L := (Formalism.UG.cT (σ : E →+* E) Y * J).map φ)
    (T := (Formalism.UG.cT (σ : E →+* E) X * J).map φ) hd ?_ ?_ ?_ eB f (fun i j hij => hB hij) (fun i j hij => ?_) _ ?_
    (fun j => idemA_eq _ _ j) (fun j => ?_)
  · rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hY, Matrix.map_zero _ (map_zero _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' hij, map_zero]
  · have := adj 1
    rw [Matrix.mul_one, Formalism.UG.cT_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

    rw [← map_sum, sum_idemA, this, Matrix.map_mul]
  · refine (adj (single j j 1)).trans ?_
    congr 2
    ext a b
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp [Formalism.UG.cT, single, h1, h2]

end GlobalTheory.UAut.OppFlagWeight
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeIsotropicFlagStabilizerNotRaiseWeightStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

theorem _root_.GlobalTheory.T.oppositeIsotropicFlagStabilizer_not_raise_weight : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J Y d, ∀ a b, wt d M b < wt d M a → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  first | exact @GlobalTheory.UAut.OppFlagWeight.not_raise_of_mem_parFlag | exact GlobalTheory.UAut.OppFlagWeight.not_raise_of_mem_parFlag | (intros; apply GlobalTheory.UAut.OppFlagWeight.not_raise_of_mem_parFlag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.LeviFlag

private theorem cT_mul_lemma {A : Type} [CommRing A] (s : A →+* A) {a b c : ℕ} (P : Matrix (Fin a) (Fin b) A)
    (Q : Matrix (Fin b) (Fin c) A) : Formalism.UG.cT s (P * Q) = Formalism.UG.cT s Q * Formalism.UG.cT s P := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_cT_of_involutive {A : Type} [CommRing A] (s : A →+* A) (hs : ∀ x, s (s x) = x) {a b : ℕ}
    (P : Matrix (Fin a) (Fin b) A) : Formalism.UG.cT s (Formalism.UG.cT s P) = P := by
  unfold Formalism.UG.cT
  ext i j
  simp [hs]

private theorem cT_one_divisor {A : Type} [CommRing A] (s : A →+* A) {a : ℕ} :
    Formalism.UG.cT s (1 : Matrix (Fin a) (Fin a) A) = 1 := by
  unfold Formalism.UG.cT
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

private theorem cT_Y_J_X_eq_one_and_complement_eq_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (hσ : ∀ x, σ (σ x) = x) {X Y : Matrix (Fin n) (Fin r) E}
    (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0) (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) :
    Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 ∧
      Formalism.UG.cT (σ : E →+* E) Y * J * J⁻¹ * Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Y * J) = 0 := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => hσ x
  have hJJ : Formalism.UG.cT (σ : E →+* E) J = J := by
    unfold Formalism.UG.cT
    ext i j
    simp [hJ.1 i j]
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  constructor
  · have e := congrArg (Formalism.UG.cT (σ : E →+* E)) hxy
    rw [cT_mul_lemma, cT_mul_lemma, cT_cT_of_involutive _ hs, hJJ, cT_one_divisor, ← Matrix.mul_assoc] at e
    exact e
  · rw [cT_mul_lemma, cT_cT_of_involutive _ hs, hJJ, Matrix.mul_nonsing_inv_cancel_right _ _ hdet, ← Matrix.mul_assoc]
    exact hyy

private theorem exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ)
    (hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0)
    (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) (p : GAd σ J) (hp : p ∈ parFlag σ J X d) :
    ∃ u ∈ unipFlag σ J X d, ∃ m ∈ leviFlag σ J X Y d, p = u * m ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) := by
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma h
  obtain ⟨hL, hLL⟩ := cT_Y_J_X_eq_one_and_complement_eq_zero σ hJ hσ hyy hxy
  have hdM : ∀ j, d j < ∑ i, d i + 1 := fun j =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  have hm : ∀ a b, adjA σ J (a * b) = adjA σ J b * adjA σ J a := adjA_mul hJ
  have hi : ∀ a, adjA σ J (adjA σ J a) = a := adjA_adjA hJ hσ
  have hε : CompleteOrthogonalIdempotents (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))) :=
    idemA_complete hJ X _ hL hxx hLL
  have h1 : adjA σ J 1 = 1 := by
    have e := hm (adjA σ J 1) 1
    simp only [mul_one, hi] at e
    exact e.symm
  have hτ : ∀ a, adjA σ J (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a) =
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) (Option.map Sum.swap a) := by
    rintro (_ | j | j)
    · show adjA σ J (1 - ∑ j, Sum.elim (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))
          (fun j => adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j)) j) =
        1 - ∑ j, Sum.elim (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))
          (fun j => adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j)) j

      rw [map_sub, h1, map_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hi]
      rw [add_comm]
    · rfl
    · exact hi _
  have hw : ∀ a, wt d (∑ i, d i + 1) (Option.map Sum.swap a) = - wt d (∑ i, d i + 1) a := by
    rintro (_ | j | j) <;> simp [wt]
  have hττ : ∀ a : Option (Fin r ⊕ Fin r), Option.map Sum.swap (Option.map Sum.swap a) = a := by
    rintro (_ | j | j) <;> rfl
  have hxy1 : (matHom _ σ J p).1 * (matHom _ σ J p⁻¹).1 = 1 := by
    rw [map_inv]
    exact Units.mul_inv _
  have hyx1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [map_inv]
    exact Units.inv_mul _
  obtain ⟨m, m', hmm', hm'm, hstm, hmd, hm'd, hraise, hsub⟩ :=
    GlobalTheory.T.exists_weightPreservingPart_nonLowering_unit (adjA σ J) (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)))
      (wt d (∑ i, d i + 1)) (Option.map Sum.swap) hm hi hε hτ hw hττ _ _ hxy1 hyx1 (adjA_mat hJ p)
      (GlobalTheory.T.isotropicFlagStabilizer_not_lower_weight F E σ h n J hJ r X Y d _ hdM hxx hyy hxy p hp)
      (GlobalTheory.T.isotropicFlagStabilizer_not_lower_weight F E σ h n J hJ r X Y d _ hdM hxx hyy hxy p⁻¹ (inv_mem hp))
  let U : GL (Fin n) (AF F ⊗[F] E) := ⟨m, m', hmm', hm'm⟩
  have hU : U ∈ HR (AF F) σ J := (adjA_mul_self_iff hJ U).1 (by
    show adjA σ J m * m = 1
    rw [hstm, hm'm])
  let g : GAd σ J := (⟨U, hU⟩ : HR (AF F) σ J)
  have hg1 : (matHom _ σ J g).1 = m := rfl
  have hg2 : (matHom _ σ J g⁻¹).1 = m' := by
    rw [map_inv]
    rfl
  have hgl : g ∈ leviFlag σ J X Y d :=
    GlobalTheory.T.mem_isotropicFlagLevi_of_keeps_weights F E σ h n J hJ r X Y d _ hdM hxx hyy hxy g (by rw [hg1]; exact hmd) (by rw [hg2]; exact hm'd)
  refine ⟨p * g⁻¹, ?_, g, hgl, (inv_mul_cancel_right p g).symm, ?_⟩
  · rw [mem_unipFlag_iff_raise hJ hσ X _ hL hxx hLL hdM, map_mul, Units.val_mul, hg2]
    exact hraise
  · intro hpr
    rw [← range_ratEmb σ J] at hpr
    obtain ⟨γ, hγ⟩ := hpr
    have : Nontrivial (AF F) := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      exact (evInf F w).toRingHom.domain_nontrivial
    have hinj : Function.Injective (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E) :=
      Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap F (AF F)))
    have hφ : Function.Injective ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix :
        Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := Matrix.map_injective hinj
    have hu : ∀ j, idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range :=
      fun j => ⟨_, rfl⟩
    have hsu : ∀ j, adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j) ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      intro j
      show adjA σ J ((X * Matrix.single j j (1 : E) * (Formalism.UG.cT (σ : E →+* E) Y * J)).map
        (inclR (F := F) (AF F))) ∈ _
      rw [adjA_map]
      exact ⟨_, rfl⟩
    have hε0 : ∀ a, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rintro (_ | j | j)
      · exact Subring.sub_mem _ (Subring.one_mem _) (Subring.sum_mem _ fun j _ => by
          rcases j with j | j
          exacts [hu j, hsu j])
      · exact hu j
      · exact hsu j
    have hx0 : (matHom _ σ J p).1 ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rw [← hγ]
      exact ⟨_, rfl⟩
    have hy0 : (matHom _ σ J p⁻¹).1 ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rw [← hγ, ← map_inv]
      exact ⟨_, rfl⟩
    obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ := hsub _ hε0 hx0 hy0
    have hkk' : k * k' = 1 := hφ (by rw [map_mul, map_one, hk, hk', hmm'])
    have hk'k : k' * k = 1 := hφ (by rw [map_mul, map_one, hk, hk', hm'm])
    have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
    have hadj : J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J = k' := hφ (by
      show (J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J).map (inclR (F := F) (AF F)) = _
      rw [← adjA_map, hk', ← hstm, ← hk]
      rfl)
    have hUJ : Formalism.UG.cT (σ : E →+* E) k * J * k = J := by
      calc Formalism.UG.cT (σ : E →+* E) k * J * k = J * (J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J) * k := by
            rw [← mul_assoc J, ← mul_assoc J, Matrix.mul_nonsing_inv _ hdet, one_mul]
        _ = J := by rw [hadj, mul_assoc, hk'k, mul_one]
    let K : GL (Fin n) E := ⟨k, k', hkk', hk'k⟩
    have hK : K ∈ Formalism.UG.UJ (σ : E →+* E) J := by
      show Formalism.UG.cT (σ : E →+* E) k * J * k = J
      exact hUJ
    rw [← range_ratEmb σ J]
    refine ⟨⟨K, hK⟩, matHom_injective _ σ J (Units.ext ?_)⟩
    show (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix k = m
    exact hk

private theorem unipFlag_inf_leviFlag_eq_bot (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ)
    (hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0)
    (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) :
    unipFlag σ J X d ⊓ leviFlag σ J X Y d = ⊥ := by
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma h
  obtain ⟨hL, hLL⟩ := cT_Y_J_X_eq_one_and_complement_eq_zero σ hJ hσ hyy hxy
  have hdM : ∀ j, d j < ∑ i, d i + 1 := fun j =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  have hε : CompleteOrthogonalIdempotents (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))) :=
    idemA_complete hJ X _ hL hxx hLL
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hu, hl⟩ := Subgroup.mem_inf.1 hg
  have hl' : g ∈ parFlag σ J X d ⊓ parFlag σ J Y d := hl
  rw [mem_unipFlag_iff_raise hJ hσ X _ hL hxx hLL hdM] at hu
  have hu' : ∀ a b, wt d (∑ i, d i + 1) a ≤ wt d (∑ i, d i + 1) b + ((0 : ℕ) : ℤ) →
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * ((matHom _ σ J g).1 - 1) *
        fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := hu
  have hY := GlobalTheory.T.oppositeIsotropicFlagStabilizer_not_raise_weight F E σ h n J hJ r X Y d _ hdM hxx hyy hxy g (Subgroup.mem_inf.1 hl').2
  have hz : ∀ a b, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * ((matHom _ σ J g).1 - 1) *
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
    intro a b
    by_cases hab : wt d (∑ i, d i + 1) a ≤ wt d (∑ i, d i + 1) b
    · exact hu' a b (by simpa using hab)
    · rw [not_le] at hab
      have hne : a ≠ b := by
        rintro rfl
        exact lt_irrefl _ hab
      rw [mul_sub, sub_mul, hY a b hab, mul_one, hε.ortho hne, sub_zero]
  have h0 : (matHom _ σ J g).1 - 1 = 0 := by
    rw [show (matHom _ σ J g).1 - 1 =
        (∑ a, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a) * ((matHom _ σ J g).1 - 1) *
          (∑ b, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b) by
        rw [hε.complete, one_mul, mul_one]]
    simp only [Finset.sum_mul, Finset.mul_sum, hz, Finset.sum_const_zero]
  apply matHom_injective _ σ J
  rw [map_one]
  exact Units.ext (sub_eq_zero.1 h0)

theorem levi_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → (∀ p ∈ parFlag σ J X d, ∃ u ∈ unipFlag σ J X d, ∃ m ∈ leviFlag σ J X Y d, p = u * m ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J)) ∧ unipFlag σ J X d ⊓ leviFlag σ J X Y d = ⊥ ∧ leftGrp σ J X d = unipFlag σ J X d ⊔ (ratPts σ J ⊓ leviFlag σ J X Y d) ∧ ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y d hxx hyy hxy
  refine ⟨fun p hp => exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag F E σ h n J hJ r X Y d hxx hyy hxy p hp,
    unipFlag_inf_leviFlag_eq_bot F E σ h n J hJ r X Y d hxx hyy hxy, ?_,
    fun t a ht hta => GlobalTheory.T.splitTorusElement_mem_isotropicFlagLevi F E σ h n J hJ r X Y d hxx hyy hxy t a ht hta⟩
  apply le_antisymm
  · show unipFlag σ J X d ⊔ (ratPts σ J ⊓ parFlag σ J X d) ≤ _
    refine sup_le le_sup_left ?_
    intro p hp
    obtain ⟨hpr, hpp⟩ := Subgroup.mem_inf.1 hp
    obtain ⟨u, hu, m, hm, hpe, hrat⟩ := exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag F E σ h n J hJ r X Y d hxx hyy hxy p hpp
    rw [hpe]
    exact Subgroup.mul_mem_sup hu (Subgroup.mem_inf.2 ⟨hrat hpr, hm⟩)
  · show _ ≤ unipFlag σ J X d ⊔ (ratPts σ J ⊓ parFlag σ J X d)
    exact sup_le_sup_left (inf_le_inf_left _ (inf_le_left : parFlag σ J X d ⊓ parFlag σ J Y d ≤ _)) _

end GlobalTheory.LeviFlag
end
end
end
