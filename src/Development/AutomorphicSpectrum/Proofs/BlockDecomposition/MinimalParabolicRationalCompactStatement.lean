module

public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantClosedSubgroupCompactQuotientStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleBoundOfJointAnisotropicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalCommutesProjectionFamilyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalIdeleHermitianBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviParabolicIntersectionClosedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicLeviDecompositionStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFamilyAnisotropicJoint

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_eq_dot (σ : E →ₐ[F] E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ A x y = (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) := by
  have : hE σ A x y = ∑ i, ∑ j, σ (x i) * A i j * y j := rfl
  rw [this]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hE_normMat (σ : E →ₐ[F] E) {n : ℕ} (l ξ : Fin n → E) :
    hE σ (normMat σ l) ξ ξ = σ (l ⬝ᵥ ξ) * (l ⬝ᵥ ξ) := by
  have : hE σ (normMat σ l) ξ ξ = ∑ i, ∑ j, σ (ξ i) * (σ (l i) * l j) * ξ j := rfl
  rw [this]

  simp only [dotProduct, map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dot_eq_zero_of_hE_normMat (σ : E →ₐ[F] E) {n : ℕ} {l ξ : Fin n → E}
    (h : hE σ (normMat σ l) ξ ξ = 0) : l ⬝ᵥ ξ = 0 := by
  rw [hE_normMat] at h
  rcases mul_eq_zero.1 h with h | h
  · exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h
  · exact h

theorem hE_conj (σ : E →ₐ[F] E) {n : ℕ} (J P : Matrix (Fin n) (Fin n) E) (ξ : Fin n → E) :
    hE σ (cT (σ : E →+* E) P * J * P) ξ ξ = hE σ J (P *ᵥ ξ) (P *ᵥ ξ) := by
  rw [hE_eq_dot, hE_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT (σ : E →+* E) P)]
  congr 1
  ext j

  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem anisoProj_mulVec (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E)
    (ξ : Fin n → E) (hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0) (hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0) :
    anisoProj σ J X Y *ᵥ ξ = ξ := by
  have h0 : ∀ k, projFam σ J X Y k *ᵥ ξ = 0 := by
    rintro (i | i)
    · simp only [projFam, Sum.elim_inl, lineProj, Matrix.vecMulVec_mulVec, hY i]
      ext k
      simp
    · simp only [projFam, Sum.elim_inr, lineProj, Matrix.vecMulVec_mulVec, hX i]
      ext k
      simp
  rw [anisoProj, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Finset.sum_eq_zero fun k _ => h0 k, sub_zero]

end GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem hermFam_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ ξ : Fin n → E,
    (∀ j, hE σ (hermFam σ J X Y j) ξ ξ = 0) → ξ = 0 := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y hW ξ h
  have hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inl i)))
  have hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inr i)))
  have hπ := HermNondeg.anisoProj_mulVec σ J X Y ξ hX hY
  have hn : hE σ J ξ ξ = 0 := by
    have := h none
    change hE σ (cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y) ξ ξ = 0 at this
    rwa [HermNondeg.hE_conj, hπ] at this
  refine hW.aniso ξ ?_ ?_ hn
  · ext i
    exact hX i
  · ext i
    exact hY i

end GlobalTheory.CompanionTheory.ParCocompact
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFamilyAnisotropicJointStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.hermitian_family_anisotropic_joint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ ξ : Fin n → E, (∀ j, hE σ (hermFam σ J X Y j) ξ ξ = 0) → ξ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg | exact GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLeviMinimalOfCommutesProjections

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem mul_eq_mul_diagonal_of_comm {R : Type} [CommRing R] {n r : ℕ} {G : Matrix (Fin n) (Fin n) R}
    {C : Matrix (Fin n) (Fin r) R} {L : Matrix (Fin r) (Fin n) R} (hL : L * C = 1)
    (hc : ∀ i, G * Matrix.vecMulVec (fun k => C k i) (L i) = Matrix.vecMulVec (fun k => C k i) (L i) * G) :
    G * C = C * Matrix.diagonal (fun i => (L * (G * C)) i i) := by
  ext k i
  have h := congrArg (fun M => (M * C) k i) (hc i)
  simp only [Matrix.mul_assoc, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_apply] at h
  have h1 : (L i ᵥ* C) i = 1 := by
    have := congrFun (congrFun hL i) i
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
  rw [h1, mul_one] at h
  rw [Matrix.mul_diagonal, ← Matrix.mul_assoc]
  simpa [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct] using h

theorem mem_leviMin_of_comm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ leviMin σ J X Y ∧ γ ∈ minParOne σ J X := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW γ hγ hcomm
  have hF := pfrA h hJ hW
  have hinj : Function.Injective (inclR (F := F) (AF F) : E → AF F ⊗[F] E) := fun a b hab =>
    congrFun (GlobalTheory.CompanionTheory.RedCov.ratV_injective (F := F) (E := E) (n := 1)
      (show ratV F (fun _ : Fin 1 => a) = ratV F (fun _ : Fin 1 => b) from funext fun _ => hab)) 0
  have key : ∀ p ∈ ratPts σ J, ∃ M : Matrix (Fin n) (Fin n) E,
      (matHom _ σ J p).1 = M.map (inclR (F := F) (AF F)) := by
    intro p hp
    have hp2 : (p.1 : GL (Fin n) (AF F ⊗[F] E)) ∈
        Subgroup.map (Formalism.UG.bc (inclR (F := F) (AF F))) (Formalism.UG.UJ (σ : E →+* E) J) := hp
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 hp2
    refine ⟨g.1, ?_⟩
    rw [show (matHom _ σ J p).1 = ((p.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) _) from rfl, ← hg]
    rfl
  have bmRat : ∀ p ∈ ratPts σ J, ∃ M : Matrix (Fin r) (Fin r) E,
      Bm σ J X Y p = M.map (inclR (F := F) (AF F)) := by
    intro p hp
    obtain ⟨M, hM⟩ := key p hp
    refine ⟨cT (σ : E →+* E) Y * J * (M * X), ?_⟩
    rw [Bm, coefM, hM, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, PositivityTheory.ThKR.cT_map_inclR]
    rfl
  have hrow : ∀ C : Matrix (Fin n) (Fin r) E,
      cT (sigR (AF F) σ) (adMat F C) * JR (AF F) J = (cT (σ : E →+* E) C * J).map (inclR (F := F) (AF F)) := by
    intro C
    rw [Matrix.map_mul, PositivityTheory.ThKR.cT_map_inclR]
    rfl
  have hP : ∀ (C D : Matrix (Fin n) (Fin r) E) (i : Fin r),
      (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
        Matrix.vecMulVec (fun k => adMat F C k i)
          ((cT (sigR (AF F) σ) (adMat F D) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) i) := by
    intro C D i
    rw [hrow]
    ext a b
    simp only [lineProj, rowOf, Matrix.vecMulVec_apply, Matrix.map_apply, adMat, map_mul]
  have hX := mul_eq_mul_diagonal_of_comm (G := (matHom _ σ J γ).1) hF.yx (fun i => by
    have := hcomm (Sum.inl i)
    rwa [projFam, Sum.elim_inl, hP] at this)
  have hY := mul_eq_mul_diagonal_of_comm (G := (matHom _ σ J γ).1) hF.xy (fun i => by
    have := hcomm (Sum.inr i)
    rwa [projFam, Sum.elim_inr, hP] at this)
  refine ⟨⟨_, _, hX, hY⟩, ⟨Matrix.diagonal _, Matrix.blockTriangular_diagonal _, hX, fun i => ?_⟩⟩
  have hp : γ ∈ minPar σ J X := ⟨_, Matrix.blockTriangular_diagonal _, hX⟩
  have hp' := inv_mem_minPar h hJ hW hp
  refine ⟨uU σ J X Y h hJ hW hp hp' i, ?_, ?_⟩
  · rw [val_uU h hJ hW hp hp' i, Bm_eq hF hX]
  · obtain ⟨M, hM⟩ := bmRat γ hγ
    obtain ⟨M', hM'⟩ := bmRat γ⁻¹ (inv_mem hγ)
    have hu1 : ((uU σ J X Y h hJ hW hp hp' i : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (F := F) (AF F) (M i i) := by
      rw [val_uU h hJ hW hp hp' i, hM]
      rfl
    have hu2 : (((uU σ J X Y h hJ hW hp hp' i)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (F := F) (AF F) (M' i i) := by
      show Bm σ J X Y γ⁻¹ i i = _
      rw [hM']
      rfl
    have he : M i i * M' i i = 1 := hinj (by rw [map_mul, ← hu1, ← hu2, Units.mul_inv, map_one])
    have he' : M' i i * M i i = 1 := by rw [mul_comm]; exact he
    have hu : uU σ J X Y h hJ hW hp hp' i =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* AF F ⊗[F] E) ⟨M i i, M' i i, he, he'⟩ :=
      Units.ext (by rw [hu1]; rfl)
    rw [hu]
    exact GlobalTheory.Doubling.absE_inclR _

end GlobalTheory.CompanionTheory.ParCocompact

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLeviMinimalOfCommutesProjectionsStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.mem_levi_minimal_of_commutes_projections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ leviMin σ J X Y ∧ γ ∈ minParOne σ J X := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm | exact GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompact

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem levi_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ C ⊆ leviMin σ J X Y ∩ minParOne σ J X ∧ ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∃ δ ∈ ratPts σ J, δ ∈ leviMin σ J X Y ∧ ∃ c ∈ C, m = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨L, hL, hLc⟩ := GlobalTheory.T.levi_parabolic_intersection_closed F E σ h n J hJ r X Y hW
  have hmem : ∀ g, g ∈ L ↔ g ∈ leviMin σ J X Y ∧ g ∈ minParOne σ J X := fun g => by
    rw [← SetLike.mem_coe, hL]; rfl
  obtain ⟨ε, hε, hh⟩ := GlobalTheory.T.idele_bound_of_joint_anisotropic F E σ h n J hJ _ (hermFam σ J X Y) (L : Set (GAd σ J))
    (GlobalTheory.T.hermitian_family_anisotropic_joint F E σ h n J hJ r X Y hW)
    (fun g hg j => GlobalTheory.T.levi_minimal_idele_hermitian_bound F E σ h n J hJ r X Y hW g ((hmem g).1 hg).1 ((hmem g).1 hg).2 j)
  obtain ⟨Ω, hΩ, hsub, hred⟩ := GlobalTheory.T.commutant_closed_subgroup_compact_quotient F E σ h n J hJ _ (projFam σ J X Y) L hLc
    (fun g hg k => GlobalTheory.T.levi_minimal_commutes_projection_family F E σ h n J hJ r X Y hW g ((hmem g).1 hg).1 k) ⟨ε, hε, hh⟩
    (fun γ hγ hc => (hmem γ).2 (GlobalTheory.T.mem_levi_minimal_of_commutes_projections F E σ h n J hJ r X Y hW γ hγ hc))
  refine ⟨Ω, hΩ, fun c hc => (hmem c).1 (hsub hc), fun m hm hm1 => ?_⟩
  obtain ⟨δ, hδ, hδL, hd⟩ := hred m ((hmem m).2 ⟨hm, hm1⟩)
  exact ⟨δ, hδ, ((hmem δ).1 hδL).1, _, hd, by group⟩

theorem minParOne_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ ∀ p ∈ minParOne σ J X, ∃ δ ∈ ratPts σ J, δ ∈ minPar σ J X ∧ ∃ ω ∈ Ω, p = δ * ω := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨hcl, hmul⟩ := minParOne_props h hJ hW
  obtain ⟨C, hC, hU⟩ := GlobalTheory.CompanionTheory.UnipCocompact.unipMin_cocompact F E σ h n J hJ r X Y hW
  obtain ⟨C', hC', hsub, hM⟩ := levi_cocompact F E σ h n J hJ r X Y hW
  refine ⟨(C ∩ minParOne σ J X) * C', (hC.inter_right hcl).mul hC', ?_, fun p hp => ?_⟩
  · rintro _ ⟨c, hc, c', hc', rfl⟩
    exact hmul _ hc.2 _ (hsub hc').2
  · obtain ⟨u, hu, m, hm, hm1, rfl⟩ := GlobalTheory.T.minimal_parabolic_levi_decomposition F E σ h n J hJ r X Y hW p hp
    obtain ⟨δ, hδ, hδL, c', hc', rfl⟩ := hM m hm hm1
    have hu' := GlobalTheory.T.levi_normalizes_unipotent_ter F E σ h n J hJ r X Y hW δ hδL u hu
    obtain ⟨δ', hδ', hδU, c, hc, hcU, e⟩ := hU _ hu'
    refine ⟨δ * δ', mul_mem hδ hδ', mul_mem_minPar (leviMin_subset X Y hδL)
      (minParOne_subset (unipMin_subset_minParOne X hδU)), c * c',
      ⟨c, ⟨hc, unipMin_subset_minParOne X hcU⟩, c', hc', rfl⟩, ?_⟩
    have e2 : u = δ * (δ' * c) * δ⁻¹ := by
      rw [← e]; group
    rw [e2]; group

end GlobalTheory.CompanionTheory.ParCocompact

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompactStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.minimal_parabolic_rational_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ ∀ p ∈ minParOne σ J X, ∃ δ ∈ ratPts σ J, δ ∈ minPar σ J X ∧ ∃ ω ∈ Ω, p = δ * ω := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact | exact GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact <;> assumption)
end
end
