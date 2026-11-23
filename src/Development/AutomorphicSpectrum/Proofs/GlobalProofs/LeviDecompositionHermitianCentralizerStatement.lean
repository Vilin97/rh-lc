module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompInfRTensorInlA
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspaceStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExtendByZeroApplyOfNeStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryElementPrescribedBlocksStatement
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanUnitaryElementLift

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit

section Lin

variable {A : Type} [CommRing A] {n m : ℕ}

theorem mulVec_eq_of_mem (C : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A) (U : Matrix (Fin m) (Fin n) A)
    (W : Matrix (Fin n) (Fin m) A) (I : Set (Fin m)) (hDC : D * C = 0) (hUC : ∀ i j, j ∈ I → (U * C) i j = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Cᵀ i) '' I)) : (1 + C * U + W * D) *ᵥ y = y := by
  obtain ⟨a, ha, rfl⟩ := (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff C I y).1 hy
  have h1 : (U * C) *ᵥ a = 0 := funext fun i => by
    show ∑ l, (U * C) i l * a l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l ∈ I
    · rw [hUC i l hl, zero_mul]
    · rw [ha l hl, mul_zero]
  have h2 : (1 + C * U + W * D) *ᵥ (C *ᵥ a) = C *ᵥ a + C *ᵥ ((U * C) *ᵥ a) + W *ᵥ ((D * C) *ᵥ a) := by
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec]
  rw [h2, h1, hDC]
  simp

theorem mulVec_sub_mem (C : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A) (U : Matrix (Fin m) (Fin n) A)
    (W : Matrix (Fin n) (Fin m) A) (I : Set (Fin m)) (hU : ∀ i v, i ∉ I → U i v = 0) {y : Fin n → A}
    (hy : W *ᵥ (D *ᵥ y) = 0) : (1 + C * U + W * D) *ᵥ y - y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) := by
  have h : (1 + C * U + W * D) *ᵥ y - y = C *ᵥ (U *ᵥ y) := by
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec, hy]
    abel
  rw [h]
  refine (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff C I _).2 ⟨U *ᵥ y, fun l hl => ?_, rfl⟩
  show ∑ v, U l v * y v = 0
  exact Finset.sum_eq_zero fun v _ => by rw [hU l v hl, zero_mul]

theorem mem_iff_of_fix {M : Matrix (Fin n) (Fin n) A} (hM : Function.Injective M.mulVec) (S : Submodule A (Fin n → A))
    (hS : ∀ y ∈ S, M *ᵥ y = y) (y : Fin n → A) : y ∈ S ↔ M *ᵥ y ∈ S :=
  ⟨fun h => by rwa [hS y h], fun h => by rwa [← hM (hS _ h)]⟩

end Lin

theorem mem_unip {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin m) E) (T : Finset (Fin m)) (g : GAd σ J)
    (U : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) (W : Matrix (Fin n) (Fin m) (AF F ⊗[F] E))
    (hX : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hU : ∀ i v, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → U i v = 0)
    (hW : ∀ v i, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → W v i = 0)
    (hUX : ∀ i j, j ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → (U * GlobalTheory.SiegelSet.adMat F X) i j = 0)
    (hg : (GlobalTheory.AdelicU.matHom _ σ J g).1 =
      1 + GlobalTheory.SiegelSet.adMat F X * U + W * GlobalTheory.SiegelSet.adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) :
    g ∈ GlobalTheory.StdPar.unip σ J X T := by
  have hDC : adMat F (Formalism.UG.cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [adMat, adMat, ← Matrix.map_mul, hX]
    exact Matrix.map_zero _ (map_zero _)
  have hinj : Function.Injective (GlobalTheory.AdelicU.matHom _ σ J g).1.mulVec :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit _)
  have hfix : ∀ y ∈ colSpan F X (upTo T), (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    rw [hg]
    exact mulVec_eq_of_mem _ _ U W _ hDC hUX hy
  have hsub : ∀ y, W *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) = 0 →
      (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y - y ∈ colSpan F X (upTo T) := fun y hy => by
    rw [hg]
    exact mulVec_sub_mem _ _ U W _ hU hy
  have hiff : ∀ S ≤ colSpan F X (upTo T), ∀ y, y ∈ S ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y ∈ S := fun S hS =>
    mem_iff_of_fix hinj S fun y hy => hfix y (hS hy)
  refine ⟨Subgroup.mem_iInf.2 fun j => ?_, hiff _ le_rfl, fun y hy => hsub y ?_⟩
  · by_cases hj : j ∈ upTo T
    · have hA : colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ≤ colSpan F X (upTo T) :=
        Submodule.span_mono (Set.image_mono fun i ⟨k, hk, hik, _⟩ => ⟨k, hk, hik⟩)
      have hB : colSpan F X {j} ≤ colSpan F X (upTo T) :=
        Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj))
      refine ⟨hiff _ hA, fun y hy => ?_⟩
      rw [hfix y (hB hy), sub_self]
      exact zero_mem _
    · have hA : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = upTo T := Set.ext fun i =>
        ⟨fun ⟨k, hk, hik, _⟩ => ⟨k, hk, hik⟩, fun ⟨k, hk, hik⟩ =>
          ⟨k, hk, hik, not_le.1 fun h => hj ⟨k, hk, h⟩⟩⟩
      rw [hA]
      refine ⟨hiff _ le_rfl, fun y hy => hsub y ?_⟩
      obtain ⟨a, -, rfl⟩ := (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff _ _ y).1 hy
      rw [mulVec_mulVec a, hDC, zero_mulVec, mulVec_zero]
  · funext v
    show ∑ i, W v i * (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ upTo T
    · have h : (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0 := by
        simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy
        exact hy i hi
      rw [h, mul_zero]
    · rw [hW v i hi, zero_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanUnitaryElementLiftStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.unitary_adelic_unipotent_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin m) E) (T : Finset (Fin m)) (g : GAd σ J)
    (U : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) (W : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)),
    Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → (∀ i v, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → U i v = 0) →
    (∀ v i, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → W v i = 0) →
    (∀ i j, j ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → (U * GlobalTheory.SiegelSet.adMat F X) i j = 0) →
    (GlobalTheory.AdelicU.matHom _ σ J g).1 = 1 + GlobalTheory.SiegelSet.adMat F X * U + W * GlobalTheory.SiegelSet.adMat F (Formalism.UG.cT (σ : E →+* E) X * J) →
    g ∈ GlobalTheory.StdPar.unip σ J X T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip | exact GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviDecompositionHermitianCentralizer

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem eichler_frame : ∀ {n m : ℕ} (ε : Fin n → Bool) (G Q : Matrix (Fin n) (Fin n) ℂ) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    IsUnit Q → Qᴴ * Formalism.REAL.Jm ε * Q = G → xᴴ * G * x = 0 → xᴴ * G * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * G ∈ Formalism.QuantumDeterminants.UH G ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)) := by
  intro n m ε G Q x y A hQ hG hxx hxy
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have h2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have ex : ∀ z : Matrix (Fin n) (Fin m) ℂ, xᴴ * G * z = (Q * x)ᴴ * Formalism.REAL.Jm ε * (Q * z) := fun z => by
    rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  obtain ⟨u, w, hu, hw, hux, hN, hJ⟩ := GlobalTheory.T.unitary_element_prescribed_blocks ε (Q * x) (Q * y) A (by rw [← ex, hxx]) (by rw [← ex, hxy])
  refine ⟨u * Q, Q⁻¹ * w, fun i v hi => ?_, fun v i hi => ?_, fun i j hj => ?_, ?_⟩
  · simp [Matrix.mul_apply, hu i _ hi]
  · simp [Matrix.mul_apply, hw _ i hi]
  · rw [Matrix.mul_assoc]; exact hux i j hj
  have key : Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) = (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q := by
    rw [← hG, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q⁻¹, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · show _ = _
    have e : (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)ᴴ * G * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) =
        (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G))ᴴ * Formalism.REAL.Jm ε * (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) := by
      rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, key, Matrix.conjTranspose_mul]
    have hN' : _ = _ := hN
    calc Qᴴ * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q)
        = Qᴴ * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)) * Q := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hN', ← hG, Matrix.mul_assoc]
  · have cx : ∀ z : Matrix (Fin n) (Fin m) ℂ, ∀ i : A, (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) *ᵥ (fun j => z j i) =
        (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => (Q * z) j i := fun z i => by
      rw [key, ← Matrix.mulVec_mulVec]
      congr 1
    simp only [cx]
    exact hJ

theorem iwasawa_adapted : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (b : GA D V), ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ b₀ : GA D V, b = n * mm * b₀ ∧ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) := by
  intro D θ hθ V ε fr hfr m X Y hW T b
  classical
  have hQ := isFrameFam_mul_infMat_inv D θ hθ V ε fr hfr b
  let Q : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹
  let x : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => X.map (tauE D τ)
  let y : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => Y.map (tauE D τ)
  have hmap : ∀ τ (Z Z' : Matrix (Fin V.rank) (Fin m) D.host.E), (Z.map (tauE D τ))ᴴ * gramAt D V τ * Z'.map (tauE D τ) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z').map (tauE D τ) := by
    intro τ Z Z'
    have e : (Z.map (tauE D τ))ᴴ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (tauE D τ) := by
      ext i j
      simp [Formalism.UG.cT, GlobalTheory.Mem.Isom.tauE_sig]
    rw [e, gramAt, Matrix.map_mul, Matrix.map_mul]
  have hxx : ∀ τ, (x τ)ᴴ * gramAt D V τ * x τ = 0 := fun τ => by
    rw [hmap, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have hxy : ∀ τ, (x τ)ᴴ * gramAt D V τ * y τ = 1 := fun τ => by
    rw [hmap, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  choose u w hu hw hux hN hJ using fun τ =>
    eichler_frame (ε τ) (gramAt D V τ) (Q τ) (x τ) (y τ) (upTo T) (hQ τ).1 (hQ τ).2 (hxx τ) (hxy τ)
  obtain ⟨g, hg, U, W, hU, hW', hUX, hgM⟩ := GlobalTheory.T.archimedean_unitary_element_lift D θ hθ V X u w hN
  have hgu : g ∈ unip D.sp.cm.sig V.gram X T :=
    GlobalTheory.T.unitary_adelic_unipotent_lift D.sp.cm.sig V.gram X T g U W hW.xx (fun i v hi => hU i v fun τ => hu τ i v hi)
      (fun v i hi => hW' v i fun τ => hw τ v i hi) (fun i j hj => hUX i j fun τ => hux τ i j hj) hgM
  refine ⟨g, hgu, 1, one_mem _, g⁻¹ * b, by rw [mul_one, mul_inv_cancel_left], fun τ => ?_⟩
  have e1 : (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) g := by
    rw [Formalism.L2.Fam.ThC.infMat_mul, Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have e2 : fr τ * (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * (1 + x τ * u τ + w τ * (x τ)ᴴ * gramAt D V τ) := by
    rw [e1, hg τ, ← Matrix.mul_assoc]
  obtain ⟨k, S, hk⟩ := GlobalTheory.T.involution_stable_subspace_coordinate (ε τ) _ (hJ τ)
  refine ⟨k, S, ?_⟩
  beta_reduce
  rw [e2]
  exact hk

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviDecompositionHermitianCentralizerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.langlands_decomposition_unipotent_levi : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (b : GA D V), ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ b₀ : GA D V, b = n * mm * b₀ ∧ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted <;> assumption)
end
end
