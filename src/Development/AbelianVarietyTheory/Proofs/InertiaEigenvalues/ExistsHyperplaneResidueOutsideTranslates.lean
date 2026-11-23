module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueAnnihilatorOfNotStandardColumnFormAStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.ToLin

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrMatrixProjPreimage

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem dvr_matrix_proj_preimage (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n]
    (S : Submodule K (n → K)) :
    ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧
      ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  classical
  let f : (n → O) →ₗ[O] (n → K) := LinearMap.compLeft (Algebra.linearMap O K) n
  let U : Submodule O (n → O) := (S.restrictScalars O).comap f
  have hmem : ∀ v : n → O, v ∈ U ↔ (fun i => algebraMap O K (v i)) ∈ S := fun v => Iff.rfl
  have htf : NoZeroSMulDivisors O ((n → O) ⧸ U) := by
    constructor
    intro c x hcx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U x
    by_cases hc : c = 0
    · left; exact hc
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcx
    rw [Submodule.Quotient.mk_eq_zero]
    rw [hmem] at hcx ⊢
    have e : (fun i => algebraMap O K ((c • v) i)) = algebraMap O K c • (fun i => algebraMap O K (v i)) := by
      funext i; simp [Algebra.smul_def]
    rw [e] at hcx
    have hc' : algebraMap O K c ≠ 0 := by
      intro h; exact hc ((IsFractionRing.injective O K) (by rw [h, map_zero]))
    have := S.smul_mem (algebraMap O K c)⁻¹ hcx
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
  haveI : Module.Free O ((n → O) ⧸ U) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective O ((n → O) ⧸ U) := Module.Projective.of_free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property U.mkQ LinearMap.id (Submodule.mkQ_surjective U)
  let π : (n → O) →ₗ[O] (n → O) := LinearMap.id - s ∘ₗ U.mkQ
  have hπU : ∀ v, π v ∈ U := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (U.mkQ v)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply U (s _), this, Submodule.mkQ_apply, sub_self]
  have hπfix : ∀ u ∈ U, π u = u := by
    intro u hu
    have h0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hu
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]
  refine ⟨LinearMap.toMatrix' π, ?_, ?_⟩
  · intro v
    rw [LinearMap.toMatrix'_mulVec]
    exact hπU v
  · intro u hu
    rw [LinearMap.toMatrix'_mulVec]
    exact hπfix u hu

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrMatrixProjPreimageStatement

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.dvr_matrix_proj_preimage_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n] (S : Submodule K (n → K)), ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧ ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  first | exact @GlobalTheory.dvr_matrix_proj_preimage | exact GlobalTheory.dvr_matrix_proj_preimage | (intros; apply GlobalTheory.dvr_matrix_proj_preimage <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlFactorFromBlocksModUniformizer

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem gl_factor_fromBlocks_mod_uniformizer : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (g : GL (Fin r) (IsLocalRing.ResidueField O)) (L : Matrix (Fin r) (Fin r) O), L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∀ (B : Matrix (Fin r) (Fin t) O) (q : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O), (∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O) i j)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) = q := by
  intro O _ _ _ r t ϖ hϖ g L hL B q hq
  classical
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hmem : ∀ x : O, IsLocalRing.residue O x = 0 → x ∈ Ideal.span {ϖ} := fun x hx =>
    hmax ▸ (IsLocalRing.residue_eq_zero_iff x).mp hx
  have hg : IsUnit (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hLdet : IsLocalRing.residue O L.det = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hL]
  have hLu : IsUnit L.det :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hLdet]; exact hg.ne_zero)
  set D : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L 0 0 1 with hDdef
  have hDu : IsUnit D.det := by
    rw [hDdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact hLu
  have hqmap : q.map (IsLocalRing.residue O) =
      (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O)).map (IsLocalRing.residue O) := by
    ext i j; exact hq i j
  have hqu : IsUnit q.det := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hqmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, hLdet]
    exact hg.ne_zero
  have hHu : IsUnit (q * D⁻¹).det := by
    rw [Matrix.det_mul]; exact hqu.mul (Matrix.isUnit_nonsing_inv_det D hDu)
  have hHD : q * D⁻¹ * D = q := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDu, Matrix.mul_one]
  have hMD : (q * D⁻¹).map (IsLocalRing.residue O) * D.map (IsLocalRing.residue O) =
      q.map (IsLocalRing.residue O) := by
    rw [← Matrix.map_mul, hHD]
  rw [hqmap, ← Matrix.fromBlocks_toBlocks ((q * D⁻¹).map (IsLocalRing.residue O)), hDdef,
    Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hMD
  obtain ⟨h11, -, h21, -⟩ := hMD
  simp only [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, add_zero, hL] at h11 h21
  have e11 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₁₁ = 1 := by
    have := congrArg (· * ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _)) h11
    simpa [Matrix.mul_assoc] using this
  have e21 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₂₁ = 0 := by
    have hgg : (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) *
        ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _) = 1 := Units.mul_inv g
    rw [hDdef, ← Matrix.mul_one (Matrix.toBlocks₂₁ _), ← hgg, ← Matrix.mul_assoc, h21, Matrix.zero_mul]
  refine ⟨Matrix.nonsingInvUnit (q * D⁻¹) hHu, ?_, ?_, hHD⟩
  · intro i j
    apply hmem
    have := congrFun (congrFun e11 i) j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.map_apply] at this
    show IsLocalRing.residue O ((q * D⁻¹) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j) = 0
    rw [map_sub, this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro i j
    show (q * D⁻¹) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}
    apply hmem
    have := congrFun (congrFun e21 i) j
    simpa [Matrix.toBlocks₂₁] using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlFactorFromBlocksModUniformizerStatement

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.gl_factor_fromBlocks_mod_uniformizer_alt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (g : GL (Fin r) (IsLocalRing.ResidueField O)) (L : Matrix (Fin r) (Fin r) O), L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∀ (B : Matrix (Fin r) (Fin t) O) (q : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O), (∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O) i j)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) = q := by
  first | exact @GlobalTheory.gl_factor_fromBlocks_mod_uniformizer | exact GlobalTheory.gl_factor_fromBlocks_mod_uniformizer | (intros; apply GlobalTheory.gl_factor_fromBlocks_mod_uniformizer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTopFactorThroughBottom

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem residue_top_factor_through_bottom : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t : ℕ) (U : Submodule O (Fin r ⊕ Fin t → O)) (a : Fin r → IsLocalRing.ResidueField O), (∀ u ∈ U, (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0) → ∀ g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → g.mulVec v = v) → ∃ b : Matrix (Fin r) (Fin t) (IsLocalRing.ResidueField O), ∀ u ∈ U, g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) + b.mulVec (fun i => IsLocalRing.residue O (u (Sum.inr i))) = (fun i => IsLocalRing.residue O (u (Sum.inl i))) := by
  intro O _ _ r t U a ha g hg
  let res : (Fin r ⊕ Fin t → O) → (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) :=
    fun u j => IsLocalRing.residue O (u j)
  let Wsp : Submodule (IsLocalRing.ResidueField O) (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) :=
    { carrier := {w | ∃ u ∈ U, res u = w}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, U.add_mem hu hv, by ext j; simp [res]⟩
      zero_mem' := ⟨0, U.zero_mem, by ext j; simp [res]⟩
      smul_mem' := by
        rintro c _ ⟨u, hu, rfl⟩
        obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨o • u, U.smul_mem o hu, by ext j; simp [res]⟩ }
  let top : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    LinearMap.funLeft _ _ Sum.inl
  let bot : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O) :=
    LinearMap.funLeft _ _ Sum.inr
  let π : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O) := bot.comp Wsp.subtype
  let f : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    (LinearMap.id - Matrix.toLin' g).comp (top.comp Wsp.subtype)
  have hker : LinearMap.ker π ≤ LinearMap.ker f := by
    rintro ⟨w, u, hu, rfl⟩ hw
    rw [LinearMap.mem_ker] at hw ⊢
    have h2 : ∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0 := fun i => congrFun hw i
    have h3 := hg _ (ha u hu h2)
    simp only [f, top, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Matrix.toLin'_apply]
    rw [sub_eq_zero]
    exact h3.symm
  let b₀ : LinearMap.range π →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    ((LinearMap.ker π).liftQ f hker).comp (π.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨B, hB⟩ := LinearMap.exists_extend b₀
  refine ⟨LinearMap.toMatrix' B, ?_⟩
  intro u hu
  have hw : res u ∈ Wsp := ⟨u, hu, rfl⟩
  have key : B (π ⟨res u, hw⟩) = f ⟨res u, hw⟩ := by
    have h1 := LinearMap.congr_fun hB ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    show (LinearMap.ker π).liftQ f hker
      (π.quotKerEquivRange.symm ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have e : π ⟨res u, hw⟩ = fun i => IsLocalRing.residue O (u (Sum.inr i)) := rfl
  have e2 : f ⟨res u, hw⟩ = (fun i => IsLocalRing.residue O (u (Sum.inl i))) -
      g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) := rfl
  rw [e, e2] at key
  rw [LinearMap.toMatrix'_mulVec, key]
  abel

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTopFactorThroughBottomStatement

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.exists_residue_first_block_factor_of_second : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t : ℕ) (U : Submodule O (Fin r ⊕ Fin t → O)) (a : Fin r → IsLocalRing.ResidueField O), (∀ u ∈ U, (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0) → ∀ g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → g.mulVec v = v) → ∃ b : Matrix (Fin r) (Fin t) (IsLocalRing.ResidueField O), ∀ u ∈ U, g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) + b.mulVec (fun i => IsLocalRing.residue O (u (Sum.inr i))) = (fun i => IsLocalRing.residue O (u (Sum.inl i))) := by
  first | exact @GlobalTheory.residue_top_factor_through_bottom | exact GlobalTheory.residue_top_factor_through_bottom | (intros; apply GlobalTheory.residue_top_factor_through_bottom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHyperplaneResidueOutsideTranslates

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem GlobalTheory.gen_type_core : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v) → ∀ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) * x) = x := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ x hx
  obtain ⟨a, ha, hA⟩ := GlobalTheory.T.exists_residue_annihilator_of_not_standard_column_form_alt O K r t ϖ hϖ x hx
  refine ⟨a, ha, fun g hg L hL => ?_⟩
  set S : Submodule K (Fin r ⊕ Fin t → K) := Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) with hS
  let U : Submodule O (Fin r ⊕ Fin t → O) := Submodule.comap ((Algebra.linearMap O K).compLeft (Fin r ⊕ Fin t)) (S.restrictScalars O)
  have hU : ∀ u, u ∈ U ↔ (fun i => algebraMap O K (u i)) ∈ S := fun u => Iff.rfl
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_residue_first_block_factor_of_second O r t U a (fun u hu h2 => hA u ((hU u).1 hu) h2) (g : Matrix (Fin r) (Fin r) _) hg
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.T.dvr_matrix_proj_preimage_alt O K (Fin r ⊕ Fin t) S
  set bt : Matrix (Fin r) (Fin t) O := b.map (Function.surjInv IsLocalRing.residue_surjective) with hbt
  have hbt' : bt.map (IsLocalRing.residue O) = b := by
    ext i j; simp [hbt, Function.surjInv_eq]
  set q₀ : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L bt 0 1 with hq₀

  have key : ∀ u ∈ U, ∀ i, IsLocalRing.residue O (Matrix.mulVec (1 - q₀) u i) = 0 := by
    intro u hu i
    have h1 := hb u hu
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub, sub_eq_zero]
    rw [RingHom.map_mulVec, hq₀, Matrix.fromBlocks_map]
    rw [Matrix.fromBlocks_mulVec]
    rcases i with i | i
    · have := congrFun h1 i
      simp only [Sum.elim_inl, Pi.add_apply] at this ⊢
      rw [hL, hbt']
      simpa [Function.comp_def] using this.symm
    · simp [Function.comp_def]
  have hPx : P * x = x := by
    ext i j
    have := hP2 (fun i => x i j) (Submodule.subset_span ⟨j, rfl⟩)
    exact congrFun this i
  set q := q₀ + (1 - q₀) * P with hq
  have hqx : q * x = x := by
    rw [hq, Matrix.add_mul, Matrix.mul_assoc, hPx, Matrix.sub_mul, Matrix.one_mul]; abel
  have hqq : ∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (q₀ i j) := by
    intro i j
    have hcol : (fun l => P l j) ∈ U := by
      have := hP1 (Pi.single j 1)
      rw [hU]; simpa [Matrix.mulVec_single] using this
    have := key _ hcol i
    rw [hq, Matrix.add_apply, map_add (f := _)]
    have e : ((1 - q₀) * P) i j = Matrix.mulVec (1 - q₀) (fun l => P l j) i := rfl
    rw [e, this, add_zero]
  obtain ⟨h, h1, h2, h3⟩ := GlobalTheory.T.gl_factor_fromBlocks_mod_uniformizer_alt O r t ϖ hϖ g L hL bt q hqq
  exact ⟨h, h1, h2, by rw [← Matrix.mul_assoc, h3, hqx]⟩
end
end
