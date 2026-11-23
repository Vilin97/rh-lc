module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.DualLattices.FischerAdjointStatement
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsStableSubmoduleTopWeightLine
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.DualLattices.ConstantCoeffRowSubst
public import ReciprocityTheory.DualLattices.FischerSelfNeZero
import ReciprocityTheory.DualLattices.FischerSmulRight

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerIrreducibleUnitaryHighestWeight

section

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.HighestWeightMap

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_line {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

end

theorem raising_eq_zero {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} (E : Fin k → Fin k → Module.End ℂ W) (Δ : W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z →
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) Δ) (∑ a, ∑ b, Z a b • E a b Δ) 0)
    (hd : DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) Δ)
      (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j))
    {a b : Fin k} (hab : ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) : E a b Δ = 0 := by
  obtain ⟨D, hD⟩ := hd
  let Φ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W :=
    { toFun := fun Z => ∑ a, ∑ b, Z a b • E a b Δ
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, mul_smul] }
  let Ψ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] W :=
    { toFun := fun Z => D fun i j => Z i j
      map_add' := fun x y => D.map_add x y
      map_smul' := fun c x => D.map_smul c x }
  have hskew : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → Φ Z = Ψ Z := by
    intro Z hZ
    have h1 : HasDerivAt (fun t : ℝ => fun i j => NormedSpace.exp ((t : ℂ) • Z) i j) (fun i j => Z i j) 0 :=
      hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_exp_line Z i j
    have h2 := (hD.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 h1 (by simp)
    exact (hE Z hZ).unique h2
  have hall : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Φ Z = Ψ Z := by
    intro Z
    have e : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + (-Complex.I / 2) • (Complex.I • (Z + Zᴴ)) := by
      have : -Complex.I / 2 * Complex.I = 1 / 2 := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      rw [smul_smul, this]
      module
    have s1 := hskew (Z - Zᴴ) (by simp)
    have s2 := hskew (Complex.I • (Z + Zᴴ)) (by simp [conjTranspose_smul, add_comm])
    rw [e, map_add (f := _), map_add (f := _), map_smul, map_smul (Ψ), s1, map_smul Φ (-Complex.I / 2), map_smul Ψ (-Complex.I / 2), s2]
  have h3 : Φ (Matrix.single a b 1) = E a b Δ := by
    show ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • E c d Δ = _
    simp [Matrix.single_apply, ite_and, ite_smul]
  have h4 : HasDerivAt (fun s : ℂ => fun i j => (1 + Matrix.single a b s : Matrix (Fin k) (Fin k) ℂ) i j)
      (fun i j => Matrix.single a b (1 : ℂ) i j) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [Matrix.add_apply, Matrix.single_apply]
    split_ifs
    · exact (hasDerivAt_id' _).const_add _
    · exact hasDerivAt_const _ _
  have h5 : HasDerivAt (fun s : ℂ => π (1 + Matrix.single a b s) Δ) (Ψ (Matrix.single a b 1)) 0 :=
    hD.comp_hasDerivAt_of_eq 0 h4 (by
      funext i j
      show _ = (1 : Matrix (Fin k) (Fin k) ℂ) i j + Matrix.single a b (0 : ℂ) i j
      simp)
  simp only [hab] at h5
  rw [← h3, hall, h5.unique (hasDerivAt_const _ _)]


open Formalism.REAL in
theorem exists_lie_map {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [NormedAddCommGroup V₂]
    [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] {n : ℕ}
    (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ)
    (v₁ : V₁) (v₂ : V₂) (hE₁ : GlRel E₁) (hE₂ : GlRel E₂)
    (hU : ∀ a b x y, ⟪E₂ a b x, y⟫_ℂ = ⟪x, E₂ b a y⟫_ℂ)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw₁ : IsHW E₁ ν v₁) (hw₂ : IsHW E₂ ν v₂) (hv₁ : v₁ ≠ 0) :
    ∃ L : V₁ →ₗ[ℂ] V₂, (∀ a b x, L (E₁ a b x) = E₂ a b (L x)) ∧ L v₁ = v₂ := by
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  let K : Submodule ℂ V₂ := S.comap (LinearMap.inr ℂ V₁ V₂)
  have hK : ∀ a b, ∀ x ∈ K, E₂ a b x ∈ K := fun a b x hx => by
    have := hS a b _ hx
    simpa [hEap, K] using this
  have hK' : ∀ a b, ∀ x ∈ Kᗮ, E₂ a b x ∈ Kᗮ := fun a b x hx =>
    (Submodule.mem_orthogonal _ _).2 fun u hu => by
      rw [← hU]
      exact (Submodule.mem_orthogonal _ _).1 hx _ (hK _ _ _ hu)
  have hv₂ : v₂ ∈ Kᗮ := by
    obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal v₂
    have hyw : ∀ a, E₂ a a y = ν a • y := fun a => by
      have e := hw₂.1 a
      rw [hyz, map_add (f := _), smul_add] at e
      have e' : E₂ a a y - ν a • y = -(E₂ a a z - ν a • z) := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, e, add_comm]
      rw [← sub_eq_zero]
      refine Submodule.disjoint_def.1 K.orthogonal_disjoint _ (K.sub_mem (hK _ _ _ hy) (K.smul_mem _ hy)) ?_
      rw [e']
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (hK' _ _ _ hz) (Submodule.smul_mem _ _ hz))
    obtain ⟨c, hc⟩ := htop (0, y) hy fun a => by simp [hEap, hyw]
    have hc1 : (0 : V₁) = c • v₁ := congrArg Prod.fst hc
    have hc2 : y = c • v₂ := congrArg Prod.snd hc
    rw [(smul_eq_zero.1 hc1.symm).resolve_right hv₁, zero_smul] at hc2
    rw [hyz, hc2, zero_add]
    exact hz
  let T : Submodule ℂ (V₁ × V₂) := S ⊓ Kᗮ.comap (LinearMap.snd ℂ V₁ V₂)
  have hT : ∀ a b, ∀ x ∈ T, E a b x ∈ T := fun a b x hx => ⟨hS a b x hx.1, hK' a b _ hx.2⟩
  have hvT : (v₁, v₂) ∈ T := ⟨hvS, hv₂⟩
  have hb : Function.Bijective ((LinearMap.fst ℂ V₁ V₂).comp T.subtype) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨⟨x, y⟩, hx⟩ h0
      obtain rfl : x = 0 := h0
      obtain rfl : y = 0 := Submodule.disjoint_def.1 K.orthogonal_disjoint y hx.1 hx.2
      rfl
    · rcases h₁ (T.map (LinearMap.fst ℂ V₁ V₂)) (by
        rintro a b _ ⟨x, hx, rfl⟩
        exact ⟨E a b x, hT a b x hx, rfl⟩) with h | h
      · have hm : v₁ ∈ T.map (LinearMap.fst ℂ V₁ V₂) := ⟨_, hvT, rfl⟩
        rw [h] at hm
        exact absurd hm hv₁
      · intro y
        have hm : y ∈ T.map (LinearMap.fst ℂ V₁ V₂) := by rw [h]; trivial
        obtain ⟨x, hx, rfl⟩ := hm
        exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨((LinearMap.snd ℂ V₁ V₂).comp T.subtype).comp (LinearEquiv.ofBijective _ hb).symm.toLinearMap, ?_, ?_⟩
  · intro a b x
    obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ hb).surjective x
    have h : E₁ a b (LinearEquiv.ofBijective _ hb y)
        = LinearEquiv.ofBijective _ hb ⟨E a b y, hT a b y y.2⟩ := rfl
    rw [h]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  · have h : v₁ = LinearEquiv.ofBijective _ hb ⟨(v₁, v₂), hvT⟩ := rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, (LinearEquiv.symm_apply_eq _).2 h]
    rfl


open Formalism.MainNotions.S in
theorem exists_intertwiner : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (Δ : E), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ Λ ⊤ → IsURepOn (UJset (allPos k)) π → (∀ w : E, DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w) (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j)) → Δ ≠ 0 → (∀ a b : Fin k, a < b → ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) → IsWtOn (Formalism.REAL.Kset (allPos k)) π Λ Δ → ∃ L : H →ₗ[ℂ] E, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = π g (L u)) ∧ ∃ v, L v = Δ := by
  intro k Λ H _ _ _ τ E _ _ _ π Δ hτ hK hπ hd _ hup hwt
  have : Nontrivial H := by
    obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
    exact nontrivial_of_ne v 0 hv
  have hτ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) τ := hτ
  have hπ' : PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π := hπ
  obtain ⟨E₁, g₁, d₁, i₁, x₁, hx₁, w₁⟩ :=
    GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest (Λ := Λ) hτ' hK
  obtain ⟨E₂, g₂, u₂, d₂⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k E π hπ'
  have w₂ : Formalism.REAL.IsHW E₂ (fun a => (Λ a : ℂ)) Δ :=
    ⟨GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E₂ d₂ Λ Δ hwt,
      fun a b hab => raising_eq_zero E₂ Δ (fun Z hZ => d₂ Z hZ Δ) (hd Δ) (hup a b hab)⟩
  obtain ⟨L, hL, hLx⟩ := exists_lie_map E₁ E₂ _ x₁ Δ g₁ g₂
    (fun a b x y => by simpa [Formalism.REAL.sgn, PI.UpqRep.allPos] using u₂ a b x y) i₁ w₁ w₂ hx₁
  refine ⟨L, fun g hg x => ?_, x₁, hLx⟩
  obtain ⟨Y, hY, hg', -⟩ := Formalism.REAL.compact_exponential_surjective k (PI.UpqRep.allPos k) g
    ((GlobalTheory.UnitaryHighestWeight.mem_K_iff g).2 hg)
  have hZ : Yᴴ = -Y := by
    have h : Yᴴ * PI.UpqRep.Jm (PI.UpqRep.allPos k) + PI.UpqRep.Jm (PI.UpqRep.allPos k) * Y = 0 := hY.1
    rw [GlobalTheory.UnitaryHighestWeight.Jm_allPos, Matrix.mul_one, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := GlobalTheory.UnitaryHighestWeightUnique.intertwine_group
    (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₁ a b)
    (GlobalTheory.UnitaryHighestWeight.group_zero hτ' _) (GlobalTheory.UnitaryHighestWeight.group_add hτ' hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using d₁ _ hZ w)
    (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E₂ a b)
    (GlobalTheory.UnitaryHighestWeight.group_zero hπ' _) (GlobalTheory.UnitaryHighestWeight.group_add hπ' hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using d₂ _ hZ w)
    L (fun w => by simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hL]) x 1
  simpa [hg'] using h

end GlobalTheory.HighestWeightMap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerIrreducibleUnitaryHighestWeightStatement

section

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_intertwiner_with_highestWeight_vector_in_range : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (Δ : E), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ Λ ⊤ → IsURepOn (UJset (allPos k)) π → (∀ w : E, DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w) (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j)) → Δ ≠ 0 → (∀ a b : Fin k, a < b → ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) → IsWtOn (Formalism.REAL.Kset (allPos k)) π Λ Δ → ∃ L : H →ₗ[ℂ] E, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = π g (L u)) ∧ ∃ v, L v = Δ := by
  first | exact @GlobalTheory.HighestWeightMap.exists_intertwiner | exact GlobalTheory.HighestWeightMap.exists_intertwiner | (intros; apply GlobalTheory.HighestWeightMap.exists_intertwiner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupIntertwinerOfHighestWeightPoly

section

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HighestPolynomial

open MvPolynomial ReciprocityTheory.PGsh

theorem differentiable_rowSubst {k : ℕ} {κ : Type} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : MvPolynomial (Fin k × κ) ℂ) (ψ : MvPolynomial (Fin k × κ) ℂ →ₗ[ℂ] F) :
    Differentiable ℂ fun g : Fin k → Fin k → ℂ => ψ (rowSubst (Matrix.of g) P) := by
  induction P using MvPolynomial.induction_on generalizing ψ with
  | C c => simp only [rowSubst_C]; exact differentiable_const _
  | add p q hp hq => simp only [map_add (f := _)]; exact (hp ψ).add (hq ψ)
  | mul_X p s hp =>
    have h : (fun g : Fin k → Fin k → ℂ => ψ (rowSubst (Matrix.of g) (p * X s))) =
        fun g : Fin k → Fin k → ℂ => ∑ l, g l s.1 •
          (ψ ∘ₗ LinearMap.mulRight ℂ (X (l, s.2))) (rowSubst (Matrix.of g) p) := by
      funext g

      rw [map_mul, rowSubst_X, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ← map_smul, MvPolynomial.smul_eq_C_mul, Matrix.of_apply]
      congr 1
      ring
    rw [h]
    refine Differentiable.fun_sum fun l _ => Differentiable.smul ?_ (hp _)
    fun_prop

theorem totalDegree_rowSubst_le {k : ℕ} {κ : Type} (g : Matrix (Fin k) (Fin k) ℂ)
    (P : MvPolynomial (Fin k × κ) ℂ) : (rowSubst g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

theorem fischer_conj {k : ℕ} {κ : Type} (P Q : MvPolynomial (Fin k × κ) ℂ) :
    starRingEnd ℂ (fischer P Q) = fischer Q P := by
  classical

  rw [fischer_eq_sum P Q (P.support ∪ Q.support) Finset.subset_union_left,
  fischer_eq_sum Q P (P.support ∪ Q.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fischer_self_re_nonneg {k : ℕ} {κ : Type} (P : MvPolynomial (Fin k × κ) ℂ) : 0 ≤ (fischer P P).re := by
  rw [fischer_eq_sum P P P.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

@[reducible] def fischerCore {k : ℕ} {κ : Type} (S : Submodule ℂ (MvPolynomial (Fin k × κ) ℂ)) :
    InnerProductSpace.Core ℂ S where
  inner x y := fischer y.1 x.1
  conj_inner_symm x y := fischer_conj _ _
  re_inner_nonneg x := fischer_self_re_nonneg _
  add_left x y z := fischer_add_right _ _ _
  smul_left x y r := fischer_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fischer_self_ne_zero x.1 (fun h' => h (Subtype.ext h')) hx

theorem mem_UJset_allPos {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : gᴴ * g = 1 := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  have h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) := hg
  rwa [hJ, Matrix.mul_one] at h

theorem exists_intertwiner_of_embedding (k : ℕ) (κ : Type) (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (j : E →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ) (hj : Function.Injective j)
    (hin : ∀ x y : E, inner ℂ x y = fischer (j y) (j x))
    (hst : ∀ g x, ∃ y, j y = rowSubst g (j x)) (D : E)
    (hτ : IsURepOn (UJset (allPos k)) τ) (hK : IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤) (hD : j D ≠ 0)
    (hu : ∀ g, IsUpperUnitri g → rowSubst g (j D) = j D)
    (hd : ∀ d : Fin k → ℂ, rowSubst (Matrix.diagonal d) (j D) = (∏ a, d a ^ ν a) • j D) :
    ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ,
      (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = rowSubst g (L u)) ∧ ∃ v, L v = j D := by
  obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hrj : ∀ x, r (j x) = x := fun x => LinearMap.congr_fun hr x
  let π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E) := fun g =>
    LinearMap.toContinuousLinearMap (r ∘ₗ (rowSubst g).toLinearMap ∘ₗ j)
  have hπ : ∀ g x, π g x = r (rowSubst g (j x)) := fun g x => rfl
  have hjπ : ∀ g x, j (π g x) = rowSubst g (j x) := by
    intro g x
    obtain ⟨y, hy⟩ := hst g x
    rw [hπ, ← hy, hrj]
  have hdiff : ∀ w : E, Differentiable ℂ fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w := fun w =>
    differentiable_rowSubst (j w) r
  have hrep : IsURepOn (UJset (allPos k)) π := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · ext x
      apply hj
      rw [hjπ, rowSubst_one]
      rfl
    · intro a _ b _
      ext x
      apply hj
      change _ = j (π a (π b x))
      rw [hjπ, hjπ, hjπ, rowSubst_mul]
    · intro g hg v
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ v, hin, hin, hjπ, fischer_rowSubst,
        rowSubst_mul, mem_UJset_allPos hg, rowSubst_one]
    · intro v
      exact (hdiff v).continuous.continuousOn
  obtain ⟨L, hL, v, hv⟩ := GlobalTheory.T.exists_intertwiner_with_highestWeight_vector_in_range k (fun a => (ν a : ℝ)) H τ E π D hτ hK hrep (fun w => hdiff w _)
    (fun h => hD (by rw [h, map_zero]))
    (by
      intro a b hab s
      apply hj
      rw [hjπ]
      refine hu _ ⟨fun i => ?_, fun i l hl => ?_⟩
      · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, h2⟩
        exact hab.ne (h1.trans h2.symm)
      · rw [Matrix.add_apply, Matrix.one_apply_ne hl.ne', Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, h2⟩
        subst h1 h2
        exact lt_asymm hab hl)
    (by
      intro θ _
      apply hj
      rw [hjπ, hd, map_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← Complex.exp_nat_mul, mul_assoc])
  exact ⟨j ∘ₗ L, fun g hg u => by rw [LinearMap.comp_apply, hL g hg, hjπ]; rfl, v, by rw [LinearMap.comp_apply, hv]⟩

theorem exists_intertwiner : ∀ (k : ℕ) (κ : Type) [Fintype κ] (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (Δ : MvPolynomial (Fin k × κ) ℂ), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤ → Δ ≠ 0 → (∀ g, ReciprocityTheory.PGsh.IsUpperUnitri g → ReciprocityTheory.PGsh.rowSubst g Δ = Δ) → (∀ d : Fin k → ℂ, ReciprocityTheory.PGsh.rowSubst (Matrix.diagonal d) Δ = (∏ a, d a ^ ν a) • Δ) → ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = ReciprocityTheory.PGsh.rowSubst g (L u)) ∧ ∃ v, L v = Δ := by
  intro k κ _ ν H _ _ _ τ Δ hτ hK hΔ hu hd
  let S : Submodule ℂ (MvPolynomial (Fin k × κ) ℂ) := restrictTotalDegree (Fin k × κ) ℂ Δ.totalDegree
  have hfin : FiniteDimensional ℂ S := inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Fin k × κ) ℂ Δ.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fischerCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  exact exists_intertwiner_of_embedding k κ ν H τ S S.subtype S.injective_subtype (fun _ _ => rfl)
    (fun g x => ⟨⟨rowSubst g x.1, (mem_restrictTotalDegree _ _ _).mpr
      ((totalDegree_rowSubst_le g x.1).trans ((mem_restrictTotalDegree _ _ _).mp x.2))⟩, rfl⟩)
    ⟨Δ, (mem_restrictTotalDegree _ _ _).mpr le_rfl⟩ hτ hK hΔ hu hd

end GlobalTheory.HighestPolynomial

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupIntertwinerOfHighestWeightPolyStatement

section

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial : ∀ (k : ℕ) (κ : Type) [Fintype κ] (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (Δ : MvPolynomial (Fin k × κ) ℂ), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤ → Δ ≠ 0 → (∀ g, ReciprocityTheory.PGsh.IsUpperUnitri g → ReciprocityTheory.PGsh.rowSubst g Δ = Δ) → (∀ d : Fin k → ℂ, ReciprocityTheory.PGsh.rowSubst (Matrix.diagonal d) Δ = (∏ a, d a ^ ν a) • Δ) → ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = ReciprocityTheory.PGsh.rowSubst g (L u)) ∧ ∃ v, L v = Δ := by
  first | exact @GlobalTheory.HighestPolynomial.exists_intertwiner | exact GlobalTheory.HighestPolynomial.exists_intertwiner | (intros; apply GlobalTheory.HighestPolynomial.exists_intertwiner <;> assumption)
end
end
