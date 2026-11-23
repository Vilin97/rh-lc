module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgebraicModuleOfVanishingBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceAutomorphicProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceCentreOfBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceTypesOfBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicSaturationSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConstantTermLinearMapEquivariantUniversalE
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIdempotentDecompositionMixedSpace
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsBasisAlgModLaplacianOfTypesCentre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalInfKerAevalMonic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
public import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteDimensionalCompactTranslatesOfLevelT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UpperTriangularEqUnipotentMulLevi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSlSpReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SiegelLeviBlockAevalStable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SlSpPreservesGrowthAndLevel
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfBddCuspidal

section

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_bdd_cuspidal :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → (∀ φ ∈ S, IsCuspidal φ.1) → FiniteDimensional ℂ S := by
  intro K _ _ n S hS hcusp
  classical
  have hle : cuspForms K n ≤ archSmooth K n :=
    cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth
  let j : cuspForms K n →ₗ[ℂ] archSmooth K n := Submodule.inclusion hle
  have hj : Function.Injective j := Submodule.inclusion_injective hle
  have hju : ∀ (u : UEnv K n) (ψ : cuspForms K n), j (uActionCusp K n u ψ) = uAction u (j ψ) :=
    fun u ψ => rfl
  have hjf : ∀ (h : AdelicGLn.FiniteAdelicGL K n) (ψ : cuspForms K n),
      j (finRepCusp K n h ψ) = rtFin h (j ψ) := fun h ψ => rfl
  obtain ⟨d, b, P, hPm, hP⟩ := UpperTheory.exists_basis_algMod_laplacian_of_types_centre K n S hS.types hS.centre
  set Z := UnitaryAdmissible.centralZ K n with hZdef
  have hZc : UniversalEnvelopingAlgebra.ι ℝ Z ∈ (isExpLieAlgebra K n).centerU := by
    apply mem_center_of_forall_ι_commute
    intro x
    have h1 := UnitaryAdmissible.lie_centralZ (K := K) (n := n) x
    have h2 : UniversalEnvelopingAlgebra.ι ℝ ⁅Z, x⁆ = UniversalEnvelopingAlgebra.ι ℝ Z * UniversalEnvelopingAlgebra.ι ℝ x - UniversalEnvelopingAlgebra.ι ℝ x * UniversalEnvelopingAlgebra.ι ℝ Z := by
      rw [LieHom.map_lie, Ring.lie_def]
    rw [h1, map_zero] at h2
    exact (sub_eq_zero.mp h2.symm).symm
  obtain ⟨Q, hQm, hQ⟩ := hS.centre _ hZc
  obtain ⟨L, hLo, hL⟩ := hS.level
  let U : Subgroup (AdelicGLn.integralFiniteGL K n) := L.subgroupOf _
  have hUo : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) := hLo.preimage continuous_subtype_val
  have hP'm : (Polynomial.X * P).Monic := Polynomial.monic_X.mul hPm
  have hP'd : 0 < (Polynomial.X * P).natDegree := by
    rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X hPm, Polynomial.natDegree_X]
    omega
  let N : Submodule ℂ (cuspForms K n) :=
    LinearMap.ker (Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (Polynomial.X * P)) ⊓
      ⨅ u : U, LinearMap.ker (finRepCusp K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) - LinearMap.id)
  have hmemN : ∀ ψ, ψ ∈ N ↔ Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (Polynomial.X * P) ψ = 0 ∧
      ∀ u : U, finRepCusp K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) ψ = ψ := by
    intro ψ
    simp only [N, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hTA : ∀ m, uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) (uActionCusp K n (laplacianU K n b) m) =
      uActionCusp K n (laplacianU K n b) (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) m) := by
    intro m
    have hc := (Subalgebra.mem_center_iff.mp hZc) (laplacianU K n b)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hc]
  have hTf : ∀ (h : AdelicGLn.FiniteAdelicGL K n) m,
      uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) (finRepCusp K n h m) =
        finRepCusp K n h (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) m) := by
    intro h m
    apply hj
    rw [hju, hjf, hjf, hju, uAction_rtFin]
  have hTN : ∀ x ∈ N, uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) x ∈ N := by
    intro x hx
    rw [hmemN] at hx ⊢
    refine ⟨?_, fun u => ?_⟩
    · rw [← map_aeval_apply_of_intertwine _ hTA, hx.1, map_zero]
    · rw [← hTf, hx.2 u]
  have hE : ∀ c : ℂ, FiniteDimensional ℂ ↥(N ⊓ (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z)).eigenspace c) := by
    intro c
    refine UnitaryAdmissible.finiteDimensional_of_eigen b _ hP'm hP'd c U hUo _ ?_
    intro φ hφ
    rw [Submodule.mem_inf, hmemN, Module.End.mem_eigenspace_iff] at hφ
    exact ⟨hφ.1.1, hφ.2, fun u hu => hφ.1.2 ⟨u, hu⟩⟩
  have hfin := UpperTheory.finiteDimensional_inf_ker_aeval_monic _ _ N hTN hE Q hQm
  refine Submodule.finiteDimensional_of_le (S₂ := (N ⊓ LinearMap.ker (Polynomial.aeval
    (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z)) Q)).map j) ?_
  intro φ hφ
  have hφc : (φ : AdelicGLn.AdelicGL K n → ℂ) ∈ cuspForms K n :=
    ⟨UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ, hcusp φ hφ⟩
  have hjψ : j ⟨φ.1, hφc⟩ = φ := rfl
  refine ⟨⟨φ.1, hφc⟩, ?_, hjψ⟩
  refine Submodule.mem_inf.mpr ⟨(hmemN _).mpr ⟨?_, fun u => ?_⟩, ?_⟩
  · apply hj
    rw [map_zero, map_aeval_apply_of_intertwine j (hju _), hjψ, map_mul, Polynomial.aeval_X,
      Module.End.mul_apply, (Submodule.mem_bot ℂ).mp (hP φ hφ), map_zero]
  · apply hj
    rw [hjf, hjψ]
    apply Subtype.ext
    funext g
    exact hL φ hφ _ (Subgroup.mem_subgroupOf.mp u.2) g
  · rw [LinearMap.mem_ker]
    apply hj
    rw [map_zero, map_aeval_apply_of_intertwine j (hju _), hjψ]
    exact (Submodule.mem_bot ℂ).mp (hQ φ hφ)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalMapOfSeparatelyFinite

section

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_map_of_separately_finite :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X Y : Type) (S : Submodule ℂ M) (Φ : M →ₗ[ℂ] (X × Y → ℂ)) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → (∀ m ∈ S, ∀ y, (fun x => Φ m (x, y)) ∈ V₁) → (∀ m ∈ S, ∀ x, (fun y => Φ m (x, y)) ∈ V₂) → FiniteDimensional ℂ (S.map Φ) := by
  intro M _ _ X Y S Φ V₁ V₂ h₁ h₂ hrow hcol
  obtain ⟨T, hT⟩ := exists_finset_eval_eq_zero V₁
  have mem : ∀ g ∈ S.map Φ, ∀ x, (fun y => g (x, y)) ∈ V₂ := by
    rintro g ⟨m, hm, rfl⟩ x
    exact hcol m hm x
  have memr : ∀ g ∈ S.map Φ, ∀ y, (fun x => g (x, y)) ∈ V₁ := by
    rintro g ⟨m, hm, rfl⟩ y
    exact hrow m hm y
  let F : S.map Φ →ₗ[ℂ] (T → V₂) :=
    LinearMap.pi fun t => LinearMap.codRestrict V₂
      ((LinearMap.funLeft ℂ ℂ (fun y : Y => ((t : X), y))).comp (S.map Φ).subtype)
      (fun g => mem g.1 g.2 t)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    apply Subtype.ext
    funext p
    obtain ⟨x, y⟩ := p
    have h0 := hT (fun x => g.1 (x, y)) (memr g.1 g.2 y) (by
      intro t ht
      have := congrArg (fun v : T → V₂ => ((v ⟨t, ht⟩ : V₂) : Y → ℂ) y) hg
      simpa [F, LinearMap.funLeft] using this)
    simpa using congrFun h0 x
  exact Module.Finite.of_injective F hF
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfFiniteDimensionalLeviSlices

section

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Sat S → Level S → Types S → FiniteDimensional ℂ (slSp (e1 r s) (Set.range (emb (e2 r s))) S) → FiniteDimensional ℂ (slSp (e2 r s) (Set.range (emb (e1 r s))) S) → FiniteDimensional ℂ S := by
  intro K _ _ r s S hN hsat hlev htyp h1 h2
  obtain ⟨V, hVfd, hV⟩ := UpperTheory.exists_finiteDimensional_compact_translates_of_level_types K (r + s) S hlev htyp
  let Φ₀ : archSmooth K (r + s) →ₗ[ℂ] (AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1 * emb (e2 r s) p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Φ : archSmooth K (r + s) →ₗ[ℂ]
      ((AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s) × (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K (r + s))) → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1.1 * emb (e2 r s) p.1.2 * (p.2 : AdelicGLn.AdelicGL K (r + s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfd0 : FiniteDimensional ℂ (Submodule.map Φ₀ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ₀ ((slSp (e1 r s) (Set.range (emb (e2 r s))) S).map (archSmooth K r).subtype)
      ((slSp (e2 r s) (Set.range (emb (e1 r s))) S).map (archSmooth K s).subtype) inferInstance inferInstance ?_ ?_
    · intro m hm y
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K r (r + s) (e1 r s) (emb (e2 r s) y)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e2 r s) y, ⟨y, rfl⟩, fun x => hf m x⟩, ?_⟩
      funext x
      change (f m : AdelicGLn.AdelicGL K r → ℂ) x = _
      rw [hf, ← emb_comm]
      rfl
    · intro m hm x
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K s (r + s) (e2 r s) (emb (e1 r s) x)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e1 r s) x, ⟨x, rfl⟩, fun y => hf m y⟩, ?_⟩
      funext y
      change (f m : AdelicGLn.AdelicGL K s → ℂ) y = _
      rw [hf]
      rfl
  have hfd : FiniteDimensional ℂ (Submodule.map Φ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ (Submodule.map Φ₀ S) V hfd0 hVfd ?_ ?_
    · intro m hm k
      refine Submodule.mem_map.mpr ⟨rt (k : AdelicGLn.AdelicGL K (r + s)) m, hsat _ k.2 m hm, ?_⟩
      funext x
      change ((rt (k : AdelicGLn.AdelicGL K (r + s)) m : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) _ = _
      rw [rt_apply]
      rfl
    · intro m hm x
      exact hV m hm (emb (e1 r s) x.1 * emb (e2 r s) x.2)
  refine FiniteDimensional.of_injective (Φ.submoduleMap S) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : ∀ p, Φ x p = 0 := fun p => congrFun (congrArg Subtype.val hx) p
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (Reduction.mem_adelicBorel.mp hb)
  have hxN := hN x.2
  change ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * blk m₁ m₂ * k) = 0
  rw [mul_assoc]
  change (∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) g, ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * g) = _) at hxN
  rw [hxN]
  exact hx' ((m₁, m₂), ⟨k, hk⟩)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFinite

section

@[expose] public section

noncomputable section

open NumberField NumberField.mixedEmbedding Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

private theorem slLeft {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n))
    (h : ∀ ψ ∈ S, ∀ g ∈ Γ, ∀ γ m, ψ.1 (g * emb e (AdelicGLn.diagonal K a γ * m)) = ψ.1 (g * emb e m)) :
    ∀ f ∈ slSp e Γ S, IsLeftInvariant f.1 := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, g, hg, hf⟩ := hf
    intro γ m
    rw [hf, hf, h ψ hψ g hg]
  | zero => exact isLeftInvariant_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

theorem ctFin {r s : ℕ} (h₁ : FinAt K r) (h₂ : FinAt K s) {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S)
    (hK : Sat S) : FiniteDimensional ℂ (ctSp r S) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hSat, hinv⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K (r + s) r S hS
  have hC := UpperTheory.constantTermSpace_centre_of_bdd K (r + s) r S hS
  have hcap := UpperTheory.algebraic_module_of_vanishing_block K r s (ctSp r S) hN hC ι D
  have hb1 : ∀ γ : GL (Fin r) K, emb (e1 r s) γ = blk γ (1 : GL (Fin s) K) := by
    intro γ
    simp [blk]
  have hb2 : ∀ γ : GL (Fin s) K, emb (e2 r s) γ = blk (1 : GL (Fin r) K) γ := by
    intro γ
    simp [blk]
  refine UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices K r s (ctSp r S) hN hSat hL hT ?_ ?_
  · refine h₁ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K r (r + s) (e1 r s) _ _ hT, ?_⟩
    · apply slLeft
      rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
      rw [map_mul, ← mul_assoc, ← emb_comm, mul_assoc, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K r (r + s) (e1 r s)).2.1 γ, hb1,
        hinv ψ hψ]
    · refine UpperTheory.siegelLevi_block_aeval_stable K r (r + s) (e1 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).1)
      rintro ψ hψ _ ⟨m₂, rfl⟩ m
      rw [← emb_comm]
      exact hψ m m₂
  · refine h₂ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K s (r + s) (e2 r s) _ _ hT, ?_⟩
    · apply slLeft
      rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
      rw [map_mul, ← mul_assoc, emb_comm m₁ (AdelicGLn.diagonal K s γ), mul_assoc,
        (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K s (r + s) (e2 r s)).2.1 γ, hb2, hinv ψ hψ]
    · refine UpperTheory.siegelLevi_block_aeval_stable K s (r + s) (e2 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).2)
      rintro ψ hψ _ ⟨m₁, rfl⟩ m
      exact hψ m₁ m

private theorem fin_of_ker {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (h1 : FiniteDimensional ℂ (LinearMap.range f)) (h2 : FiniteDimensional ℂ (LinearMap.ker f)) :
    FiniteDimensional ℂ M := by
  apply Module.rank_lt_aleph0_iff.mp
  rw [← LinearMap.rank_range_add_rank_ker f]
  exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 ℂ _) (Module.rank_lt_aleph0 ℂ _)

theorem finAt_of {n : ℕ} (ih : ∀ m < n, FinAt K m) : FinAt K n := by
  intro S hS
  obtain ⟨S', hSS', hB', hSat'⟩ := UpperTheory.exists_automorphic_saturation_submodule K n S hS
  have hct : ∀ r, 0 < r → r < n → FiniteDimensional ℂ (ctSp r S') := by
    intro r hr0 hrn
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn.le
    exact ctFin (ih r hrn) (ih s (by omega)) hB' hSat'
  choose F hF1 _ using fun r => UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping K n r
  let ι : S' →ₗ[ℂ] automorphicForms K n :=
    LinearMap.codRestrict _ ((archSmooth K n).subtype ∘ₗ S'.subtype)
      (fun φ => UpperTheory.isAutomorphicForm_of_bdd_submodule K n S' hB' φ.1 φ.2)
  let I := {r : Fin n // 0 < r.val}
  have hmem : ∀ (i : I) (φ : S'), F i.1.val (ι φ) ∈ ctSp i.1.val S' := fun i φ =>
    Submodule.subset_span ⟨φ.1, φ.2, hF1 _ _⟩
  let G : S' →ₗ[ℂ] ((i : I) → ctSp i.1.val S') :=
    LinearMap.pi (fun i => LinearMap.codRestrict _ ((F i.1.val).comp ι) (hmem i))
  haveI : ∀ i : I, FiniteDimensional ℂ (ctSp i.1.val S') := fun i => hct _ i.2 i.1.2
  haveI : FiniteDimensional ℂ S' := by
    refine fin_of_ker G inferInstance ?_
    have hW : FiniteDimensional ℂ ((LinearMap.ker G).map S'.subtype) := by
      refine UpperTheory.finiteDimensional_of_bdd_cuspidal K n _ (hB'.mono (Submodule.map_subtype_le _ _)) ?_
      rintro _ ⟨x, hx, rfl⟩ r hr0 hrn g
      have h0 : F r (ι x) = 0 := by
        have := congrFun (LinearMap.mem_ker.mp hx) ⟨⟨r, hrn⟩, hr0⟩
        exact congrArg Subtype.val this
      have h1 := congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) g) h0
      simp only [hF1] at h1
      exact h1
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ S'.injective_subtype _).symm
  exact Submodule.finiteDimensional_of_le hSS'

theorem formsFinite : FormsFinite := fun _ _ _ n => Nat.strong_induction_on n fun _ ih => finAt_of ih

end UpperTheory.V.Af.Fin
end
end
end
