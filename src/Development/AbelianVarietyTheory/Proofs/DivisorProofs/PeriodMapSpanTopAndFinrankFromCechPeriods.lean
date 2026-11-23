module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamClassEqZeroOfPeriodsZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexAStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerUniqueStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinearStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Mathlib.RingTheory.Henselian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerPullStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePeriodMapAbelianVarietyLatticeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfDiscreteOfSpanEqTopComplexPi

section

@[expose] public section

namespace GlobalTheory

theorem exists_basis_of_discrete_of_span_eq_top_complex_pi :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ b : Module.Basis (Fin (2 * g)) ℤ Λ,
        LinearIndependent ℝ (fun i => (b i : Fin g → ℂ)) ∧
          Submodule.span ℝ (Set.range fun i => (b i : Fin g → ℂ)) = ⊤ := by
  intro g Λ hd h
  haveI : IsZLattice ℝ Λ := ⟨h⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have hr : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex]
    simp [mul_comm]
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hr
  have e : (fun i => (b i : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ Λ) := by
    funext i
    exact (Module.Basis.ofZLatticeBasis_apply ℝ Λ b i).symm
  refine ⟨b, ?_, ?_⟩
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).linearIndependent
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).span_eq

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEvaluationSpanDualFinrank

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_eval_eq_top_and_finrank_dual : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (Λ : Type) [AddCommGroup Λ] (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (P : Λ →+ Module.Dual ℂ W), (∀ w, (∀ l, P l w = 0) → w = 0) → (∀ p : Λ →+ ℂ, ∃ w, ∀ l, P l w = p l) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (Module.Dual ℂ W) = n := by
  intro W _ _ Λ _ n b P hinj hsurj
  let Φ : W →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => P (b i))
  have hΦ : ∀ w i, Φ w i = P (b i) w := fun w i => rfl
  have h1 : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    apply hinj
    intro l

    rw [← b.sum_repr l, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, ← hΦ, hw]
    simp
  have h2 : Function.Surjective Φ := by
    intro v
    obtain ⟨w, hw⟩ := hsurj (b.constr ℤ v).toAddMonoidHom
    refine ⟨w, funext fun i => ?_⟩
    rw [hΦ, hw]
    simp
  let e : W ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofBijective Φ ⟨h1, h2⟩
  let c : Module.Basis (Fin n) ℂ W := Module.Basis.ofEquivFun e
  have hc : ∀ i, c.dualBasis i = P (b i) := by
    intro i
    ext w
    rw [Module.Basis.dualBasis_apply]
    exact hΦ w i
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff, ← c.dualBasis.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · simpa using Module.finrank_eq_card_basis c.dualBasis

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEvaluationSpanDualFinrankStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.latticeEvaluation_span_dual_finrank : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (Λ : Type) [AddCommGroup Λ] (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (P : Λ →+ Module.Dual ℂ W), (∀ w, (∀ l, P l w = 0) → w = 0) → (∀ p : Λ →+ ℂ, ∃ w, ∀ l, P l w = p l) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (Module.Dual ℂ W) = n := by
  first | exact @GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual | exact GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual | (intros; apply GlobalTheory.CechPer.span_eval_eq_top_and_finrank_dual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationSquareAbelianVari

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_holUnif_square : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (L' : LB (A ⊗ A).left) (v : HolUnif (A ⊗ A) L' n) (M₁ M₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsAbelianScheme (A ⊗ A) ∧ (∀ w, u.ex (M₁ w) = v.ex w ≫ fst A A) ∧ (∀ w, u.ex (M₂ w) = v.ex w ≫ snd A A) ∧ (∀ w, u.ex ((M₁ + M₂) w) = v.ex w ≫ μ[A]) ∧ (∀ l : v.Λ, M₁ l ∈ u.Λ) ∧ ∀ l : v.Λ, M₂ l ∈ u.Λ := by
  intro A _ g L u hA
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hg := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨n, hn⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ (A ⊗ A) hAA
  obtain ⟨L', ⟨v⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif (A ⊗ A) n hAA hn
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨M₁, hM₁, hΛ₁, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (fst A A) inferInstance
  obtain ⟨M₂, hM₂, hΛ₂, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (snd A A) inferInstance
  refine ⟨n, L', v, M₁, M₂, hAA, hM₁, hM₂, fun w => ?_, fun l => hΛ₁ l l.2, fun l => hΛ₂ l l.2⟩
  rw [LinearMap.add_apply, u.ex_add, hM₁, hM₂, Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationSquareAbelianVariStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_holomorphicUniformisation_square_abelianVariety : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (L' : LB (A ⊗ A).left) (v : HolUnif (A ⊗ A) L' n) (M₁ M₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsAbelianScheme (A ⊗ A) ∧ (∀ w, u.ex (M₁ w) = v.ex w ≫ fst A A) ∧ (∀ w, u.ex (M₂ w) = v.ex w ≫ snd A A) ∧ (∀ w, u.ex ((M₁ + M₂) w) = v.ex w ≫ μ[A]) ∧ (∀ l : v.Λ, M₁ l ∈ u.Λ) ∧ ∀ l : v.Λ, M₂ l ∈ u.Λ := by
  first | exact @GlobalTheory.CechPer.exists_holUnif_square | exact GlobalTheory.CechPer.exists_holUnif_square | (intros; apply GlobalTheory.CechPer.exists_holUnif_square <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriods

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem mem_primDR_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  intro A _ g L u hA c p hp
  obtain ⟨n, L', v, M₁, M₂, hAA, h1, h2, h3, hM1, hM2⟩ := GlobalTheory.T.exists_holomorphicUniformisation_square_abelianVariety A g L u hA
  rw [mem_prim_iff]
  have key : ∀ (φ : A ⊗ A ⟶ A) (M : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (_hw : ∀ w, u.ex (M w) = v.ex w ≫ φ)
      (hM : ∀ l : v.Λ, M l ∈ u.Λ),
      IsPer v.ex v.Λ (cmp1 (str (A ⊗ A)) (pullOver (dp0 ℂ) (𝟙 _) φ c)) (fun l ↦ p ⟨M l, hM l⟩) := by
    intro φ M hw hM
    have hm := IsMor.of_over (dp0 ℂ) (φ := φ.left) (s := str A) (s' := str (A ⊗ A))
      (by rw [← Category.assoc, Over.w])
    exact GlobalTheory.T.isPer_of_isPull1_of_isPer A g L u (A ⊗ A) n L' v φ M hm.w hw hM _ _ _ (comparison_pullback hm c) hp
  have hμ := key μ[A] (M₁ + M₂) h3 (fun l ↦ add_mem (hM1 l) (hM2 l))
  have hf := key (fst A A) M₁ h1 hM1
  have hs := key (snd A A) M₂ h2 hM2
  obtain ⟨hlin, -⟩ := GlobalTheory.T.cechDeRhamPeriods_linear (A ⊗ A) n L' v
  have hdiff := (hlin _ _ _ _ hμ (hlin _ _ _ _ hf hs).1).2
  have hq : ((fun l : v.Λ ↦ p ⟨(M₁ + M₂) l, add_mem (hM1 l) (hM2 l)⟩) -
      ((fun l : v.Λ ↦ p ⟨M₁ l, hM1 l⟩) + fun l : v.Λ ↦ p ⟨M₂ l, hM2 l⟩)) = 0 := by
    funext l
    rw [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_eq_zero, ← map_add (f := _)]
    rfl
  rw [hq] at hdiff
  have h0 := GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero (A ⊗ A) n L' v hAA _ hdiff
  rw [← map_add (f := _), ← map_sub] at h0
  exact sub_eq_zero.1 ((GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex (A ⊗ A) hAA).1 (h0.trans (map_zero _).symm))

end GlobalTheory.CechPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriodsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_primitiveDeRhamCohomology_of_additive_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  first | exact @GlobalTheory.CechPer.mem_primDR_of_isPer | exact GlobalTheory.CechPer.mem_primDR_of_isPer | (intros; apply GlobalTheory.CechPer.mem_primDR_of_isPer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSpanTopAndFinrankFromCechPeriods

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem span_periods_eq_top_and_finrank : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ P : u.Λ →+ HdR A, (∀ c : primDR A, IsPer u.ex u.Λ (cmp1 (str A) c.1) fun l => P l c) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g := by
  intro A _ g L u hA P hP
  obtain ⟨b, -, -⟩ := GlobalTheory.exists_basis_of_discrete_of_span_eq_top_complex_pi g u.Λ u.discrete u.full
  refine GlobalTheory.T.latticeEvaluation_span_dual_finrank (primDR A) u.Λ (2 * g) b P (fun w hw ↦ ?_) (fun p ↦ ?_)
  · have h0 : (fun l ↦ P l w) = 0 := funext hw
    have h1 := hP w
    rw [h0] at h1
    have h2 := GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero A g L u hA _ h1
    have h3 : w.1 = 0 := (GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex A hA).1 (h2.trans (map_zero _).symm)
    exact Subtype.ext h3
  · obtain ⟨x, hx⟩ := GlobalTheory.T.surjective_periodMap_abelianVariety_lattice A g L u hA p
    obtain ⟨c, rfl⟩ := (GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex A hA).2 x
    have hc := GlobalTheory.T.mem_primitiveDeRhamCohomology_of_additive_periods A g L u hA c p hx
    exact ⟨⟨c, hc⟩, fun l ↦ congrFun (GlobalTheory.T.isPer_unique' A g L u _ _ _ (hP ⟨c, hc⟩) hx) l⟩

end GlobalTheory.CechPer
end
end
