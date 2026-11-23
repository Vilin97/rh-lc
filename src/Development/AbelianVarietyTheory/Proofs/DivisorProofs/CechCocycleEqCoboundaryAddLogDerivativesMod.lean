module

import Mathlib
import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1Affine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocycleInTangentSpanStatement
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransition

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1AffineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cech_comparison_structure_h1_affine : ∀ (X T : Scheme.{0}) (p : T ⟶ X), IsSeparated p → ∀ (U : X.affineOpens) (J : Type) (W : J → T.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = p ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), ∃ Φ : (∀ i i' : J, Γ(T, W i ⊓ W i')) → GlobalTheory.CechDR.HO1 ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)), (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∀ (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ k, (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ((e k) i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ((e k) i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') ((e k) i i''))) → Φ (fun i i' => c i i' - ∑ k, (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i') = Φ c - ∑ k, r k • Φ (e k)) ∧ (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → Φ c = 0 → ∃ h : ∀ i : J, Γ(T, W i), ∀ i i', c i i' = resG T inf_le_left (h i) - resG T inf_le_right (h i')) ∧ (∀ x, ∃ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) ∧ Φ c = x) ∧ ∀ (R' : Type) [CommRing R'] (σ : Γ(X, U.1) →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ T) (ι' : Y ⟶ (p ⁻¹ᵁ U.1).toScheme), ι' ≫ (p ⁻¹ᵁ U.1).ι = ι → ∀ (w : ι' ≫ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (Φ c) = 0 := by
  first | exact @GlobalTheory.CechCmp.exists_cech_ho1_cmp | exact GlobalTheory.CechCmp.exists_cech_ho1_cmp | (intros; apply GlobalTheory.CechCmp.exists_cech_ho1_cmp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.AbCohFibre

theorem mem_smul_top_of_tmul_tmul_eq_zero {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] (m : Ideal R)
    [Algebra S (R ⧸ m)] [IsScalarTower R S (R ⧸ m)] [AddCommGroup M] [Module R M] (x : M)
    (hx : ((1 : R ⧸ m) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x) : (R ⧸ m) ⊗[S] (S ⊗[R] M)) = 0) :
    x ∈ m • (⊤ : Submodule R M) := by
  have h1 := congrArg (AlgebraTensorModule.cancelBaseChange R S (R ⧸ m) (R ⧸ m) M) hx
  rw [AlgebraTensorModule.cancelBaseChange_tmul, one_smul, map_zero] at h1
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M m) h1
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

theorem mem_smul_top_of_pull_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (m : Ideal R), m.IsMaximal → ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp (R ⧸ m)) (φ : Y ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ m)))) (x : GlobalTheory.CechDR.HO1 A.hom), GlobalTheory.CechDR.pullHO1 h.w x = 0 → x ∈ m • (⊤ : Submodule R (GlobalTheory.CechDR.HO1 A.hom)) := by
  intro R _ A _ hA m hm Y s' φ h x hx
  haveI : m.IsMaximal := hm
  haveI : m.IsPrime := hm.isPrime
  let f := spMap (algebraMap R (Localization.AtPrime m))
  letI : GrpObj ((Over.pullback f).obj A) := Functor.grpObjObj
  have hAm : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA f
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (Localization.AtPrime m) ((Over.pullback f).obj A) hAm
  have hsq0 : IsPullback (pullback.fst A.hom f) ((Over.pullback f).obj A).hom A.hom f :=
    IsPullback.of_hasPullback A.hom f
  have := hA.proper
  obtain ⟨⟨e₁, he₁⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (Localization.AtPrime m) A.left _ A.hom _ _ hsq0
    inferInstance inferInstance
  obtain ⟨-, -, hbc, -⟩ := GlobalTheory.AbCoh.oStr (Localization.AtPrime m) ((Over.pullback f).obj A) g hAm hg
  let ψ : Localization.AtPrime m →+* R ⧸ m :=
    IsLocalization.lift (M := m.primeCompl) (g := Ideal.Quotient.mk m) (fun y : m.primeCompl => by
      show IsUnit (Ideal.Quotient.mk m (y : R))
      have hy : Ideal.Quotient.mk m (y : R) ≠ 0 := by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact y.2
      letI := Ideal.Quotient.field m
      exact isUnit_iff_ne_zero.mpr hy)
  letI : Algebra (Localization.AtPrime m) (R ⧸ m) := ψ.toAlgebra
  have hcomp : (algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m)) =
      algebraMap R (R ⧸ m) := IsLocalization.lift_comp _
  haveI : IsScalarTower R (Localization.AtPrime m) (R ⧸ m) := IsScalarTower.of_algebraMap_eq'  hcomp.symm
  have hsp : spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f = spMap (algebraMap R (R ⧸ m)) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let φ' : Y ⟶ ((Over.pullback f).obj A).left :=
    pullback.lift φ (s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) (by
      rw [h.w, Category.assoc, hsp])
  have hφ' : φ' ≫ pullback.fst A.hom f = φ := pullback.lift_fst _ _ _
  have hs' : φ' ≫ ((Over.pullback f).obj A).hom = s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) :=
    pullback.lift_snd _ _ _
  have hbig : IsPullback (φ' ≫ pullback.fst A.hom f) s' A.hom
      (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f) := by
    rw [hφ', hsp]; exact h
  have hsq : IsPullback φ' s' ((Over.pullback f).obj A).hom (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) :=
    IsPullback.of_right hbig hs' hsq0
  obtain ⟨e₂, he₂⟩ := hbc (R ⧸ m) Y s' φ' hsq
  have cong : ∀ (φ₁ : Y ⟶ A.left) (σ₁ : R →+* R ⧸ m) (h₁ : φ₁ ≫ A.hom = s' ≫ spMap σ₁), φ₁ = φ →
      σ₁ = algebraMap R (R ⧸ m) → GlobalTheory.CechDR.pullHO1 h₁ x = GlobalTheory.CechDR.pullHO1 h.w x := by
    rintro _ _ _ rfl rfl; rfl
  have h'' : (φ' ≫ pullback.fst A.hom f) ≫ A.hom =
      s' ≫ spMap ((algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m))) := by
    rw [hφ', hcomp]; exact h.w
  have key : GlobalTheory.CechDR.pullHO1 hsq.w (GlobalTheory.CechDR.pullHO1 hsq0.w x) = 0 := by
    rw [GlobalTheory.CechDR.pullHO1_comp hsq0.w hsq.w h'', cong _ _ h'' hφ' hcomp]
    exact hx
  have k1 : ((1 : R ⧸ m) ⊗ₜ[Localization.AtPrime m] (GlobalTheory.CechDR.pullHO1 hsq0.w x)) = 0 := by
    apply e₂.injective
    rw [he₂, map_zero]; exact key
  have k2 := congrArg (LinearMap.lTensor (R ⧸ m) e₁.symm.toLinearMap) k1
  rw [LinearMap.lTensor_tmul, map_zero, ← he₁, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at k2
  exact mem_smul_top_of_tmul_tmul_eq_zero m x k2

end GlobalTheory.AbCohFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.structure_h1_nakayama_closed_fibre : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (m : Ideal R), m.IsMaximal → ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp (R ⧸ m)) (φ : Y ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ m)))) (x : GlobalTheory.CechDR.HO1 A.hom), GlobalTheory.CechDR.pullHO1 h.w x = 0 → x ∈ m • (⊤ : Submodule R (GlobalTheory.CechDR.HO1 A.hom)) := by
  first | exact @GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero | exact GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero | (intros; apply GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleMemCoboundaryAddMaximalSmul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CechBCInj

theorem grp_of_isPullback {X S' P : Scheme.{0}} (G : Over X) [GrpObj G] (hG : IsAbelianScheme G) (f : S' ⟶ X)
    (fst : P ⟶ G.left) (snd : P ⟶ S') (h : IsPullback fst snd G.hom f) :
    ∃ _ : GrpObj (Over.mk snd), IsAbelianScheme (Over.mk snd) := by
  letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj
  have hP := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hG f
  let e : Over.mk snd ≅ (Over.pullback f).obj G := Over.isoMk h.isoPullback (by simp)
  letI gr : GrpObj (Over.mk snd) := GrpObj.ofIso e.symm
  refine ⟨gr, GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso e ?_ hP⟩
  haveI : IsMonHom e.symm.hom := inferInstance
  exact isMonHom_inv_of_iso e.symm

theorem restrict_isPullback {X T : Scheme.{0}} (p : T ⟶ X) (U : X.affineOpens) :
    IsPullback (p ⁻¹ᵁ U.1).ι ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) p (chart U) := by
  have h1 := (isPullback_morphismRestrict p U.1).flip
  have h2 : IsPullback U.1.ι U.2.isoSpec.hom (𝟙 X) (U.2.isoSpec.inv ≫ U.1.ι) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have h3 := h1.paste_vert h2
  rw [Category.comp_id] at h3
  have e : chart U = U.2.isoSpec.inv ≫ U.1.ι := (IsAffineOpen.isoSpec_inv_ι U.2).symm
  rw [e]
  exact h3

theorem resG_appLE' {X T : Scheme.{0}} (p : T ⟶ X) (U : X.affineOpens) {O O' : T.Opens} (hO : O ≤ p ⁻¹ᵁ U.1)
    (h : O' ≤ O) (r : Γ(X, U.1)) :
    resG T h ((p.appLE U.1 O hO).hom r) = (p.appLE U.1 O' (h.trans hO)).hom r := by
  show ((p.appLE U.1 O hO) ≫ T.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]

theorem exists_fin_sum {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (x : M)
    (hx : x ∈ I • (⊤ : Submodule R M)) :
    ∃ (N : ℕ) (r : Fin N → R) (y : Fin N → M), (∀ k, r k ∈ I) ∧ x = ∑ k, r k • y k := by
  have key : ∃ l : List (R × M), (∀ p ∈ l, p.1 ∈ I) ∧ x = (l.map fun p => p.1 • p.2).sum := by
    refine Submodule.smul_induction_on hx (fun r hr n _ => ⟨[(r, n)], by simpa using hr, by simp⟩) ?_
    rintro a b ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
    refine ⟨l₁ ++ l₂, fun p hp => ?_, by simp⟩
    rcases List.mem_append.1 hp with h | h
    exacts [h₁ p h, h₂ p h]
  obtain ⟨l, hl, rfl⟩ := key
  refine ⟨l.length, fun k => l[k].1, fun k => l[k].2, fun k => hl _ (List.getElem_mem _), ?_⟩
  exact (Fin.sum_univ_fun_getElem l (fun p => p.1 • p.2)).symm

theorem cocycle_mem_coboundary_add_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) (ι : A.left ⟶ t.G.left), IsPullback ι A.hom t.G.hom (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∃ (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP U J W hWa hcov hWU m hm A ι hpb c hc hcob
  have sq := restrict_isPullback t.G.hom U
  obtain ⟨inst, hAb⟩ := grp_of_isPullback t.G
    (GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hP) (chart U) _ _ sq
  have hsq : ι ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hpb.w, Category.assoc]
  let ι' := sq.lift ι (A.hom ≫ spMap (Ideal.Quotient.mk m)) hsq
  have hι' : ι' ≫ (t.G.hom ⁻¹ᵁ U.1).ι = ι := sq.lift_fst _ _ _
  have hw : ι' ≫ ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom : (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) =
      A.hom ≫ spMap (Ideal.Quotient.mk m) := sq.lift_snd _ _ _
  have hpb' : IsPullback ι' A.hom (Over.mk ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom :
      (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1))).hom (spMap (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m))) :=
    IsPullback.of_right (by rw [hι']; exact hpb) hw sq
  obtain ⟨Φ, hlin, hinj, hsurj, hnat⟩ := GlobalTheory.T.cech_comparison_structure_h1_affine X t.G.left t.G.hom t.semi.separated U J W hWa hcov hWU
  have h0 := hnat _ (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m)) A.left A.hom ι ι' hι' hpb'.w c hc hcob
  have hmem := GlobalTheory.T.structure_h1_nakayama_closed_fibre _ _ hAb m hm A.left A.hom ι' hpb' (Φ c) h0
  obtain ⟨N, r, y, hr, hy⟩ := exists_fin_sum m _ hmem
  choose e he hΦe using hsurj
  let ρ : ∀ i i' : J, Γ(X, U.1) →+* Γ(t.G.left, W i ⊓ W i') := fun i i' =>
    (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom
  let c' : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i') := fun i i' => c i i' - ∑ k, ρ i i' (r k) * e (y k) i i'
  have hc' : (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c' i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c' i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c' i i'')) := by
    intro i i' i''

    simp only [c', ρ, map_sub, map_sum, map_mul, resG_appLE']
    rw [← hc i i' i'']
    have := fun k => he (y k) i i' i''
    simp only [← this, mul_add, Finset.sum_add_distrib]
    ring
  have hΦ : Φ c' = 0 := by
    rw [hlin c hc N r (fun k => e (y k)) (fun k => he (y k))]
    simp only [hΦe, ← hy, sub_self]
  obtain ⟨h, hh⟩ := hinj c' hc' hΦ
  refine ⟨h, N, r, fun k => e (y k), hr, fun k => he (y k), fun i i' => ?_⟩
  have := hh i i'
  simp only [c'] at this
  rw [sub_eq_iff_eq_add] at this
  exact this

end GlobalTheory.CechBCInj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleMemCoboundaryAddMaximalSmulStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cechCocycle_mem_coboundary_add_maximal_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) (ι : A.left ⟶ t.G.left), IsPullback ι A.hom t.G.hom (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∃ (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  first | exact @GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul | exact GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul | (intros; apply GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransitionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cech_cocycle_condition_log_derivative_transition : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (W₀ : Z.Opens) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W₀ d → ∀ (J : Type) (W : J → Z.Opens) (j : J → L.ι), (∀ i, W i ≤ W₀) → ∀ (hj : ∀ i, W i ≤ L.U (j i)) (i i' i'' : J), resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) * resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val) + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d (W i' ⊓ W i'') (resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i'')).val) * resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i''))⁻¹.val) = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d (W i ⊓ W i'') (resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i'')).val) * resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i''))⁻¹.val) := by
  first | exact @GlobalTheory.DlogCocycle.dlog_cocycle | exact GlobalTheory.DlogCocycle.dlog_cocycle | (intros; apply GlobalTheory.DlogCocycle.dlog_cocycle <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesMod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem GlobalTheory.CechFibre.resG_appLE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {O O' : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (h : O' ≤ O)
    (r : Γ(X, U.1)) :
    resG t.G.left h ((t.G.hom.appLE U.1 O hO).hom r) = (t.G.hom.appLE U.1 O' (h.trans hO)).hom r := by
  show ((t.G.hom.appLE U.1 O hO) ≫ t.G.left.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]



theorem GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  classical
  intro E _ _ _ H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj m hm c hc
  let x0 : Sp (Γ(X, U.1) ⧸ m) ⟶ X := spMap (Ideal.Quotient.mk m) ≫ chart U
  letI : GrpObj ((Over.pullback x0).obj t.G) := Functor.grpObjObj
  have hpb := isGrpPullback_pullback t.G x0
  obtain ⟨θ, h', hθ⟩ := GlobalTheory.T.closedFibre_cechCocycle_in_tangentSpan E H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj m hm
    ((Over.pullback x0).obj t.G) (pullback.fst t.G.hom x0) hpb c hc
  let κ : Fin n → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i') := fun b i i' =>
    δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) *
      resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val
  have hκ : ∀ b i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (κ b i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (κ b i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (κ b i i'') :=
    fun b i i' i'' => GlobalTheory.T.cech_cocycle_condition_log_derivative_transition t.G.left t.PP.L t.PP.isLB _ (δ b) (hδ b) J W j hWU hj i i' i''
  let c₀ : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i') := fun i i' =>
    c i i' - ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * κ b i i'
  have hc₀ : ∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c₀ i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c₀ i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c₀ i i'') := by
    intro i i' i''

    simp only [c₀, map_sub, map_sum, map_mul, GlobalTheory.CechFibre.resG_appLE]
    rw [← hc i i' i'']
    have e : ∀ b, resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (κ b i i'') = _ := fun b => (hκ b i i' i'').symm
    simp only [e, mul_add, Finset.sum_add_distrib]
    ring
  obtain ⟨h, N, r, e, hr, he, hce⟩ := GlobalTheory.T.cechCocycle_mem_coboundary_add_maximal_smul E H X t hP U J W hWa hcov hWU m hm
    ((Over.pullback x0).obj t.G) (pullback.fst t.G.hom x0) hpb.1 c₀ hc₀ ⟨h', hθ⟩
  refine ⟨θ, h, N, r, e, hr, he, fun i i' => ?_⟩
  have := hce i i'
  simp only [c₀] at this
  linear_combination this
end
end
