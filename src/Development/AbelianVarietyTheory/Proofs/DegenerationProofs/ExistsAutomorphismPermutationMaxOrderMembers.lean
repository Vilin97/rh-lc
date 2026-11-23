module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyAutomorphismShiftsJacobianOrderStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobianOrderMonotoneSemistableModelStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeronStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VectorFieldOrderAddOfProdStrictHenselianStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsModelMapDefinedWeakNeronFamily

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SS.WeakNeronDef

theorem fromSpecStalk_comp {X : Scheme.{0}} {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p =
      Spec.map ((Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp

theorem isDominant_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (x : X) : IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (N : Model R A) : IsPullback N.j A.hom N.Y.hom (spMap (algebraMap R K)) := by
  have h := Over.w N.e.inv
  have : IsIso N.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map N.e.inv))
  refine IsPullback.of_iso (IsPullback.of_hasPullback N.Y.hom (spMap (algebraMap R K)))
    (asIso N.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j]
  · simp [← h]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem exists_dvr_point (N : Model R A) [IsIntegral N.Y.left] (hN : N.Irr) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ y ∈ N.sp, IsDiscreteValuationRing (N.Y.left.presheaf.stalk y) ∧
      Irreducible (((Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫
        N.Y.left.presheaf.germ ⊤ y trivial).hom ϖ) := by
  have := N.smooth
  have hs := IsPullback.of_hasPullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  set i := pullback.fst N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hi
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : IsClosedImmersion i := by rw [hi]; infer_instance
  have := GlobalTheory.isReduced_of_smooth_of_isReduced
    (pullback.snd N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  have hr : Set.range i = N.sp := Set.ext fun x => DvrModel.mem_range_special hs x
  have : IrreducibleSpace ↥(pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
    have h1 : IrreducibleSpace (Set.range i) := by
      rw [hr]; exact Subtype.irreducibleSpace hN
    exact i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.surjective.irreducibleSpace
      i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.continuous
  have := isIntegral_of_irreducibleSpace_of_isReduced
    (pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact ⟨i (genericPoint _), hr.le ⟨_, rfl⟩, DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs⟩

end GlobalTheory.SS.WeakNeronDef

namespace GlobalTheory.SS

open WeakNeronDef

theorem exists_defAt_of_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  intro R K _ _ _ _ _ _ A _ I M hM N hN
  have := N.smooth
  have hK := isPullback_j N
  have : IsIntegral N.Y.left := DvrModel.isIntegral hK
  have : IsOpenImmersion N.j := DvrModel.isOpenImmersion_generic hK
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨y, hy, hd, hi⟩ := exists_dvr_point N hN hϖ
  let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫ N.Y.left.presheaf.germ ⊤ y trivial
  let R' : Type := N.Y.left.presheaf.stalk y
  let K' : Type := FractionRing R'
  letI : Algebra R R' := ψ.hom.toAlgebra
  let s : Sp R' ⟶ N.Y.left := N.Y.left.fromSpecStalk y
  have hs : s ≫ N.Y.hom = spMap (algebraMap R R') := fromSpecStalk_comp N.Y.hom y
  have hi' : Irreducible (algebraMap R R' ϖ) := hi
  have := DvrModel.isLocalization_away (K := K) hϖ
  have hu : IsUnit (((algebraMap R' K').comp (algebraMap R R')) ϖ) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R' K')).2 hi'.ne_zero).isUnit
  let k : K →+* K' := IsLocalization.Away.lift ϖ hu
  have hk : spMap k ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) := by
    rw [← Spec.map_comp, ← IsLocalization.Away.lift_comp ϖ (S := K) hu]; rfl
  have hw : (spMap (algebraMap R' K') ≫ s) ≫ N.Y.hom = spMap k ≫ spMap (algebraMap R K) := by
    rw [hk, Category.assoc, hs, ← Spec.map_comp]; rfl
  let a := hK.lift _ _ hw
  have ha : a ≫ N.j = spMap (algebraMap R' K') ≫ s := hK.lift_fst _ _ _
  have ha' : a ≫ A.hom = spMap k := hK.lift_snd _ _ _
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' (by
    rw [hϖ.maximalIdeal_eq, hi'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]) a
    (by rw [← Category.assoc, ha', hk])
  have := (M i).smooth
  have := (M i).sep
  obtain ⟨U, hU, g, h₁, h₂⟩ := spread_out_of_isGermInjective' N.Y.hom (M i).Y.hom (x := y) b (hb.trans hs.symm)
  refine ⟨i, y, hy, U, g, hU, h₂, ?_⟩
  let t : Sp R' ⟶ U.toScheme := U.fromSpecStalkOfMem y hU
  have ht : t ≫ U.ι = s := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hP := isPullback_morphismRestrict N.j U
  have hc : a ≫ N.j = (spMap (algebraMap R' K') ≫ t) ≫ U.ι := by rw [ha, Category.assoc, ht]
  let c := hP.lift _ _ hc.symm
  have hc₁ : c ≫ (N.j ⁻¹ᵁ U).ι = a := hP.lift_snd _ _ _
  have hc₂ : c ≫ (N.j ∣_ U) = spMap (algebraMap R' K') ≫ t := hP.lift_fst _ _ _
  have : IsDominant s := isDominant_fromSpecStalk _ _
  have := GlobalTheory.isDominant_spMap_of_isFractionRing R' K'
  have : IsDominant (c ≫ (N.j ⁻¹ᵁ U).ι ≫ N.j) := by
    rw [← Category.assoc, hc₁, ha]; infer_instance
  have : IsDominant c := IsDominant.of_comp_of_isOpenImmersion c ((N.j ⁻¹ᵁ U).ι ≫ N.j)
  refine ext_of_isDominant_of_isSeparated (M i).Y.hom ?_ c ?_
  · simp only [Category.assoc, h₂, Over.id_left, Category.id_comp, Model.j_hom]
    rw [morphismRestrict_ι_assoc, Model.j_hom]
  · simp only [Over.id_left, Category.id_comp]
    rw [← Category.assoc, hc₂, ← Category.assoc, hc₁, ← hb', Category.assoc]
    exact congrArg _ h₁.symm

end GlobalTheory.SS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsModelMapDefinedWeakNeronFamilyStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_modelMapDefined_weakNeronFamily : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  first | exact @GlobalTheory.SS.exists_defAt_of_weakNeron | exact GlobalTheory.SS.exists_defAt_of_weakNeron | (intros; apply GlobalTheory.SS.exists_defAt_of_weakNeron <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrderStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.existsUnique_modelHasJacobianOrder : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ M : Model R A, M.Irr → ∃! n : ℤ, HasOrd M D π n := by
  first | exact @GlobalTheory.SS.Ord.existsUnique_hasOrd | exact GlobalTheory.SS.Ord.existsUnique_hasOrd | (intros; apply GlobalTheory.SS.Ord.existsUnique_hasOrd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAutomorphismPermutationMaxOrderMembers

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem Model.twist_twist_symm {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
    (M : Model R A) (f : A ≅ A') : (M.twist f).twist f.symm = M := by
  obtain ⟨Y, e, h₁, h₂, h₃⟩ := M
  simp [Model.twist]

theorem isIntegral_of_abelian {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem exists_genIso_of_max_ord (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) (π : R) (hπ : Irreducible π) (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A) (hD : IsFrame D)
    (J : Type) (M : J → Model R A) (hI : ∀ j, (M j).Irr) (hW : WeakNeron M) (o : J → ℤ)
    (ho : ∀ j, HasOrd (M j) D π (o j)) (ρ : ℤ) (hρ : ∀ j, o j ≤ ρ) (f : A ≅ A) (i : J) (hi : o i = ρ) :
    ∃ i', o i' = ρ ∧ GenIso (M i) (M i') f.hom := by
  have hint := isIntegral_of_abelian A hA
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  have bound : ∀ (N : Model R A) (m : ℤ), N.Irr → HasOrd N D π m →
      m ≤ ρ ∧ (m = ρ → ∃ i', o i' = ρ ∧ GenIso N (M i') (𝟙 A)) := by
    intro N m hN hm
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_modelMapDefined_weakNeronFamily R K A J M hW N hN
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.jacobian_order_monotone_semistableModel R K π hπ A I D hD N (M j) m (o j) hN (hI j) hm (ho j) hj
    have := hρ j
    exact ⟨h₁.trans this, fun e => ⟨j, by omega, h₂ (by omega)⟩⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder R K π hπ A hA I D hD f
  obtain ⟨c', hc'⟩ := GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder R K π hπ A hA I D hD f.symm
  have t₁ := hc _ _ (ho i)
  have t₂ := hc' _ _ (ho i)
  have t₃ := hc' _ _ t₁
  rw [Model.twist_twist_symm] at t₃
  have e₃ := (GlobalTheory.T.existsUnique_modelHasJacobianOrder R K π hπ A I D hD (M i) (hI i)).unique t₃ (ho i)
  have i₁ : ((M i).twist f).Irr := hI i
  have i₂ : ((M i).twist f.symm).Irr := hI i
  obtain ⟨b₁, b₁'⟩ := bound _ _ i₁ t₁
  obtain ⟨b₂, -⟩ := bound _ _ i₂ t₂
  obtain ⟨i', hi', hg⟩ := b₁' (by omega)
  exact ⟨i', hi', (h3 A A (M i) (M i') f).2.1.2 hg⟩

theorem WeakNeron.nonempty {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) {A : Over (Sp K)} [GrpObj A] {J : Type} {M : J → Model R A} (hW : WeakNeron M) :
    Nonempty J := by
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  obtain ⟨i, -⟩ := hW R K (by simp) (η[A]).left (by
    rw [← Category.assoc, Over.w]
    simp)
  exact ⟨i⟩

theorem exists_permuted_members : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ S : Finset (Fin n), S.Nonempty ∧ (∀ (f : A ≅ A), ∀ i ∈ S, ∃ i' ∈ S, GenIso (M i) (M i') f.hom) ∧ ∀ (Θ : A ⊗ A ≅ A ⊗ A), ∀ i ∈ S, ∀ j ∈ S, ∃ i' ∈ S, ∃ j' ∈ S, GenIso ((M i).prod (M j)) ((M i').prod (M j')) Θ.hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  have hne := hW.nonempty hSH
  have hdvr := hSH.1
  have hfr := hSH.2.2.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_vectorFieldFrame_smooth_commGrpScheme K A g hg
  choose o ho using fun i => (GlobalTheory.T.existsUnique_modelHasJacobianOrder R K π hπ A (Fin g) D hD (M i) (hI i)).exists
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max o
  refine ⟨Finset.univ.filter fun i => o i = o i₀, ⟨i₀, by simp⟩, ?_, ?_⟩
  · intro f i hi
    obtain ⟨i', hi', h⟩ := exists_genIso_of_max_ord R K hSH π hπ A hA _ D hD _ M hI hW o ho (o i₀) hi₀ f i
      (by simpa using hi)
    exact ⟨i', by simpa using hi', h⟩
  · intro Θ i hi j hj
    have hi : o i = o i₀ := by simpa using hi
    have hj : o j = o i₀ := by simpa using hj
    obtain ⟨D₂, hD₂, hp⟩ := GlobalTheory.T.vectorFieldOrder_add_of_prod_strictHenselian R K hSH π hπ A A _ _ D D hD hD
    obtain ⟨p₁, p₂⟩ := GlobalTheory.T.prod_irr_and_weakNeron' R K hSH A A
    obtain ⟨⟨i', j'⟩, h', h⟩ := exists_genIso_of_max_ord R K hSH π hπ (A ⊗ A)
      (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ D₂ hD₂ (Fin n × Fin n)
      (fun p => (M p.1).prod (M p.2)) (fun p => p₁ _ _ (hI _) (hI _)) (p₂ _ _ M M hW hW)
      (fun p => o p.1 + o p.2) (fun p => hp _ _ _ _ (hI _) (hI _) (ho _) (ho _)) (o i₀ + o i₀)
      (fun p => add_le_add (hi₀ _) (hi₀ _)) Θ (i, j) (by simp [hi, hj])
    have a₁ := hi₀ i'
    have a₂ := hi₀ j'
    have h' : o i' + o j' = o i₀ + o i₀ := h'
    exact ⟨i', by simp; omega, j', by simp; omega, h⟩

end GlobalTheory.SS
end
end
