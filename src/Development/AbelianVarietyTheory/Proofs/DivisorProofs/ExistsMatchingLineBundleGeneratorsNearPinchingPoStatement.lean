module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpen
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenLeOfAppEqOneOfIsClosedImmersionAl

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion :
    ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (Y' : X'.Opens), IsAffineOpen Y' →
    ∀ (N : X'.Opens), (∀ z : Z', i' z ∈ Y' → i' z ∈ N) →
    ∃ b : Γ(X', Y'), (i'.app Y').hom b = 1 ∧ X'.basicOpen b ≤ N := by
  intro X' Z' i' _ Y' hY N hN
  classical
  let K : Ideal Γ(X', Y') :=
    { carrier := {f | X'.basicOpen f ≤ N}
      add_mem' hf hg := (X'.basicOpen_add_le _ _).trans (sup_le hf hg)
      zero_mem' := by simp
      smul_mem' c f hf := by
        change X'.basicOpen (c * f) ≤ N
        rw [Scheme.basicOpen_mul]
        exact inf_le_right.trans hf }
  have hmem (z : Spec Γ(X', Y')) (f : Γ(X', Y')) :
      hY.fromSpec z ∈ X'.basicOpen f ↔ f ∉ z.asIdeal := by
    change z ∈ hY.fromSpec ⁻¹ᵁ X'.basicOpen f ↔ _
    rw [hY.fromSpec_preimage_basicOpen]
    rfl
  have hJ : RingHom.ker (i'.app Y').hom ⊔ K = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ h
    let z : Spec Γ(X', Y') := ⟨m, hm.isPrime⟩
    have hyY : hY.fromSpec z ∈ Y' := hY.range_fromSpec.le ⟨z, rfl⟩
    by_cases hy : hY.fromSpec z ∈ Set.range i'
    · obtain ⟨w, hw⟩ := hy
      have hwN : hY.fromSpec z ∈ N := hw ▸ hN w (hw ▸ hyY)
      obtain ⟨f, hfN, hf⟩ := hY.exists_basicOpen_le (V := N) ⟨_, hwN⟩ hyY
      exact (hmem z f).mp hf (hJm (Ideal.mem_sup_right hfN))
    · have h1 : hY.fromSpec z ∉ (i'.ker.support : Set X') := by
        rw [Scheme.Hom.support_ker, i'.isClosedEmbedding.isClosed_range.closure_eq]
        exact hy
      have h2 : hY.fromSpec z ∉ X'.zeroLocus (U := Y') (i'.ker.ideal ⟨Y', hY⟩ : Set Γ(X', Y')) :=
        fun h ↦ h1 ((i'.ker.coe_support_inter ⟨Y', hY⟩).ge ⟨h, hyY⟩).1
      rw [Scheme.mem_zeroLocus_iff] at h2
      push_neg at h2
      obtain ⟨a, ha, hya⟩ := h2
      have ha' : a ∈ RingHom.ker (i'.app Y').hom := by
        rw [Scheme.Hom.ker_apply] at ha
        exact ha
      exact (hmem z a).mp hya (hJm (Ideal.mem_sup_left ha'))
  have h1 : (1 : Γ(X', Y')) ∈ RingHom.ker (i'.app Y').hom ⊔ K := hJ ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  refine ⟨b, ?_, hb⟩
  have ha0 : (i'.app Y').hom a = 0 := ha
  calc (i'.app Y').hom b = (i'.app Y').hom (a + b) := by rw [map_add (f := _), ha0, zero_add]
    _ = 1 := by rw [hab, map_one]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenLeOfAppEqOneOfIsClosedImmersionAlStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion' : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (Y' : X'.Opens), IsAffineOpen Y' →
    ∀ (N : X'.Opens), (∀ z : Z', i' z ∈ Y' → i' z ∈ N) →
    ∃ b : Γ(X', Y'), (i'.app Y').hom b = 1 ∧ X'.basicOpen b ≤ N := by
  first | exact @GlobalTheory.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion | exact GlobalTheory.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion | (intros; apply GlobalTheory.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpenStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lift_lineBundle_section_of_closedImmersion_affineOpen : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (L' : LB X'), L'.IsLB →
    ∀ (Y' : X'.Opens), IsAffineOpen Y' → ∀ (τ : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ Y'))),
    (∀ (k l : L'.ι) (z : Z') (hk : z ∈ i' ⁻¹ᵁ (L'.U k ⊓ Y')) (hl : z ∈ i' ⁻¹ᵁ (L'.U l ⊓ Y')),
      Z'.presheaf.germ _ z hk (τ k) =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z hl (τ l)) →
    ∃ θ : ∀ k, Γ(X', L'.U k ⊓ Y'),
      (∀ (k l : L'.ι) (x : X') (hk : x ∈ L'.U k ⊓ Y') (hl : x ∈ L'.U l ⊓ Y'),
        X'.presheaf.germ _ x hk (θ k) =
          X'.presheaf.germ (L'.U k ⊓ L'.U l) x ⟨hk.1, hl.1⟩ (L'.g k l).val * X'.presheaf.germ _ x hl (θ l)) ∧
      ∀ k, (i'.app (L'.U k ⊓ Y')).hom (θ k) = τ k := by
  first | exact @GlobalTheory.PinchLift.lift_section_of_closedImm | exact GlobalTheory.PinchLift.lift_section_of_closedImm | (intros; apply GlobalTheory.PinchLift.lift_section_of_closedImm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchingLineBundleGeneratorsNearPinchingPo

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem exists_affine_nbhd_of_closedImm {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (V : Z.Opens)
    (z : Z) (hz : z ∈ V) : ∃ W : X.Opens, IsAffineOpen W ∧ i z ∈ W ∧ i ⁻¹ᵁ W ≤ V := by
  obtain ⟨O, hO, hOV⟩ : ∃ O : Set X, IsOpen O ∧ i ⁻¹' O = V :=
    (i.isClosedEmbedding.isInducing.isOpen_iff).1 V.isOpen
  obtain ⟨W, hW, hzW, hWO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show i z ∈ (⟨O, hO⟩ : X.Opens) by show i z ∈ O; rw [← Set.mem_preimage, hOV]; exact hz)
  refine ⟨W, hW, hzW, fun y hy => ?_⟩
  have : i y ∈ O := hWO hy
  rw [← Set.mem_preimage, hOV] at this
  exact this

theorem gm_idHom_val {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (h : y ∈ U) (a : Γ(Y, U)ˣ) :
    (gm (𝟙 Y) y U a).val = Y.presheaf.germ U y h a.val := by
  rw [gm_val (𝟙 Y) y U h]
  rfl

end GlobalTheory.PinchLift

namespace GlobalTheory.PinchLift

theorem near_matched : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z), L'.IsLB → LZ.IsLB → ∀ w : LB.Iso (L'.pull i') (LZ.pull p'), w.IsGen → ∀ z : Z, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), i z ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ := by
  intro X X' Z Z' p i i' p' hpb hp hi hg L' LZ hL' hLZ w hw z
  haveI : IsClosedImmersion i' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) hpb.flip hi
  have hc : ∀ z' : Z', p (i' z') = i (p' z') := fun z' => by
    have := congrArg (fun f : Z' ⟶ X => f z') hpb.w
    simpa using this
  obtain ⟨j₀, hj₀⟩ := exists_chart hLZ z
  obtain ⟨W₀, hW₀, hzW₀, hW₀j⟩ := exists_affine_nbhd_of_closedImm i (LZ.U j₀) z hj₀
  have hY : IsAffineOpen (p ⁻¹ᵁ W₀) := hW₀.preimage p
  have hZj : ∀ z' : Z', i' z' ∈ p ⁻¹ᵁ W₀ → p' z' ∈ LZ.U j₀ := fun z' h =>
    hW₀j (show i (p' z') ∈ W₀ from (hc z') ▸ h)

  have hpl : ∀ (z' : Z') (k k' : L'.ι) (hk : i' z' ∈ L'.U k) (hk' : i' z' ∈ L'.U k'),
      gm (𝟙 Z') z' ((L'.pull i').U (fun _ => k) ⊓ (L'.pull i').U (fun _ => k'))
        ((L'.pull i').g (fun _ => k) (fun _ => k')) = gm i' z' _ (L'.g k k') := by
    intro z' k k' hk hk'
    have hp : (𝟙 Z' : Z' ⟶ Z') z' ∈ (L'.pull i').U (fun _ => k) ⊓ (L'.pull i').U (fun _ => k') :=
      ⟨mem_pull.2 hk, mem_pull.2 hk'⟩
    show gm (𝟙 Z') z' _ (∏ _k : PUnit, (res _ (pullU i' _ (L'.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z' _ hp _).trans ((gm_pull (𝟙 Z') i' z' (L'.U k ⊓ L'.U k') ⟨hk, hk'⟩ _).trans
      (by rw [Category.id_comp]))

  have hwst : ∀ (z' : Z') (j j' : LZ.ι) (k k' : L'.ι), p' z' ∈ LZ.U j → p' z' ∈ LZ.U j' → i' z' ∈ L'.U k →
      i' z' ∈ L'.U k' →
      gm (𝟙 Z') z' _ (w.s (fun _ => j, fun _ => k)) =
        gm p' z' _ (LZ.g j j') * (gm i' z' _ (L'.g k k'))⁻¹ * gm (𝟙 Z') z' _ (w.s (fun _ => j', fun _ => k')) := by
    intro z' j j' k k' hj hj' hk hk'
    have hm : (𝟙 Z' : Z' ⟶ Z') z' ∈ (LZ.pull p').U (fun _ => j) ⊓ (L'.pull i').U (fun _ => k) ⊓
        ((LZ.pull p').U (fun _ => j') ⊓ (L'.pull i').U (fun _ => k')) :=
      ⟨⟨mem_pull.2 hj, mem_pull.2 hk⟩, mem_pull.2 hj', mem_pull.2 hk'⟩
    have e := congrArg (gm (𝟙 Z') z' _) (hw (fun _ => j, fun _ => k) (fun _ => j', fun _ => k'))
    have hd := gm_div_g (F := p') (L := LZ) (L' := L'.pull i') (𝟙 Z') z' j j' (fun _ => k) (fun _ => k') hj hj'
      (mem_pull.2 hk) (mem_pull.2 hk')
    rw [hpl z' k k' hk hk', Category.id_comp] at hd
    rw [← hd]
    exact (gm_res _ z' _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ z' _ hm _))))

  have hle : ∀ k, i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀) ≤ (LZ.pull p').U (fun _ => j₀) ⊓ (L'.pull i').U (fun _ => k) :=
    fun k z' hz' => ⟨mem_pull.2 (hZj z' hz'.2), mem_pull.2 hz'.1⟩
  let τu : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀))ˣ := fun k => res (hle k) (w.s (fun _ => j₀, fun _ => k))⁻¹
  have hτu : ∀ (z' : Z') (k : L'.ι) (h : z' ∈ i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀)),
      gm (𝟙 Z') z' _ (τu k) = (gm (𝟙 Z') z' _ (w.s (fun _ => j₀, fun _ => k)))⁻¹ := by
    intro z' k h
    show gm (𝟙 Z') z' _ (res (hle k) (w.s (fun _ => j₀, fun _ => k))⁻¹) = _
    rw [gm_res _ z' _ h]; exact map_inv _ _
  have hτ : ∀ (k l : L'.ι) (z' : Z') (hk : z' ∈ i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀))
      (hl : z' ∈ i' ⁻¹ᵁ (L'.U l ⊓ p ⁻¹ᵁ W₀)),
      Z'.presheaf.germ _ z' hk (τu k).val =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z' ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z' hl (τu l).val := by
    intro k l z' hk hl
    have e : gm (𝟙 Z') z' _ (τu k) = gm i' z' (L'.U k ⊓ L'.U l) (L'.g k l) * gm (𝟙 Z') z' _ (τu l) := by
      rw [hτu z' k hk, hτu z' l hl, hwst z' j₀ j₀ k l (hZj z' hk.2) (hZj z' hk.2) hk.1 hl.1,
        gm_self hLZ p' z' (hZj z' hk.2), _root_.one_mul, _root_.mul_inv, inv_inv]
    have e' := congrArg Units.val e
    rw [Units.val_mul, gm_idHom_val z' _ hk, gm_idHom_val z' _ hl, gm_val i' z' (L'.U k ⊓ L'.U l) (show i' z' ∈ L'.U k ⊓ L'.U l from ⟨hk.1, hl.1⟩)] at e'
    exact e'
  obtain ⟨θ, hθc, hθi⟩ := GlobalTheory.T.lift_lineBundle_section_of_closedImmersion_affineOpen X' Z' i' L' hL' (p ⁻¹ᵁ W₀) hY (fun k => (τu k).val) hτ

  have hN : ∀ z' : Z', i' z' ∈ p ⁻¹ᵁ W₀ → i' z' ∈ ⨆ k, X'.basicOpen (θ k) := by
    intro z' h
    obtain ⟨k, hk⟩ := exists_chart hL' (i' z')
    have : z' ∈ i' ⁻¹ᵁ X'.basicOpen (θ k) := by
      rw [Scheme.preimage_basicOpen, hθi k, Scheme.basicOpen_of_isUnit _ (τu k).isUnit]
      exact ⟨hk, h⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, this⟩
  obtain ⟨b, hb1, hbN⟩ := GlobalTheory.T.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion' X' Z' i' (p ⁻¹ᵁ W₀) hY _ hN
  obtain ⟨s, ⟨hsp, hsi⟩, -⟩ := hg W₀ b 1 (by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hb1, map_one, map_one])
  have hzW : i z ∈ X.basicOpen s := by
    show z ∈ i ⁻¹ᵁ X.basicOpen s
    rw [Scheme.preimage_basicOpen, hsi, Scheme.basicOpen_of_isUnit _ isUnit_one]
    exact hzW₀
  have hpW : p ⁻¹ᵁ X.basicOpen s = X'.basicOpen b := by rw [Scheme.preimage_basicOpen, hsp]
  have hWle : X.basicOpen s ≤ W₀ := X.basicOpen_le s
  have hbY : X'.basicOpen b ≤ p ⁻¹ᵁ W₀ := X'.basicOpen_le b

  have hunit : ∀ (k : L'.ι) (x : X'), x ∈ L'.U k → x ∈ X'.basicOpen b → x ∈ X'.basicOpen (θ k) := by
    intro k x hk hx
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (hbN hx)
    have hxY := hbY hx
    have hlU : x ∈ L'.U l ⊓ p ⁻¹ᵁ W₀ := X'.basicOpen_le (θ l) hl
    rw [Scheme.mem_basicOpen (X := X') (f := θ k) x ⟨hk, hxY⟩, hθc k l x ⟨hk, hxY⟩ hlU]
    refine IsUnit.mul ?_ ((Scheme.mem_basicOpen (X := X') (f := θ l) x hlU).1 hl)
    exact (L'.g k l).isUnit.map _
  have hle2 : ∀ k, L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s ≤ L'.U k ⊓ p ⁻¹ᵁ W₀ :=
    fun k x hx => ⟨hx.1, hWle hx.2⟩
  have hle3 : ∀ k, L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s ≤ X'.basicOpen (θ k) := fun k x hx =>
    hunit k x hx.1 (hpW ▸ hx.2)
  have hu : ∀ k, IsUnit ((X'.presheaf.map (homOfLE (hle2 k)).op).hom (θ k)) := by
    intro k
    have e := (RingedSpace.isUnit_res_basicOpen X'.toRingedSpace (θ k)).map
      (X'.presheaf.map (homOfLE (hle3 k)).op).hom
    have h2 : (homOfLE (hle2 k)).op = (homOfLE (X'.basicOpen_le (θ k))).op ≫ (homOfLE (hle3 k)).op :=
      Subsingleton.elim _ _
    rw [h2, Functor.map_comp, CommRingCat.comp_apply]
    exact e
  have hZle : ∀ j, LZ.U j ⊓ i ⁻¹ᵁ X.basicOpen s ≤ LZ.U j ⊓ LZ.U j₀ := fun j y hy => ⟨hy.1, hW₀j (hWle hy.2)⟩
  refine ⟨X.basicOpen s, fun k => (hu k).unit, fun j => res (hZle j) (LZ.g j j₀), hzW, ?_, ?_, ?_⟩
  · intro k l y hk hl hy
    apply Units.ext
    rw [Units.val_mul, gm_idHom_val y _ (show y ∈ L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s from ⟨hk, hy⟩),
      gm_idHom_val y _ (show y ∈ L'.U k ⊓ L'.U l from ⟨hk, hl⟩),
      gm_idHom_val y _ (show y ∈ L'.U l ⊓ p ⁻¹ᵁ X.basicOpen s from ⟨hl, hy⟩),
      IsUnit.unit_spec, IsUnit.unit_spec, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact hθc k l y _ _
  · intro j l y hj hl hy
    have hy0 : y ∈ LZ.U j₀ := hW₀j (hWle hy)
    rw [gm_res _ y _ (show y ∈ LZ.U j ⊓ i ⁻¹ᵁ X.basicOpen s from ⟨hj, hy⟩),
      gm_res _ y _ (show y ∈ LZ.U l ⊓ i ⁻¹ᵁ X.basicOpen s from ⟨hl, hy⟩)]
    exact (gm_cocycle hLZ (𝟙 Z) y hj hl hy0).symm
  · intro z' j k hj hk hjW hkW
    have hkW' : i' z' ∈ X'.basicOpen b := hpW ▸ hkW
    have hY' : i' z' ∈ p ⁻¹ᵁ W₀ := hbY hkW'
    have h0 := hZj z' hY'
    have hs' : gm i' z' (L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s) (hu k).unit = gm (𝟙 Z') z' _ (τu k) := by
      apply Units.ext
      rw [gm_val i' z' _ (show i' z' ∈ L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s from ⟨hk, hkW⟩),
        gm_idHom_val z' _ (show z' ∈ i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀) from ⟨hk, hY'⟩), IsUnit.unit_spec]
      rw [← Scheme.Hom.germ_stalkMap_apply, TopCat.Presheaf.germ_res_apply, Scheme.Hom.germ_stalkMap_apply, hθi k]
    have e1 : gm (𝟙 Z') z' ((LZ.pull p').U (fun _ => j) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j, fun _ => k)) =
        gm p' z' _ (LZ.g j j₀) * (gm i' z' _ (L'.g k k))⁻¹ *
          gm (𝟙 Z') z' ((LZ.pull p').U (fun _ => j₀) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j₀, fun _ => k)) :=
      hwst z' j j₀ k k hj h0 hk hk
    have e2 : gm (𝟙 Z') z' _ (τu k) =
        (gm (𝟙 Z') z' ((LZ.pull p').U (fun _ => j₀) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j₀, fun _ => k)))⁻¹ :=
      hτu z' k ⟨hk, hY'⟩
    rw [gm_res _ z' _ (show p' z' ∈ LZ.U j ⊓ i ⁻¹ᵁ X.basicOpen s from ⟨hj, hjW⟩), hs', e2, e1,
      gm_self hL' i' z' hk, inv_one, _root_.mul_one, mul_inv_cancel_right]

end GlobalTheory.PinchLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchingLineBundleGeneratorsNearPinchingPoStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_matching_lineBundle_generators_near_pinching_point : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z), L'.IsLB → LZ.IsLB → ∀ w : LB.Iso (L'.pull i') (LZ.pull p'), w.IsGen → ∀ z : Z, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), i z ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ := by
  first | exact @GlobalTheory.PinchLift.near_matched | exact GlobalTheory.PinchLift.near_matched | (intros; apply GlobalTheory.PinchLift.near_matched <;> assumption)
end
end
