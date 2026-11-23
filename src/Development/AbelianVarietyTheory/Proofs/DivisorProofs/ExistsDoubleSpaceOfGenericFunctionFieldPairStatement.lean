module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceOfClosedImmersionContainsDiagonalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoIsMonHomOfIsGtOfRangeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapDoubleSpaceGenericPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_functionField_map_of_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K)
      (ζ : Sp K ⟶ W.Z), ζ (IsLocalRing.closedPoint K) = genericPoint W.Z → ζ ≫ W.p₁ = spMap ψ₁ ≫ (ratOf Y).pt →
        ζ ≫ W.p₂ = spMap ψ₂ ≫ (ratOf Y).pt → ∃ j : W.Z.functionField →+* K, j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y W K _ ψ₁ ψ₂ ζ h h₁ h₂
  have hs : ζ (IsLocalRing.closedPoint K) ⤳ genericPoint W.Z := h ▸ specializes_rfl
  let j : W.Z.functionField →+* K :=
    (W.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of K) ζ).hom
  have e : spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ := by
    change Spec.map (CommRingCat.ofHom j) ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo ζ
  have key : ∀ (p : W.Z ⟶ Y.X) [IsDominant p] (ψ : Y.Fn →+* K), ζ ≫ p = spMap ψ ≫ (ratOf Y).pt →
      j.comp (functionFieldMap p) = ψ := by
    intro p _ ψ hp
    have e2 : spMap (j.comp (functionFieldMap p)) ≫ Y.X.fromSpecStalk (genericPoint Y.X) =
        spMap ψ ≫ Y.X.fromSpecStalk (genericPoint Y.X) := by
      change Spec.map (CommRingCat.ofHom (j.comp (functionFieldMap p))) ≫ genericFieldPoint Y.X = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_functionFieldMap,
        ← Category.assoc]
      change (spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z)) ≫ p = _
      rw [e, hp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp e2))
  exact ⟨j, key W.p₁ ψ₁ h₁, key W.p₂ ψ₂ h₂⟩

end GlobalTheory.FlagPush
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapDoubleSpaceGenericPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (ζ : Sp K ⟶ W.Z), ζ (IsLocalRing.closedPoint K) = genericPoint W.Z → ζ ≫ W.p₁ = spMap ψ₁ ≫ (ratOf Y).pt → ζ ≫ W.p₂ = spMap ψ₂ ≫ (ratOf Y).pt → ∃ j : W.Z.functionField →+* K, j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  first | exact @GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint | exact GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint | (intros; apply GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedClosurePointFibreSquare

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_closure_pair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (q₁ q₂ : Sp K ⟶ Y.X), q₁ ≫ Y.str = q₂ ≫ Y.str → ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str) (ζ : Sp K ⟶ Z), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) ∧ ζ ≫ p₁ = q₁ ∧ ζ ≫ p₂ = q₂ ∧ ζ (IsLocalRing.closedPoint K) = genericPoint Z := by
  intro F _ Y K _ q₁ q₂ hq
  let ξ : Sp K ⟶ Limits.pullback Y.str Y.str := Limits.pullback.lift q₁ q₂ hq
  let x := ξ (IsLocalRing.closedPoint K)
  let i := GlobalTheory.MixHt.cloι x
  have hw : (i ≫ Limits.pullback.fst Y.str Y.str) ≫ Y.str = (i ≫ Limits.pullback.snd Y.str Y.str) ≫ Y.str := by
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  have hl : Limits.pullback.lift _ _ hw = i := by
    apply Limits.pullback.hom_ext
    · exact Limits.pullback.lift_fst _ _ _
    · exact Limits.pullback.lift_snd _ _ _
  have : IsReduced (Sp K) := inferInstanceAs (IsReduced (Spec _))
  have hr : Set.range ξ ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact ⟨genericPoint _, by rw [ha, GlobalTheory.MixHt.cloι_genericPoint]⟩
  have hk : i.ker ≤ ξ.ker := ker_le_ker_of_range_subset_of_isReduced i ξ hr
  let ζ := IsClosedImmersion.lift i ξ hk
  have hζ : ζ ≫ i = ξ := IsClosedImmersion.lift_fac _ _ _
  refine ⟨GlobalTheory.MixHt.clo x, inferInstance, i ≫ Limits.pullback.fst _ _, i ≫ Limits.pullback.snd _ _, hw, ζ, ?_, ?_, ?_, ?_⟩
  · rw [hl]; infer_instance
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_fst _ _ _
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_snd _ _ _
  · apply i.isClosedEmbedding.injective
    refine (Scheme.Hom.comp_apply ζ i _).symm.trans ?_
    rw [hζ, GlobalTheory.MixHt.cloι_genericPoint]

end GlobalTheory.FlagPush
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedClosurePointFibreSquareStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_reduced_closure_point_fibreSquare : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (q₁ q₂ : Sp K ⟶ Y.X), q₁ ≫ Y.str = q₂ ≫ Y.str → ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str) (ζ : Sp K ⟶ Z), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) ∧ ζ ≫ p₁ = q₁ ∧ ζ ≫ p₂ = q₂ ∧ ζ (IsLocalRing.closedPoint K) = genericPoint Z := by
  first | exact @GlobalTheory.FlagPush.exists_closure_pair | exact GlobalTheory.FlagPush.exists_closure_pair | (intros; apply GlobalTheory.FlagPush.exists_closure_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem genPair_specializes_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str,
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
        (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  intro F _ Y K _ ψ₁ ψ₂ hG
  obtain ⟨hF, V, v₁, v₂, e₁, e₂, e₃, e₄⟩ := hG
  have hs : (ratOf Y).pt ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have k : ∀ ψ : Y.Fn →+* K, (spMap ψ ≫ (ratOf Y).pt) ≫ Y.str = spMap (ψ.comp (algebraMap F Y.Fn)) :=
    fun ψ => (Category.assoc (spMap ψ) (ratOf Y).pt Y.str).trans
      ((congrArg (fun g => spMap ψ ≫ g) hs).trans (by rw [← Spec.map_comp]; rfl))
  have h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str := by
    rw [k, k, hF]
  refine ⟨h, ?_⟩
  haveI : IsDominant (spMap (algebraMap V K)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap V K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap V K) from Subtype.val_injective)]
    exact bot_le
  have hv : v₁ ≫ Y.str = v₂ ≫ Y.str := by
    refine ext_of_isDominant (spMap (algebraMap V K)) ?_
    rw [← Category.assoc, ← Category.assoc, e₁, e₂]
    exact h
  let v := Limits.pullback.lift v₁ v₂ hv
  have hgen : spMap (algebraMap V K) ≫ v =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst]; exact e₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · simp only [v, Category.assoc, Limits.pullback.lift_snd]; exact e₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hres : spMap (IsLocalRing.residue V) ≫ v =
      (spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
    · simp only [v, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id]
      exact e₃.symm
  have hsp := ClosedPt.gen_specializes v (IsLocalRing.closedPoint K)
  rw [hgen] at hsp
  have hc : v (IsLocalRing.closedPoint V) = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
    calc v (IsLocalRing.closedPoint V) = (spMap (IsLocalRing.residue V) ≫ v) (IsLocalRing.closedPoint _) :=
          (ClosedPt.closedPt_comp v).symm
      _ = ((spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str) (IsLocalRing.closedPoint _) := by
          rw [hres]
      _ = Limits.pullback.diagonal Y.str ((spMap (IsLocalRing.residue V) ≫ v₁) (IsLocalRing.closedPoint _)) :=
          Scheme.Hom.comp_apply _ _ _
      _ = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by rw [ClosedPt.closedPt_comp v₁, e₄]
  rw [hc] at hsp
  exact hsp

end GlobalTheory.FlagPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.genericPair_specializes_diagonal_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K), GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str, Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  first | exact @GlobalTheory.FlagPush.genPair_specializes_diagonal | exact GlobalTheory.FlagPush.genPair_specializes_diagonal | (intros; apply GlobalTheory.FlagPush.genPair_specializes_diagonal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubleSpaceOfGenericFunctionFieldPair

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_dbl_of_genPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y K _ ψ₁ ψ₂ hg
  obtain ⟨h, hsp⟩ := GlobalTheory.T.genericPair_specializes_diagonal_genericPoint F Y K ψ₁ ψ₂ hg
  obtain ⟨Z, hZi, p₁, p₂, hZ, ζ, hci, hζ₁, hζ₂, hζg⟩ :=
    GlobalTheory.T.exists_reduced_closure_point_fibreSquare F Y K (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
  haveI := hZi
  have hcomp : ζ ≫ Limits.pullback.lift p₁ p₂ hZ =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]; exact hζ₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Limits.pullback.lift_snd]; exact hζ₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hmem : Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ hZ) := by
    have hcl : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ hZ)) := hci.isClosedEmbedding.isClosed_range
    refine hsp.mem_closed hcl ⟨ζ (IsLocalRing.closedPoint K), ?_⟩
    rw [← hcomp]
    first | rfl | exact (Scheme.Hom.comp_apply _ _ _).symm | simp
  obtain ⟨hproj, δ, hδc, hδ₁, hδ₂, hdiag⟩ := GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal F Y Z p₁ p₂ hZ hci hmem
  let W : Dbl Y :=
    { Z := Z, integral := hZi, p₁ := p₁, p₂ := p₂, δ := δ, str_eq := hZ, proj := hproj, closed := hδc,
      δ₁ := hδ₁, δ₂ := hδ₂, diag := hdiag }
  obtain ⟨j, hj₁, hj₂⟩ := GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint F Y W K ψ₁ ψ₂ ζ hζg hζ₁ hζ₂
  exact ⟨W, j, hj₁, hj₂⟩

end GlobalTheory.FlagPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubleSpaceOfGenericFunctionFieldPairStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_doubleSpace_of_genericFunctionFieldPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K), GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  first | exact @GlobalTheory.FlagPush.exists_dbl_of_genPair | exact GlobalTheory.FlagPush.exists_dbl_of_genPair | (intros; apply GlobalTheory.FlagPush.exists_dbl_of_genPair <;> assumption)
end
end
