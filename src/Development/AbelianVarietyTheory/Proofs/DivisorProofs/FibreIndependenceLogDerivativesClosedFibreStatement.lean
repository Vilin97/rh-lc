module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompProdOfFn
public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfClosedPoint
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfClosedPoint
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcover
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTranslateCoefficientsZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InfTranslPts

theorem factor_fst {S K : Type} [CommRing S] [Field K] (w : Sp K ⟶ Sp (DualNumber S)) :
    w = (w ≫ spMap (algebraMap S (DualNumber S))) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective w
  have hε : ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
    have h : ψ.hom (DualNumber.eps : DualNumber S) * ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 h
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun x => ?_
  change ψ.hom x = ψ.hom (algebraMap S (DualNumber S) x.fst)
  have hx : x = algebraMap S (DualNumber S) x.fst + algebraMap S (DualNumber S) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [hx]
  rw [map_add (f := _), map_mul, hε, mul_zero, add_zero]

theorem transl_field_point {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
    (P : tEpsG x0 ⟶ G)
    (hP : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ G).left)
    {K : Type} [Field K] (z : Sp K ⟶ (tEpsG x0 ⊗ G).left) :
    z ≫ (lift (fst (tEpsG x0) G ≫ P) (snd (tEpsG x0) G) ≫ μ[G]).left = z ≫ (snd (tEpsG x0) G).left := by
  let zz : Over.mk (z ≫ (tEpsG x0 ⊗ G).hom) ⟶ tEpsG x0 ⊗ G := Over.homMk z rfl
  let p : tEpsG x0 ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : GlobalTheory.VertSpanZero.redOver x0 ≫ P = 1 := Over.OverMorphism.ext hP
  have h2 : zz ≫ fst (tEpsG x0) G = (zz ≫ fst (tEpsG x0) G ≫ p) ≫ GlobalTheory.VertSpanZero.redOver x0 := by
    apply Over.OverMorphism.ext
    have := factor_fst (S := S) (K := K) (z ≫ (fst (tEpsG x0) G).left)
    exact this
  have h3 : zz ≫ fst (tEpsG x0) G ≫ P = 1 := by
    rw [← Category.assoc, h2, Category.assoc, h1, MonObj.comp_one]
  have h4 : zz ≫ ((fst (tEpsG x0) G ≫ P) * snd (tEpsG x0) G) = zz ≫ snd (tEpsG x0) G := by
    rw [MonObj.comp_mul, h3, _root_.one_mul]
  exact congrArg (fun q => q.left) h4

theorem transl_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  intro E _ _ _ H X t S _ x0 P hP y
  refine ⟨(tEpsG x0 ⊗ t.G).left.residueField y, inferInstance,
    (tEpsG x0 ⊗ t.G).left.fromSpecResidueField y, ?_, transl_field_point t.G x0 P hP _⟩
  exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply y _⟩

end GlobalTheory.InfTranslPts
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualNumber_unit_translate_eq_id_field_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  first | exact @GlobalTheory.InfTranslPts.transl_points | exact GlobalTheory.InfTranslPts.transl_points | (intros; apply GlobalTheory.InfTranslPts.transl_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDlogCocycleCoboundaryClosedFibreChar

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.ChartCob

theorem resG_appLE {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O : Z.Opens} {V V' : Y.Opens} (h : V ≤ f ⁻¹ᵁ O) (h' : V' ≤ V)
    (s : Γ(Z, O)) : resG Y h' ((f.appLE O V h).hom s) = (f.appLE O V' (h'.trans h)).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_resG {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O O' : Z.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ O') (h' : O' ≤ O)
    (s : Γ(Z, O)) :
    (f.appLE O' V h).hom (resG Z h' s) = (f.appLE O V (fun _ hx => h' (h hx))).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem isCoc_pullback {Y Z : Scheme.{0}} (f : Y ⟶ Z) {J : Type} (W : J → Z.Opens)
    (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) (hc : GlobalTheory.CechFin.IsCoc W c) :
    GlobalTheory.CechFin.IsCoc (fun i => f ⁻¹ᵁ W i)
      (fun i i' => (f.appLE (W i ⊓ W i') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) := by
  intro i i' i''
  have h3 : f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'' ≤ f ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have e := congrArg (f.appLE (W i ⊓ W i' ⊓ W i'') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'') h3).hom
    (hc i i' i'')
  rw [map_add (f := _), appLE_resG, appLE_resG, appLE_resG] at e
  exact (congrArg₂ (· + ·) (resG_appLE f _ _ _) (resG_appLE f _ _ _)).trans (e.trans (resG_appLE f _ _ _).symm)

theorem isCoc_sum {Z X : Scheme.{0}} (p : Z ⟶ X) (U : X.Opens) (L : LB Z) (hL : L.IsLB) {n : ℕ}
    (δ : Fin n → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hδ : ∀ a, IsField (p ⁻¹ᵁ U) (δ a))
    {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) (hj : ∀ i, W i ≤ L.U (j i))
    (r : Fin n → Γ(X, U)) :
    GlobalTheory.CechFin.IsCoc W (fun i i' => ∑ b, (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) *
      (δ b (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) *
        resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val)) := by
  intro i i' i''

  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e := GlobalTheory.DlogCocycle.dlog_cocycle Z L hL _ (δ b) (hδ b) J W j hWU hj i i' i''
  rw [map_mul (resG Z _) ((p.appLE _ _ _).hom _), map_mul (resG Z _) ((p.appLE _ _ _).hom _),
    map_mul (resG Z _) ((p.appLE _ _ _).hom _), resG_appLE, resG_appLE, resG_appLE, ← e, mul_add]

theorem isCob_pbT {Y Z : Scheme.{0}} (f : Y ⟶ Z) {I : Type} (V Ω : I → Z.Opens)
    (hle : ∀ a, f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ Ω a) (c : ∀ a b : I, Γ(Z, Ω a ⊓ Ω b)) (h : ∀ a, Γ(Y, f ⁻¹ᵁ Ω a))
    (hh : ∀ a b, (f.appLE (Ω a ⊓ Ω b) (f ⁻¹ᵁ Ω a ⊓ f ⁻¹ᵁ Ω b) (fun _ hx => hx)).hom (c a b) =
      resG Y inf_le_left (h a) - resG Y inf_le_right (h b)) :
    GlobalTheory.KS.IsCob (fun a => f ⁻¹ᵁ V a) (fun a b => GlobalTheory.KS.pbT f (c a b) (f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b)) := by
  refine ⟨fun a => -resG Y (hle a) (h a), fun a b => ?_⟩
  have e := (resG_appLE f _ (inf_le_inf (hle a) (hle b)) _).symm.trans
    (congrArg (resG Y (inf_le_inf (hle a) (hle b))) (hh a b))
  rw [map_sub, GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG] at e
  have hab : f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b ≤ f ⁻¹ᵁ (Ω a ⊓ Ω b) := fun x hx => ⟨hle a hx.1, hle b hx.2⟩
  simp only [GlobalTheory.KS.pbT, GlobalTheory.KS.rsT]
  rw [dite_eq_left hab, dite_eq_left inf_le_left, dite_eq_left inf_le_right, map_neg, map_neg,
    GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG]
  refine e.trans ?_
  ring

theorem chart_isCob : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  intro E _ _ _ H X t U n δ hδ J W j _ hsup hWU hj m A _ ι hι r h' hh'
  have htop : ∀ x : A.left, x ∈ ι ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    intro x
    have hw := hι.1.w
    have : x ∈ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := by
      rw [hw]
      show (A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U) x ∈ (U.1 : Set X)
      rw [← U.2.range_fromSpec]
      exact ⟨(A.hom ≫ spMap (Ideal.Quotient.mk m)) x, rfl⟩
    exact this
  let Ω : J ⊕ t.PP.L.ι → t.G.left.Opens := Sum.elim W (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1)
  let jj : J ⊕ t.PP.L.ι → t.PP.L.ι := Sum.elim j id
  have hΩU : ∀ q, Ω q ≤ t.G.hom ⁻¹ᵁ U.1 := by
    rintro (i | a)
    · exact hWU i
    · exact inf_le_right
  have hΩj : ∀ q, Ω q ≤ t.PP.L.U (jj q) := by
    rintro (i | a)
    · exact hj i
    · exact inf_le_left
  have hc := isCoc_pullback ι Ω _ (isCoc_sum t.G.hom U.1 t.PP.L t.PP.isLB δ hδ Ω jj hΩU hΩj r)
  obtain ⟨h, hh⟩ := GlobalTheory.CechFin.isCob_of_isCob_subcover A.left (J ⊕ t.PP.L.ι) (fun q => ι ⁻¹ᵁ Ω q)
    (Set.range Sum.inl) (by
      intro q x _
      have hx : ι x ∈ ⨆ i, W i := by rw [hsup]; exact htop x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨Sum.inl i, TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, rfl⟩, hi⟩⟩)
    _ hc (fun q => match q with | Sum.inl i => h' i | Sum.inr _ => 0) (by
      rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
      exact hh' i i')
  exact isCob_pbT ι t.PP.L.U (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) (fun a x hx => ⟨hx, htop x⟩) _
    (fun a => h (Sum.inr a)) (fun a b => hh (Sum.inr a) (Sum.inr b))

end GlobalTheory.ChartCob
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDlogCocycleCoboundaryClosedFibreCharStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.polarisation_dlog_cocycle_coboundary_closed_fibre_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  first | exact @GlobalTheory.ChartCob.chart_isCob | exact GlobalTheory.ChartCob.chart_isCob | (intros; apply GlobalTheory.ChartCob.chart_isCob <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreIndep
open MonObj



theorem fibre_indep' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ιA : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ιA → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ιA ⁻¹ᵁ W i)), (∀ i i', (ιA.appLE (W i ⊓ W i') (ιA ⁻¹ᵁ W i ⊓ ιA ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := by
  intro E _ _ _ H X t _hprop _hamp hK U n v hv hb δ hδ hδ0 hδt J W j hWa hWcov hWU hj m hm A _ ιA hι r h' hcob
  haveI := hm
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  set q := Ideal.Quotient.mk m with hq
  set x0 : Sp (Γ(X, U.1) ⧸ m) ⟶ X := spMap q ≫ chart U with hx0
  have hB := GlobalTheory.LineNorm.isTanBasis_of_basis E H X t Γ(X, U.1) (chart U) n v hv hb
  have hT : ∀ b, IsTanAtG t x0 (spMap (dualMap q) ≫ v b) := fun b => GlobalTheory.VertSpanZero.isTanAtG_bc t q (hv b)
  let uR : Fin n → (tEpsG (chart U) ⟶ t.G) := fun b => Over.homMk (spMap (epsMul (r b)) ≫ v b) (by
    change (spMap (epsMul (r b)) ≫ v b) ≫ t.G.hom = spMap (algebraMap _ (DualNumber _)) ≫ chart U
    rw [Category.assoc, (hv b).1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      GlobalTheory.VertSpanZero.epsMul_comp_algebraMap])
  obtain ⟨xR, hxRdef⟩ : ∃ xR : tEpsG (chart U) ⟶ t.G, xR = (List.ofFn uR).prod := ⟨_, rfl⟩
  have hxR : IsCombAtG t (chart U) v r xR.left := ⟨uR, fun b => rfl, by rw [hxRdef]⟩
  have eq0 : (dualMap q).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap (Γ(X, U.1) ⧸ m) (DualNumber (Γ(X, U.1) ⧸ m))).comp q := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let jq : tEpsG x0 ⟶ tEpsG (chart U) := Over.homMk (spMap (dualMap q)) (by
    change spMap (dualMap q) ≫ spMap (algebraMap _ (DualNumber _)) ≫ chart U = spMap (algebraMap _ (DualNumber _)) ≫ spMap q ≫ chart U
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, eq0])
  obtain ⟨P, hPdef⟩ : ∃ P : tEpsG x0 ⟶ t.G, P = jq ≫ xR := ⟨_, rfl⟩
  have hPl : P.left = spMap (dualMap q) ≫ xR.left := by rw [hPdef]; rfl
  have hP : IsCombAtG t x0 (fun b => spMap (dualMap q) ≫ v b) (fun b => q (r b)) P.left := by
    refine ⟨fun b => jq ≫ uR b, fun b => ?_, ?_⟩
    · change spMap (dualMap q) ≫ spMap (epsMul (r b)) ≫ v b = spMap (epsMul (q (r b))) ≫ spMap (dualMap q) ≫ v b
      have e1 : (dualMap q).comp (epsMul (r b)) = (epsMul (q (r b))).comp (dualMap q) := by
        apply RingHom.ext; intro z; ext
        · simp [epsMul, dualMap]
        · simp [epsMul, dualMap, mul_comm]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      exact congrArg (fun g => Spec.map (CommRingCat.ofHom g) ≫ v b) e1
    · rw [← GlobalTheory.FirstOrderValue.comp_prod_ofFn, ← hxRdef, hPdef]
  have hPt : spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left := by
    obtain ⟨u', hu', hu'P⟩ := hP
    let s : Over.mk x0 ⟶ tEpsG x0 := Over.homMk (spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom) (by
      change _ ≫ spMap (algebraMap _ _) ≫ x0 = x0
      rw [← Category.assoc, GlobalTheory.VertSpanZero.spMap_fst_algebraMap, Category.id_comp])
    have hs : ∀ b, s ≫ u' b = 1 := fun b => Over.OverMorphism.ext (by
      change spMap _ ≫ (u' b).left = _
      rw [hu' b, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.VertSpanZero.fst_comp_epsMul]
      exact (hT b).2)
    have h1 : s ≫ (List.ofFn u').prod = 1 := by
      rw [GlobalTheory.FirstOrderValue.comp_prod_ofFn]; simp [hs]
    have h2 : (s ≫ (List.ofFn u').prod).left = (1 : Over.mk x0 ⟶ t.G).left := by rw [h1]
    rw [Over.comp_left, hu'P] at h2
    exact h2

  have hgen : ∃ c : LB.Gen (Out.translDiff t.G t.PP.L P), c.IsGen := by
    let T := tEpsG x0
    let π : (T ⊗ t.G).left ⟶ Sp (DualNumber (Γ(X, U.1) ⧸ m)) := (fst T t.G).left
    let τ : (T ⊗ t.G).left ⟶ t.G.left := (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G]).left
    let ρ : (T ⊗ t.G).left ⟶ t.G.left := (snd T t.G).left
    have wπ : π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) ≫ x0 = (T ⊗ t.G).hom := Over.w (fst T t.G)
    have wρ : ρ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (snd T t.G)
    have wτ : τ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G])
    obtain ⟨ρ', hρ', hρs⟩ : ∃ ρ' : (T ⊗ t.G).left ⟶ A.left, ρ' ≫ ιA = ρ ∧
        ρ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift ρ _ wρ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    obtain ⟨τ', hτ', hτs⟩ : ∃ τ' : (T ⊗ t.G).left ⟶ A.left, τ' ≫ ιA = τ ∧
        τ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift τ _ wτ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    have hpts : ∀ y, τ'.base y = ρ'.base y := by
      intro y
      obtain ⟨K, _, z, ⟨p, rfl⟩, hz⟩ := GlobalTheory.T.dualNumber_unit_translate_eq_id_field_points E H X t _ x0 P hPt y
      have hzz : z ≫ τ' = z ≫ ρ' := hι.1.hom_ext (by rw [Category.assoc, Category.assoc, hτ', hρ']; exact hz)
        (by rw [Category.assoc, Category.assoc, hτs, hρs])
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hzz]
    have hιU : ∀ z, ιA.base z ∈ t.G.hom ⁻¹ᵁ U.1 := fun z => by
      show (ιA ≫ t.G.hom).base z ∈ U.1
      rw [hι.1.w, hx0, ← Category.assoc, Scheme.Hom.comp_apply]
      have h : (chart U).base ((A.hom ≫ spMap q).base z) ∈ Set.range (chart U).base := ⟨_, rfl⟩
      rwa [chart, U.2.range_fromSpec] at h
    have e : (fun n : Fin 2 => ![τ', ρ'] n ≫ ιA) = ![τ, ρ] := by
      funext n; fin_cases n
      · exact hτ'
      · exact hρ'
    have key := GlobalTheory.KS.DlogPol.exists_gen (K := Γ(X, U.1) ⧸ m) π τ' ρ' (fun y W hy => by rwa [← hpts y]) ιA t.PP.L
      t.PP.isLB (fun a b => GlobalTheory.KS.pbT ιA (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b)) ?_ (GlobalTheory.T.polarisation_dlog_cocycle_coboundary_closed_fibre_charts E H X t U n δ hδ J W j hWa hWcov hWU hj m A ιA hι r h' hcob)
    · rw [e] at key
      exact key
    intro a b y ha hb
    beta_reduce
    have hτy : τ.base y = ρ.base y := by
      rw [← hτ', ← hρ', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hpts]
    have hρU : ρ.base y ∈ t.G.hom ⁻¹ᵁ U.1 := by rw [← hρ', Scheme.Hom.comp_apply]; exact hιU _
    have ha' : ρ.base y ∈ t.PP.L.U a := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact ha
    have hb' : ρ.base y ∈ t.PP.L.U b := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact hb
    have hyO : ρ.base y ∈ (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) := ⟨⟨ha', hρU⟩, ⟨hb', hρU⟩⟩
    have hOab : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.PP.L.U a ⊓ t.PP.L.U b :=
      inf_le_inf inf_le_left inf_le_left
    have hOU : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.G.hom ⁻¹ᵁ U.1 :=
      inf_le_left.trans inf_le_right
    have hρ'y : ρ'.base y ∈ ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b := by
      rw [← hpts y]; exact ⟨ha, hb⟩
    have e2a := GlobalTheory.T.firstOrder_translation_formula_germs E H X t U n v hv δ hδ hδ0 hδt r xR hxR (Γ(X, U.1) ⧸ m) q P hPl
    have e2 := e2a _ hOU (resG t.G.left hOab (t.PP.L.g a b).val) y hyO
    rw [GlobalTheory.KS.DlogPol.gs_pbT ρ' ιA y (O₀ := (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (O := ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b) (fun z hz => ⟨⟨hz.1, hιU z⟩, ⟨hz.2, hιU z⟩⟩) hρ'y, hτ', hρ',
      ← gs_res τ y hOab (hτy ▸ hyO), ← gs_res ρ y hOab hyO]
    rw [e2]
    have hκ : (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * (δ c _ (resG t.G.left hOab (t.PP.L.g a b).val) *
        resG t.G.left hOab (t.PP.L.g a b)⁻¹.val)) = (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) *
        δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)) * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    have hFF : resG t.G.left hOab (t.PP.L.g a b).val * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hFF' := congrArg (gs ρ y _) hFF
    rw [gs_mul ρ y _ hyO, GlobalTheory.KS.DlogPol.gs_one ρ y _ hyO] at hFF'
    rw [hκ, gs_mul ρ y _ hyO]
    linear_combination (-(gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Γ(X, U.1) ⧸ m)))).inv.hom DualNumber.eps) *
      gs ρ y _ (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)))) * hFF'
  have hP1 : P = toUnit _ ≫ η[t.G] := hK (DualNumber (Γ(X, U.1) ⧸ m)) _ P fun p => by
    obtain ⟨c, hc⟩ := hgen
    exact ⟨⊤, trivial, gen_chartPull (GlobalTheory.chartPullPull (Out.translDiff t.G t.PP.L P) _) c hc⟩
  have hP1' : P.left = (1 : tEpsG x0 ⟶ t.G).left := by rw [hP1, Hom.one_def]
  have h0 := GlobalTheory.VertSpanZero.isCombAtG_zero t x0 _ hT
  have huniq := (hB.2 (Γ(X, U.1) ⧸ m) q _ (GlobalTheory.VertSpanZero.isTanAtG_one t x0)).unique (hP1' ▸ hP) h0
  intro b
  have := congrFun huniq b
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

end GlobalTheory.FibreIndep

theorem GlobalTheory.FibreIndep.fibre_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := GlobalTheory.FibreIndep.fibre_indep'
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.fibreIndependence_logDerivatives_closedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := by
  first | exact @GlobalTheory.FibreIndep.fibre_indep | exact GlobalTheory.FibreIndep.fibre_indep | (intros; apply GlobalTheory.FibreIndep.fibre_indep <;> assumption)
end
end
