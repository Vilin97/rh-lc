module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfIsPullDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoTransOfSelfPt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LBIsoEnd

def SelfPt {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : L.ι), f y ∈ L.U i → gm f y (L.U i ⊓ L.U i) (L.g i i) = 1

theorem selfPt_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : SelfPt L :=
  fun _ f y _ hi => gm_self hL f y hi

theorem selfPt_of_lbIso {X : Scheme.{0}} {B P : LB X} (hB : B.IsLB) (H : LBIso B P) : SelfPt P := by
  intro Y f y k hk
  obtain ⟨w, hw⟩ := H
  obtain ⟨i, hi⟩ := exists_chart hB (f y)
  have hm : f y ∈ P.U k ⊓ B.U i ⊓ (P.U k ⊓ B.U i) := ⟨⟨hk, hi⟩, hk, hi⟩
  have e := congrArg (gm f y (P.U k ⊓ B.U i ⊓ (P.U k ⊓ B.U i))) (hw (k, i) (k, i))
  have e' := (gm_res f y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B P f y (k, i) (k, i) hm) (gm_res f y _ hm _))))
  rw [gm_self hB f y hi, inv_one, _root_.mul_one] at e'
  exact _root_.mul_eq_right.1 e'.symm

section Tri

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL : SelfPt L) (hL'' : SelfPt L'') {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [hL Y ((f ≫ F') ≫ F) y j hj] at a
  rw [hL'' Y f y k hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL : SelfPt L) (hL'' : SelfPt L'') :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1 h₂.2.1
          h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Tri

theorem lbIso_trans_of_selfPt {X : Scheme.{0}} {A B C : LB X} (hA : SelfPt A) (hB : B.IsLB) (hC : SelfPt C)
    (H : LBIso A B) (H' : LBIso B C) : LBIso A C := by
  obtain ⟨w', h'⟩ := H.chartPull (chartPullId A) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w, h⟩ := H'.chartPull (chartPullId B) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull C (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w'', T⟩ := exists_comp' hB w w' ((isGen_iff w).1 h) ((isGen_iff w').1 h') hC hA
  exact LBIso.chartPull (chartPullId A) (chartPullUnpull C _ (Category.id_comp _))
    ⟨w'', (isGen_iff w'').2 (T.pgen_comp hB ((isGen_iff w).1 h) ((isGen_iff w').1 h'))⟩

theorem lbIso_trans_end : ∀ (X : Scheme.{0}) (A B P : LB X), A.IsLB → B.IsLB → LBIso A B → LBIso P B → LBIso A P :=
  fun _ _ _ _ hA hB H H' =>
    lbIso_trans_of_selfPt (selfPt_of_isLB hA) hB (selfPt_of_lbIso hB H'.symm) H H'.symm

end GlobalTheory.LBIsoEnd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeCompletedLocalAbelianLoc

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullComplete

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (L : LB G₀.left) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ Z) [IsCommMonObj ((Over.pullback ξ).obj G₀)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj G₀)), LBIso U.LG.L (L.pull (pullback.fst G₀.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus G₀)) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ ψ : R →+* V, IsLocalHom ψ → (∀ w, (jK V ≫ spMap ψ ≫ ξ) w ∈ abLocus G₀) → ∃ (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (gm : G'.left ⟶ G₀.left) (ι : D.toPre.X ≃+ D'.toPre.X), IsSemiAbelian G' ∧ IsGrpPullback G' G₀ (spMap ψ ≫ ξ) gm ∧ LBIso U'.LG.L (L.pull gm) ∧ CoordMap D.toPre D'.toPre ψ ι.toAddMonoidHom ∧ ∀ f : G₀ ⟶ G₀, IsMonHom f → ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ f.left ∧ ∀ m m', EndChar U ((Over.pullback ξ).map f) m → EndChar U' f' m' → ∀ y, ι (m y) = m' (ι y) := by
  intro Z G₀ _ _ hG₀ L R _ _ _ hR ξ _ D A U hL hψ V _ _ _ hV ψ hloc hgen
  have hG : IsSemiAbelian ((Over.pullback ξ).obj G₀) := IsSemiAbelian.pullback ξ G₀ hG₀
  have hpb := isGrpPullback_pullback G₀ ξ
  have hab : ξ ⁻¹' abLocus G₀ = abLocus ((Over.pullback ξ).obj G₀) :=
    Set.ext fun x => abLocus_pullback abLocusOne hG₀ hpb.1 x
  let W : (Sp R).Opens := ⟨ξ ⁻¹' abLocus G₀, by rw [hab]; exact GlobalTheory.AbLocusOpen.isOpen_abLocus_local _ hG⟩
  have hz : (jK V).base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)) = genericPoint (Sp V) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  have hW : spMap ψ (genericPoint (Sp V)) ∈ W := by
    show ξ (spMap ψ (genericPoint (Sp V))) ∈ abLocus G₀
    rw [← hz]
    have := hgen (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    exact this
  let G := (Over.pullback ξ).obj G₀
  let G' := (Over.pullback (specOf ψ)).obj G
  have hbc : IsMonHom (Iso.refl G').hom := by show IsMonHom (𝟙 G'); infer_instance
  obtain ⟨D', A', hD, U', hP⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U V hV.1 ψ hloc W hψ hW
    G' (Iso.refl G') hbc
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback (specOf ψ) G hG
  let β : G'.left ⟶ G.left := (Iso.refl G').hom.left ≫ pullback.fst G.hom (specOf ψ)
  obtain ⟨hLB, hC, hE⟩ := GlobalTheory.Poinc.Eq8.PullUnif.main R hR G hG D A U V hV G' hG' D' A' U' ψ β hloc (Iso.refl G')
    hbc rfl hD hP
  let gm : G'.left ⟶ G₀.left := β ≫ pullback.fst G₀.hom ξ
  have hβ : IsGrpPullback G' G (specOf ψ) β :=
    ((isGrpPullback_of_iso (Iso.refl G')).comp (isGrpPullback_pullback G (specOf ψ))).congr (Category.id_comp _) rfl
  refine ⟨G', inferInstance, inferInstance, D', A', U', gm, hD.xe.symm, hG', hβ.comp hpb, ?_, hC, ?_⟩
  · exact GlobalTheory.LBIsoEnd.lbIso_trans_end _ _ _ _ U'.LG.isLB (pull_isLB U.LG.isLB β) hLB
      (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL β rfl))
  · intro f hf
    haveI := hf
    have e1 : ((Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f)).left ≫ β =
        β ≫ ((Over.pullback ξ).map f).left := by
      show _ ≫ 𝟙 _ ≫ _ = (𝟙 _ ≫ _) ≫ _
      exact pullback.lift_fst _ _ _
    have e2 : ((Over.pullback ξ).map f).left ≫ pullback.fst G₀.hom ξ = pullback.fst G₀.hom ξ ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f), inferInstance, ?_, ?_⟩
    · show _ ≫ β ≫ _ = (β ≫ _) ≫ _
      calc _ = (((Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f)).left ≫ β) ≫ pullback.fst G₀.hom ξ :=
            (Category.assoc _ _ _).symm
        _ = (β ≫ ((Over.pullback ξ).map f).left) ≫ pullback.fst G₀.hom ξ := by rw [e1]
        _ = β ≫ (((Over.pullback ξ).map f).left ≫ pullback.fst G₀.hom ξ) := Category.assoc _ _ _
        _ = β ≫ (pullback.fst G₀.hom ξ ≫ f.left) := by rw [e2]
        _ = _ := (Category.assoc _ _ _).symm
    · intro m m' hm hm' y
      exact hE _ _ inferInstance inferInstance e1 m m' hm hm' y

end GlobalTheory.Poinc.Eq8.PullComplete
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeCompletedLocalAbelianLocStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.uniformisation_baseChange_completedLocal_abelianLocus : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (L : LB G₀.left) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ Z) [IsCommMonObj ((Over.pullback ξ).obj G₀)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj G₀)), LBIso U.LG.L (L.pull (pullback.fst G₀.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus G₀)) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ ψ : R →+* V, IsLocalHom ψ → (∀ w, (jK V ≫ spMap ψ ≫ ξ) w ∈ abLocus G₀) → ∃ (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (gm : G'.left ⟶ G₀.left) (ι : D.toPre.X ≃+ D'.toPre.X), IsSemiAbelian G' ∧ IsGrpPullback G' G₀ (spMap ψ ≫ ξ) gm ∧ LBIso U'.LG.L (L.pull gm) ∧ CoordMap D.toPre D'.toPre ψ ι.toAddMonoidHom ∧ ∀ f : G₀ ⟶ G₀, IsMonHom f → ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ f.left ∧ ∀ m m', EndChar U ((Over.pullback ξ).map f) m → EndChar U' f' m' → ∀ y, ι (m y) = m' (ι y) := by
  first | exact @GlobalTheory.Poinc.Eq8.PullComplete.main | exact GlobalTheory.Poinc.Eq8.PullComplete.main | (intros; apply GlobalTheory.Poinc.Eq8.PullComplete.main <;> assumption)
end
end
