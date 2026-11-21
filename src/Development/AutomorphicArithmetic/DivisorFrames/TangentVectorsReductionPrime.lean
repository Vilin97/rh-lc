import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

section Helpers

open MonoidalCategory CartesianMonoidalCategory MonObj Matrix

private theorem isTan_iff {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsOver V V ⟶ G) :
    IsTan w ↔ IsTangent (R := V) w := by
  have h1 : (1 : ptOver V V ⟶ G).left = η[G].left := by
    have e : (1 : ptOver V V ⟶ G) = CartesianMonoidalCategory.toUnit _ ≫ η[G] := rfl
    rw [e, Over.comp_left]
    have e2 : (CartesianMonoidalCategory.toUnit (ptOver V V)).left = 𝟙 (Sp V) := by
      have := Over.w (CartesianMonoidalCategory.toUnit (ptOver V V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [h1]

private theorem eig_of_comb {K O : Type} [CommRing K] [CommRing O] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    (act : OAct O A) (a : O) (s : K) {m : ℕ} {x : Fin m → (epsR K ⟶ A)} (ht : ∀ i, IsTangent (x i))
    (he : ∀ i, (x i ≫ act.act a).left = spMap (epsScaleR s) ≫ (x i).left) {c : Fin m → K} {w : epsR K ⟶ A}
    (hc : IsLieComb c x w) : (w ≫ act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  let y : Fin m → GlobalTheory.Serre.Lie act := fun i => GlobalTheory.Serre.Lie.mk act (x i) (ht i)
  have hy : ∀ i, a • y i = s • y i := fun i => GlobalTheory.Serre.Lie.ext (Over.OverMorphism.ext (he i))
  obtain rfl := (GlobalTheory.Serre.Lie.isLieComb_iff c y w).1 hc
  have : a • ∑ i, c i • y i = s • ∑ i, c i • y i := by
    rw [Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm a, hy, smul_comm]
  exact congrArg (fun z : GlobalTheory.Serre.Lie act => z.hom.left) this

private theorem tangent_ext {V K : Type} [CommRing V] [IsLocalRing V] [CommRing K] {f : V →+* K}
    (hf : Function.Injective f) {G : Over (Sp V)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    {φ : A.left ⟶ G.left} (hG : IsSemiAbelian G) (hφ : IsGrpPullback A G (spMap f) φ) {w w₀ : epsR V ⟶ G}
    (hw : IsTangent w) (hw₀ : IsTangent w₀) {w' : epsR K ⟶ A} (o : GlobalTheory.IsVecOver f φ w w')
    (o₀ : GlobalTheory.IsVecOver f φ w₀ w') : w = w₀ := by
  have := hG.comm
  obtain ⟨n, e, e', -, he, he', h, -⟩ := exists_frame (m := 0) (x := Fin.elim0) hG hφ (fun i => i.elim0)
  obtain ⟨p, hp, -⟩ := he.2 w hw
  obtain ⟨q, hq, -⟩ := he.2 w₀ hw₀
  have := (Indep.of_basis he').2 _ _ w' ((GlobalTheory.lieComb_baseChange _ _ _ G A φ hφ n e w p e' w' h hp).1 o)
    ((GlobalTheory.lieComb_baseChange _ _ _ G A φ hφ n e w₀ q e' w' h hq).1 o₀)
  obtain rfl : p = q := funext fun j => hf (congrFun this j)
  exact ((GlobalTheory.LieComb.lieComb_algebra _ G n e he.1).1 p).unique hp hq

end Helpers
