module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSymmetricVeryAmpleBy

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.SymVeryAmple

theorem exists_iso_pull_of_triv {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (f : X ⟶ X)
    (h : Triv (LB.LinComb H (K := Fin 2) ![f, 𝟙 X] ![1, -1])) : ∃ w : LB.Iso H (H.pull f), w.IsGen := by
  classical
  obtain ⟨t, ht⟩ := h
  let idx : (PUnit.{1} → H.ι) × H.ι → Fin 2 → H.ι :=
    fun p => ![p.1 PUnit.unit, p.2]
  have le : ∀ p : (PUnit.{1} → H.ι) × H.ι,
      (LB.div (H.pull f) H).U p ≤ (LB.LinComb H ![f, 𝟙 X] ![1, -1]).U (idx p) := by
    intro p y hy
    apply Set.mem_iInter.2
    intro k
    fin_cases k
    · exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.1 hy.1
    · exact hy.2
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.gen_chartPull (A := LB.LinComb H ![f, 𝟙 X] ![1, -1]) (h := 𝟙 X)
    ⟨idx, (fun p y hy => le p hy), by
      intro y p q hp hq
      change (PUnit.{1} → H.ι) × H.ι at p q
      refine (CechPic.gm_div' (H.pull f) H (𝟙 X) y p q hp hq).trans ?_
      refine (congrArg (· * _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pull_g H f (𝟙 X) y p.1 q.1 hp.1 hq.1)).trans ?_
      refine Eq.trans ?_ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_linComb H ![f, 𝟙 X] ![1, -1] (𝟙 X) y (idx p) (idx q) (le p hp) (le q hq)).symm
      simp [Fin.prod_univ_two, idx]; rfl⟩ t ht

theorem exists_symmetric_veryAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∃ (H : LB B.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ ∃ w : LB.Iso H (H.pull (GrpObj.inv : B ⟶ B).left), w.IsGen := by
  intro K _ _ B _ hB
  have := hB.comm
  obtain ⟨H, m, s, hH, hs, ht⟩ := exists_symmetric_veryAmpleBy K B hB (GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety K B hB)
  exact ⟨H, m, s, hH, hs, exists_iso_pull_of_triv hH _ ht⟩

end GlobalTheory.SymVeryAmple
