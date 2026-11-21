module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PowerForm

theorem diag_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (h : IsE8 W) (u : Fin 8) : 0 < W u u := by
  have h₁ := h.1.diag_pos (i := u)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_pos] at h₁
  omega

theorem sum_single {G M : Type*} [Group G] [AddCommGroup M] (B : G → G → M)
    (h₁ : ∀ x x' y, B (x * x') y = B x y + B x' y) (h₂ : ∀ x x' y, B y (x * x') = B y x + B y x')
    (W : Matrix (Fin 8) (Fin 8) ℤ) (x : G) :
    ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • B (if uv.1 = 0 then x else 1) (if uv.2 = 0 then x else 1) =
      W 0 0 • B x x := by
  have z₁ : ∀ y, B 1 y = 0 := fun y => by simpa using h₁ 1 1 y
  have z₂ : ∀ y, B y 1 = 0 := fun y => by simpa using h₂ 1 1 y
  rw [Finset.sum_eq_single (0, 0) (fun b _ hb => ?_) (by simp)]
  · simp
  · by_cases a₁ : b.1 = 0
    · have a₂ : b.2 ≠ 0 := fun a₂ => hb (Prod.ext a₁ a₂)
      rw [if_neg a₂, z₂, smul_zero]
    · rw [if_neg a₁, z₁, smul_zero]


open GlobalTheory.CechPic in
theorem relAmple_diag : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) [IsLocallyNoetherian S] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.RelAmple G L → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  intro W S _ G A _ _ _ _ pr L P hW hG hA _ hpr hL hP hbi hiso hamp
  have cls_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : (L.pull f).IsLB) :
      cls (L.pull f) h = pull f (cls L hL) := rfl
  have pull_id {X Y Z : Scheme.{0}} (c : Pic X) : pull (𝟙 X) c = c := by
    obtain ⟨A, hA, rfl⟩ := cls_surj c
    exact (cls_eq_iff (pull_isLB hA _) hA).2 (iso_of_chart hA (chartPullPull A _ _ rfl))
  have pull_comp {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (c : Pic X) : pull (g ≫ f) c = pull g (pull f c) := by
    obtain ⟨A, hA, rfl⟩ := cls_surj c
    exact ((cls_eq_iff (pull_isLB (pull_isLB hA _) _) (pull_isLB hA _)).2 (iso_of_chart (pull_isLB hA _)
      (chartPullLinComb A f (fun _ : PUnit => g) (fun _ => g ≫ f) (fun _ => 1) (𝟙 _)
        fun _ => (Category.id_comp _).symm))).symm
  have cls_linComb_single {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] [DecidableEq K] (φ : K → (Y ⟶ X)) (k : K) :
      cls _ (LB.isLB_linComb hL φ (Pi.single k 1)) = pull (φ k) (cls L hL) := by
    refine (cls_eq_iff _ (pull_isLB hL _)).2 (iso_of_chart (pull_isLB hL _)
      ⟨fun j _ => j k, fun _ _ h => mem_pull.2 (Set.mem_iInter.1 h k), ?_⟩)
    intro y p q hp hq
    refine (gm_linComb L φ _ (𝟙 Y) y p q hp hq).trans (Eq.symm ((gm_pull_g L (φ k) (𝟙 Y) y (fun _ => p k) (fun _ => q k)
      (mem_pull.2 (Set.mem_iInter.1 hp k)) (mem_pull.2 (Set.mem_iInter.1 hq k))).trans ?_))
    rw [Finset.prod_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zpow_zero]) (by simp),
      Pi.single_eq_same, zpow_one]
  have cls_linComb {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (h : (LB.LinComb L φ ε).IsLB) : cls _ h = ∑ k, ε k • pull (φ k) (cls L hL) := by
    classical
    let F : (K → ℤ) →+ Pic Y := AddMonoidHom.mk' (fun ε => cls _ (LB.isLB_linComb hL φ ε)) (cls_linComb_add hL φ)
    have e : ε = ∑ k, ε k • (Pi.single k 1 : K → ℤ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    show F ε = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, ← e]
    exact congrArg _ (cls_linComb_single hL φ k)
  obtain ⟨j, hj, -⟩ := hpr A fun v => if v = 0 then 𝟙 A else 1
  have := hG.proper
  have hcl : IsClosedImmersion j.left := GlobalTheory.Retract.isClosedImmersion_section (r := (pr 0).left)
    (by rw [← Over.comp_left, hj, if_pos rfl, Over.id_left]) (Over.w (pr 0))
  have hpos := diag_pos hW 0
  have hn : 0 < (W 0 0).toNat := by omega
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := LB.isLB_pull hP _
  have hfin : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
  have c₁ := (relAmple_finite_pow_iso S A G j L 1 one_pos hA hG hL inferInstance).1 hamp
  refine (relAmple_finite_pow_iso S A A (𝟙 A) _ _ hn hA hA hD hfin).2.1.1
    ((relAmple_finite_pow_iso S A A (𝟙 A) _ 1 one_pos hA hA (LB.isLB_pull hL _) hfin).2.2.2 _
      (LB.isLB_linComb hD _ _) ?_ c₁)
  refine (cls_eq_iff (LB.isLB_pull hL _) (LB.isLB_linComb hD _ _)).1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_linComb hD, Fintype.sum_unique, pull_id, cls_pull hL, (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hiso, cls_linComb hP, map_sum,
    cls_pull hP, ← natCast_zsmul, Int.toNat_of_nonneg hpos.le]
  refine Eq.trans (Finset.sum_congr rfl fun uv _ => ?_)
    (sum_single (G := A ⟶ A) (fun a b => pull (lift a b).left (cls P hP)) (fun a a' b => ?_) (fun a a' b => ?_)
      W (𝟙 A))
  · rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hj, hj]
  · have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi A a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi A a a' b).2
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.PowerForm
