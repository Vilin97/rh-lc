module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPullbackMulGenerator
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasTorusWeightIffTorusEquivariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAppEqOfHasWtZero

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val S X Z τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

theorem gs_id_appLE {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (f : Γ(X, U)) :
    gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom f) = gs r z U f := by
  have e := gs_pull (𝟙 Z) r z U (h trivial) f
  rw [Category.id_comp] at e
  exact (gs_res (𝟙 Z) z h trivial _).trans e

theorem exists_app_eq_of_hasWt_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (W : E.B.left.Opens) (f : Γ(G.left, D.q.left ⁻¹ᵁ W)), UFib.HasWt D.i (D.q.left ⁻¹ᵁ W) f 0 → ∃ a : Γ(E.B.left, W), (D.q.left.app W).hom a = f := by
  intro k _ _ E G _ D W f hf
  have := D.q_affine
  refine (invariant_functions_descend _ G E.B _ D.q D.i D.q_hom D.i_hom D.q_flat D.q_surjective inferInstance
    D.isKernel W).2.2 f fun Z t g h₁ h₂ => fn_ext fun z _ => ?_
  rw [gs_id_appLE, gs_id_appLE, hf Z t g z (h₂ trivial), gm_charUnit_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOfRefine

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_sec_compat {Y Z : Scheme.{0}} {M : LB Y} (φ : M.Sec) (r : Z ⟶ Y) (z : Z) {l l' : M.ι}
    (hl : r z ∈ M.U l) (hl' : r z ∈ M.U l') :
    gs r z (M.U l) (φ.f l) = (gm r z (M.U l ⊓ M.U l') (M.g l l')).val * gs r z (M.U l') (φ.f l') := by
  have hm : r z ∈ M.U l ⊓ M.U l' := ⟨hl, hl'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (φ.compat l l')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem exists_sec_of_refine : ∀ (Y : Scheme.{0}) (M A : LB Y), M.IsLB → A.IsLB →
    ∀ (c : ChartPull M A (𝟙 Y)) (φ : M.Sec), ∃ s : A.Sec, ∀ (l : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ M.U l → gs r z (M.U l) (φ.f l) = gs r z (A.U (c.idx l)) (s.f (c.idx l)) := by
  intro Y M A hM hA c φ
  have cle : ∀ l (y : Y), y ∈ M.U l → y ∈ A.U (c.idx l) := fun l y hy => c.le l hy
  have glue : ∀ i : A.ι, ∃ a : Γ(Y, A.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : M.ι),
      r z ∈ A.U i → r z ∈ M.U l →
      gs r z _ a = (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) := by
    intro i
    let W : M.ι → Y.Opens := fun l => A.U i ⊓ M.U l
    have hW : ∀ l, W l ≤ A.U i ⊓ A.U (c.idx l) := fun l y hy => ⟨hy.1, cle l y hy.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) l, r z ∈ W l →
        gs r z (W l) (u l) =
          (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) :=
      ⟨fun l => (Y.presheaf.map (homOfLE (hW l)).op).hom (A.g i (c.idx l)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W l ≤ M.U l)).op).hom (φ.f l), fun Z r z l hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (hW l hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (A.U i)
      (fun l => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨l, hl⟩ := exists_chart hM y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hy, hl⟩) u
      (fun l l' => fn_ext (V := W l ⊓ W l') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y l hy.1, hu _ _ y l' hy.2, gs_sec_compat φ (𝟙 Y) y hy.1.2 hy.2.2, c.g y l l' hy.1.2 hy.2.2,
          ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hA (𝟙 Y) y hy.1.1 (cle l y hy.1.2) (cle l' y hy.2.2)])
    refine ⟨a, fun Z r z l h₁ h₂ => ?_⟩
    have hz : r z ∈ W l := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W l)) (ha l)).trans (hu Z r z l hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun l Z r z hl => ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 Y) y _ hy _) (gs_res (𝟙 Y) y _ hy _))).symm)
    rw [ha j _ (𝟙 Y) y l hy.1 hl, ha j' _ (𝟙 Y) y l hy.2 hl,
      ← gm_cocycle hA (𝟙 Y) y hy.1 hy.2 (cle l y hl), Units.val_mul, _root_.mul_assoc]
  · have m := cle l _ hl
    refine Eq.symm ((ha _ Z r z l m hl).trans ?_)
    rw [gm_self hA r z m, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionReduction

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero_eq_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val _ _ _ τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

def chartPullH {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) :
    ChartPull (Φ.H 1) (LB.LinComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ))) (𝟙 _) :=
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l _ hy => Set.mem_iInter.2 fun _ => c.le l hy
  { idx := fun l _ => c.idx l
    le := le
    g := fun y l l' hl hl' => by
      refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) (𝟙 _) y _ _
        (le l hl) (le l' hl')).symm
      have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hl hl'
      have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hl, hl'⟩ (Φ.N₀.g l l')
      refine (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).trans (Eq.symm ?_)
      refine Eq.trans ?_ (map_pow _ _ _).symm
      refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
      rw [Category.assoc]
      rfl }

theorem trF_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (q : Y' ⟶ Y) (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (j j' : K → L.ι) :
    trF (fun a => q ≫ ψ a) ε r z j j' = trF ψ ε (r ≫ q) z j j' := by
  simp only [trF, Category.assoc]

theorem exists_red_of_pure : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF α hw φ hp
  have := Φ.D.q_hom
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  obtain ⟨s, hs⟩ := exists_sec_of_refine _ _ _ (Φ.H_isLB 1) (DVR.linComb_isLB L hL _ _) (chartPullH Φ c) φ
  have hF' : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Φ.D.q.left ≫ π) φt)
      (Sum.elim (fun _ => (N : ℤ)) (fun a => - εt a)) (fun a => Φ.D.q.left ≫ ψ a) ε := by
    intro U _ h
    have e := hF U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF' (pullMulSec s (𝟙 _) (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
      r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
      gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval σ r z J * (val t r z J).val := by
    intro Z r z J hJ l hl e
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_inv, Category.comp_id, Units.inv_mul_cancel_right,
      sval_of s r z J (fun _ => c.idx l) (fun _ => e)]
    exact hs l Z r z hl
  have le : ∀ j : K → L.ι, Φ.D.q.left ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j :=
    fun j y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Φ.E.B.left, LB.wchart L ψ j),
      (Φ.D.q.left.app _).hom a = (Φ.G.left.presheaf.map (homOfLE (le j)).op).hom (σ.f j) := by
    intro j
    refine exists_app_eq_of_hasWt_zero k Φ.E Φ.G Φ.D _ _ fun Z τ g z hz => ?_
    have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
      congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
    have hz' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left (g.left z))
    have hl' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hl
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hl)
    have hwt : HasWt Φ.D.i _ (φ.f l) α :=
      (PureWt.hasWt_iff_weight k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).2 fun χ hne => by
        by_contra h
        exact hne (hp ⟨l, h⟩)
    have h₀ := hwt Z τ g z hl
    have h₁ := vσ _ g.left z J hJ l hl (e ())
    have h₂ := vσ _ ((τ ≫ Φ.D.i) * g).left z J hJ l hl' (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
    have h₃ : sval σ ((τ ≫ Φ.D.i) * g).left z J = sval σ g.left z J := by
      have h₄ := h₂.symm.trans (h₀.trans (congrArg _ h₁))
      rw [hw Z τ g z J hJ, mul_left_comm, ← Units.val_mul] at h₄
      exact (Units.mul_left_inj _).1 h₄
    rw [gm_charUnit_zero_eq_one, Units.val_one, _root_.one_mul]
    refine (gs_res _ z (le j) hz' _).trans (Eq.trans ?_ (gs_res _ z (le j) hz _).symm)
    refine (sec_trans σ _ z (le j hz') (hJ.mem _ _)).trans (Eq.trans ?_ (sec_trans σ _ z (le j hz) (hJ.mem _ _)).symm)
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) h₃
    simp only [trF_comp, ← Category.assoc, hq]
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z), Φ.D.q.left (r z) ∈ LB.wchart L ψ j →
      gs (r ≫ Φ.D.q.left) z (LB.wchart L ψ j) (a j) =
        gs r z (LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j) (σ.f j) := fun j Z r z hz =>
    (gs_pull r _ z _ hz _).symm.trans ((congrArg (gs r z _) (ha j)).trans (gs_res r z (le j) hz _))
  refine ⟨⟨a, fun j j' => FunDescent.app_injective Φ.D.q.left (LB.wchart L ψ j ⊓ LB.wchart L ψ j')
    (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ l hl e => ?_⟩
  · have hy' : Φ.D.q.left y ∈ LB.wchart L ψ j ⊓ LB.wchart L ψ j' := hy
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).symm)
    refine ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (sec_trans σ (𝟙 _) y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (gs_mul (𝟙 _ ≫ Φ.D.q.left) y _ hy' _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (congrArg Units.val
        ((gm_linComb L ψ ε (𝟙 _ ≫ Φ.D.q.left) y j j' hy'.1 hy'.2).trans (trF_comp _ _ _ _ _ _ _).symm)))
      ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  · refine (vσ Z r z J hJ l hl e).trans (congrArg₂ (· * ·) (Eq.symm ?_) rfl)
    rw [sval_of _ (r ≫ Φ.D.q.left) z J (fun a => J (r ≫ Φ.D.q.left ≫ ψ a)) (fun a => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun a => hJ (r ≫ Φ.D.q.left ≫ ψ a))

end GlobalTheory.ZH.UFib
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionReductionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.exists_pureWeight_section_reduction : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  first | exact @GlobalTheory.ZH.UFib.exists_red_of_pure | exact GlobalTheory.ZH.UFib.exists_red_of_pure | (intros; apply GlobalTheory.ZH.UFib.exists_red_of_pure <;> assumption)
end
end
