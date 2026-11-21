module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ModelData

def Labels {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La)
    (ζ : ℕ → Oˣ) (lab : ∀ k : ℕ, La → N.QT k) : Prop :=
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a * lab k b) (lab k (a + b))) ∧
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ ∃ e, a = b + k • e) ∧
  (∀ k, 0 < k → ∀ p, ∃ a, N.QEq (lab k a) p) ∧
  (∀ k m, 0 < k → 0 < m → ∀ a (p : N.QT k), p.1.1 = (lab (k * m) a).1.1 → p.1.2 = (lab (k * m) a).1.2 ^ m →
    N.QEq p (lab k a)) ∧
  ∀ k, 0 < k → ∀ a b, N.wp (lab k a) (lab k b) = ζ k ^ EF a b

def Strict {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) : Prop :=
  ∃ c : L.ι → L'.ι, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι), F (r z) ∈ L.U j →
    r z ∈ L'.U (c j) ∧ gw w r z j (c j) = 1

theorem exists_strict {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) :
    ∃ w : LB.Iso (L.pull F) (L.pull F), w.IsGen ∧ Strict w := by
  have hL' : (L.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 X') y _ hy, map_one, gm_pull_g L F (𝟙 X') y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 X') y _ hy, gm_res (𝟙 X') y _ hy, gm_res (𝟙 X') y _ hy, gm_pull_g L F (𝟙 X') y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 X') y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 X') y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  refine ⟨⟨fun j => (L.pull F).g j.1 j.2⟩, (isGen_iff _).2 fun Y f y j j' k k' hj hj' hk hk' => ?_,
    fun j _ => j, fun Z r z j hj => ⟨mem_pull.2 hj, gm_self hL' r z (mem_pull.2 hj)⟩⟩
  have a := gm_cocycle hL' f y (i := fun _ => j) (j := fun _ => j') (k := k') (mem_pull.2 hj) (mem_pull.2 hj') hk'
  have b := gm_cocycle hL' f y (i := fun _ => j) (j := k) (k := k') (mem_pull.2 hj) hk hk'
  have c := gm_pull_g L F f y (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [c, ← b] at a
  show gm f y _ ((L.pull F).g (fun _ => j) k) = _ * _ * gm f y _ ((L.pull F).g (fun _ => j') k')
  rw [mul_right_comm, a, mul_inv_cancel_right]

end GlobalTheory.ModelData
