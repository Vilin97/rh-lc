module

public import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits
import Development.EtaleCohomology.EtaleSheaves.CechLevels.CechLevelsOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits
import Development.EtaleCohomology.EtaleSheaves.CechLevels
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

-- Source module: Development.EtaleCohomology.EtaleSheaves.CechLevels.Cech0Iso

section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf

def cech0Iso (f : Arrow PSh) : f.cechNerve.obj (op (SimplexCategory.mk 0)) ≅ f.left where
  hom := WidePullback.π _ 0
  inv := WidePullback.lift f.hom (fun _ => 𝟙 _) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; rw [Fin.fin_one_eq_zero j]; rw [Category.assoc]; erw [WidePullback.lift_π, Category.comp_id]
    · rw [Category.assoc]; erw [WidePullback.lift_base, Category.id_comp]; exact WidePullback.π_arrow _ 0
  inv_hom_id := by erw [WidePullback.lift_π]

theorem level0 : Level0 := by
  intro A A' _ _ φ I
  refine ⟨Arrow.isoMk (cech0Iso _) (cech0Iso _) ?_⟩
  simp only [cech0Iso, psi, Arrow.mk_hom, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]
  rfl

theorem CechLevels_of' (hL : Levels) : LateralTheory.E.t_E1Cut.CechLevels := CechLevels_of hL level0

end LateralTheory.E.CechLevelsPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.SpecLimPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.SpecLimPf
open LateralTheory.E.LevelsGenPf

def gam {T : Scheme.{0}} {R : Type} [CommRing R] (x : T ⟶ Spec (CommRingCat.of R)) : R →+* Γ(T, ⊤) :=
  ((ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm x).unop.hom

def uns {T : Scheme.{0}} {R : Type} [CommRing R] (h : R →+* Γ(T, ⊤)) : T ⟶ Spec (CommRingCat.of R) :=
  ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R)) (CommRingCat.ofHom h).op

theorem gam_uns {T : Scheme.{0}} {R : Type} [CommRing R] (h : R →+* Γ(T, ⊤)) : gam (uns h) = h := by
  have e := (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm_apply_apply (CommRingCat.ofHom h).op
  simp only [gam, uns]
  erw [e]
  rfl

theorem gam_inj {T : Scheme.{0}} {R : Type} [CommRing R] {x y : T ⟶ Spec (CommRingCat.of R)}
    (h : gam x = gam y) : x = y := by
  apply (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm.injective
  apply Opposite.unop_injective
  exact CommRingCat.hom_ext h

theorem gam_comp {T : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (x : T ⟶ Spec (CommRingCat.of S)) : gam (x ≫ Spec.map (CommRingCat.ofHom f)) = (gam x).comp f := by
  have := ΓSpec.adjunction.homEquiv_naturality_right_symm x (CommRingCat.ofHom f).op
  simp only [gam]
  erw [this]
  rfl

theorem SpecLim_of : SpecLim := by
  intro A A' B _ _ _ φ χ n l hl hcop
  refine ⟨evaluationJointlyReflectsLimits _ fun k => ?_⟩
  obtain ⟨T⟩ := k

  let F := WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : Fin (n + 1) => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))
  have key : ∀ (s : Cone (F ⋙ (evaluation _ _).obj (op T))) (p : s.pt),
      ∀ i, (gam (s.π.app (some i) p)).comp φ = gam (s.π.app none p) := by
    intro s p i
    have h : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) =
        (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) ≫ Spec.map (CommRingCat.ofHom φ) :=
      (types_congr_hom (s.w (WidePullbackShape.Hom.term i)) p).symm
    rw [h]
    exact (gam_comp φ _).symm
  refine IsLimit.mk (fun s => TypeCat.ofHom fun p => uns (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p))
      (key s p)).exists.choose) ?_ ?_
  · intro s j
    ext p
    have hs := (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)).exists.choose_spec
    rcases j with _ | i
    · apply gam_inj
      change gam (uns _ ≫ Spec.map (CommRingCat.ofHom χ)) = _
      rw [gam_comp, gam_uns, hs.2]
      rfl
    · apply gam_inj
      change gam (uns _ ≫ Spec.map (CommRingCat.ofHom (l i))) = _
      rw [gam_comp, gam_uns, hs.1 i]
      rfl
  · intro s m hm
    ext p
    have H := hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)
    change (m p : T ⟶ Spec (CommRingCat.of B)) = uns _
    apply gam_inj
    rw [gam_uns]
    refine H.unique ⟨fun i => ?_, ?_⟩ H.exists.choose_spec
    · have e : (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) =
          (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom (l i)) :=
        (types_congr_hom (hm (some i)) p).symm
      change _ = gam (s.π.app (some i) p)
      rw [e]
      exact (gam_comp _ _).symm
    · have e : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) =
          (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom χ) :=
        (types_congr_hom (hm none) p).symm
      rw [e]
      exact (gam_comp _ _).symm

end LateralTheory.E.SpecLimPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.QuotCop

section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

theorem quotCop : QuotCop := by
  intro A A' B _ _ _ φ χ ι l hl I hcop R _ g c hg
  have hg' : ∀ i, ((g i).comp (Ideal.Quotient.mk (I.map φ))).comp φ = c.comp (Ideal.Quotient.mk I) := by
    intro i
    rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, hg i]
  obtain ⟨h', ⟨h'l, h'c⟩, h'u⟩ := hcop R _ _ hg'
  have hk : ∀ b ∈ I.map χ, h' b = 0 := by
    intro b hb
    have : I.map χ ≤ RingHom.ker h' := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change h' (χ a) = 0
      rw [← RingHom.comp_apply, h'c, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact this hb
  refine ⟨Ideal.Quotient.lift _ h' hk, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, lq, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' (l i), h'l i, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, qm, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' χ, h'c, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    have : h2.comp (Ideal.Quotient.mk _) = h' := by
      apply h'u
      refine ⟨fun i => ?_, ?_⟩
      · rw [RingHom.comp_assoc, ← Ideal.quotientMap_comp_mk (le_l φ χ (l i) (hl i) I), ← RingHom.comp_assoc]
        exact congrArg (fun f => RingHom.comp f (Ideal.Quotient.mk (I.map φ))) (h2l i)
      · rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, h2c]
    rw [this]
    ext x
    simp

end LateralTheory.E.LevelsGenPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.TensCop

section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

open PiTensorProduct in
theorem tensCop : TensCop := by
  intro A A' _ _ φ n
  letI : Algebra A A' := φ.toAlgebra
  refine ⟨PiTensorProduct A (fun _ : Fin (n + 1) => A'), inferInstance, algebraMap A _, fun i => (singleAlgHom (A := fun _ => A') i).toRingHom,
    fun i => ?_, ?_, ?_⟩
  · exact (singleAlgHom (A := fun _ => A') i).comp_algebraMap
  · rw [eq_top_iff]
    intro x _
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [Algebra.smul_def]
      refine Subring.mul_mem _ ?_ ?_
      · rw [← (singleAlgHom (A := fun _ => A') 0).commutes r]
        exact Subring.subset_closure (Set.mem_iUnion.2 ⟨0, _, rfl⟩)
      · have : tprod A f = ∏ i, singleAlgHom (A := fun _ => A') i (f i) := by
          simp only [singleAlgHom_apply, ← tprod_prod]
          congr 1
          exact (Finset.univ_prod_mulSingle f).symm
        rw [this]
        exact Subring.prod_mem _ fun i _ => Subring.subset_closure (Set.mem_iUnion.2 ⟨i, _, rfl⟩)
    | add x y hx hy => exact Subring.add_mem _ (hx trivial) (hy trivial)
  · intro R _ g c hg
    letI : Algebra A R := c.toAlgebra
    have hc : ∀ i r, g i (algebraMap A A' r) = algebraMap A R r := fun i r => by
      change g i (φ r) = c r
      rw [← RingHom.comp_apply, hg i]
    let ga : Fin (n + 1) → (A' →ₐ[A] R) := fun i => AlgHom.mk (g i) (hc i)
    let F : (Π _ : Fin (n + 1), A') →ₘₗ[A] R :=
      (MultilinearMap.mkPiAlgebra A (Fin (n + 1)) R).compLinearMap (fun i => (ga i).toLinearMap)
    let H := liftAlgHom F (by simp [F]) (by intro x y; simp [F, Finset.prod_mul_distrib])
    have hH : ∀ i a, H (singleAlgHom (A := fun _ => A') i a) = g i a := by
      intro i a
      change lift F (tprod A (MonoidHom.mulSingle (fun _ => A') i a)) = _
      rw [lift.tprod]
      simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      rw [Finset.prod_eq_single i]
      · simp [ga]
      · intro j _ hj
        simp [ga, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
      · simp
    refine ⟨H.toRingHom, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
    · ext a
      exact hH i a
    · ext a
      exact H.commutes a
    · have hc2 : ∀ r, h2 (algebraMap A (PiTensorProduct A (fun _ : Fin (n + 1) => A')) r) = algebraMap A R r := fun r => by
        change h2 (algebraMap A _ r) = c r
        rw [← RingHom.comp_apply, h2c]
      let H2 : (PiTensorProduct A (fun _ : Fin (n + 1) => A')) →ₐ[A] R := AlgHom.mk h2 hc2
      have : H2 = H := by
        apply PiTensorProduct.algHom_ext
        intro i
        ext a
        change h2 (singleAlgHom (A := fun _ => A') i a) = H (singleAlgHom (A := fun _ => A') i a)
        rw [hH]
        exact RingHom.congr_fun (h2l i) a
      exact congrArg AlgHom.toRingHom this

end LateralTheory.E.LevelsGenPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.LevelsGenOfSpecLim

section

section

namespace LateralTheory.E.LevelsGenPf

theorem LevelsGen_of_specLim (hS : SpecLim) : LateralTheory.E.LevelsPf.LevelsGen := LevelsGen_of tensCop quotCop hS

end LateralTheory.E.LevelsGenPf
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.CechLevels

section

@[expose] public section

namespace UpperTheory.Et.CechLevelsEtaleAxioms

theorem a0 : LateralTheory.E.LevelsGenPf.SpecLim := LateralTheory.E.SpecLimPf.SpecLim_of
theorem a1 : LateralTheory.E.LevelsPf.LevelsGen := LateralTheory.E.LevelsGenPf.LevelsGen_of_specLim a0
theorem a2 : LateralTheory.E.CechLevelsPf.Levels := LateralTheory.E.LevelsPf.Levels_of_gen a1
theorem a3 : LateralTheory.E.t_E1Cut.CechLevels := LateralTheory.E.CechLevelsPf.CechLevels_of' a2

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.CechLevels := a3

end UpperTheory.Et.CechLevelsEtaleAxioms
end
end
