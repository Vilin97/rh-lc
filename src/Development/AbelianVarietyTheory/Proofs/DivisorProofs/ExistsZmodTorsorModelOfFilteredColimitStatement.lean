module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyZmodTorsorGaloisProductMapBijectiveColStatement
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
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
public import Mathlib.RingTheory.Extension.Presentation.Core
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLateSplitOfFilteredColimitStatement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebraStatement
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePresentationModelOfIsColimitStatement

section

@[expose] public section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_finitePresentation_descent_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc D _ _ hD
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let P := Algebra.Presentation.ofFinitePresentation c.pt D
  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨F.map f (x y), ?_⟩
    have hw := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
    rw [hw]
    exact hx y
  let : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra
  have : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : P.HasCoeffs (F.obj j) := ⟨hj⟩
  exact ⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSplittingUnitFaithfullyFlat

section

@[expose] public section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem unit_splits_of_projective_faithfullyFlat :
    ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  intro R D _ _ _ _ hP hF
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hP
  let ev : (D →ₗ[R] R) →ₗ[R] R :=
    { toFun := fun τ => τ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  by_cases hI : LinearMap.range ev = ⊤
  · obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp (hI ▸ Submodule.mem_top : (1 : R) ∈ LinearMap.range ev)
    exact ⟨τ, hτ⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal (LinearMap.range ev) hI
  exfalso
  have hcoord : ∀ x : D, s 1 x ∈ m := fun x =>
    hIm (LinearMap.mem_range.mpr ⟨Finsupp.lapply x ∘ₗ s, rfl⟩)
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by
    have : Finsupp.linearCombination R id (s 1) = (1 : D) := LinearMap.congr_fun hs 1
    rw [← this, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem_smul (hcoord x) Submodule.mem_top
  have hmul : ∀ d : D, ∀ y ∈ m • (⊤ : Submodule R D), d * y ∈ m • (⊤ : Submodule R D) := by
    intro d y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x z hx hz
      rw [mul_add]; exact Submodule.add_mem _ hx hz
  apply Module.FaithfullyFlat.submodule_ne_top (M := D) hm
  rw [eq_top_iff]
  intro d _
  simpa using hmul d 1 h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSplittingUnitFaithfullyFlatStatement

section

@[expose] public section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  first | (exact @GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (exact GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (intros; apply GlobalTheory.unit_splits_of_projective_faithfullyFlat  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFilteredStatement

section

@[expose] public section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  first | (exact @GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_action_model_of_isColimit  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimit

section

@[expose] public section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem faithfullyFlat_of_split : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Projective R D →
    (∃ τ : D →ₗ[R] R, τ 1 = 1) → Module.FaithfullyFlat R D := by
  intro R D _ _ _ hP ⟨τ, hτ⟩
  haveI : Module.Flat R D := inferInstance
  refine ⟨fun m hm h => ?_⟩
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by rw [h]; exact Submodule.mem_top
  have h2 : ∀ x ∈ m • (⊤ : Submodule R D), τ x ∈ m := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr d _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, smul_eq_mul]; exact m.mul_mem_right _ hr
    · rw [map_add (f := _)]; exact m.add_mem hx hy
  have := h2 1 h1
  rw [hτ] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)

theorem isZModTorsor_of_algEquiv : ∀ (R D D' : Type) [CommRing R] [CommRing D] [CommRing D'] [Algebra R D] [Algebra R D'] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[R] D)) (act' : Multiplicative (ZMod q) →* (D' ≃ₐ[R] D'))
    (e : D ≃ₐ[R] D'), (∀ (g : Multiplicative (ZMod q)) (x : D), e (act g x) = act' g (e x)) →
    GlobalTheory.LocAcyc.IsZModTorsor R D q act → GlobalTheory.LocAcyc.IsZModTorsor R D' q act' := by
  intro R D D' _ _ _ _ _ q act act' e he hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  have el : D ≃ₗ[R] D' := e.toLinearEquiv
  refine ⟨Module.Finite.equiv el, Module.Projective.of_equiv el, ?_, ?_⟩
  · exact Module.FaithfullyFlat.of_linearEquiv R D el.symm
  · let eT : D ⊗[R] D ≃ₐ[R] D' ⊗[R] D' := Algebra.TensorProduct.congr e e
    let eP : (Multiplicative (ZMod q) → D) ≃ₐ[R] (Multiplicative (ZMod q) → D') :=
      AlgEquiv.piCongrRight (fun _ => e)
    have key : ∀ x, GlobalTheory.TorsorColim.prodMapOf R D' q act' (eT x) = eP (GlobalTheory.TorsorColim.prodMapOf R D q act x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        funext g
        simp [eT, eP, he]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    have hb : Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D q act) := h4
    have : ⇑(GlobalTheory.TorsorColim.prodMapOf R D' q act') = eP ∘ (GlobalTheory.TorsorColim.prodMapOf R D q act) ∘ eT.symm := by
      funext y
      simp only [Function.comp_apply]
      rw [← key, AlgEquiv.apply_symm_apply]
    change Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D' q act')
    rw [this]
    exact eP.bijective.comp (hb.comp eT.symm.bijective)

theorem exists_torsor_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc q hq D _ _ act hD
  haveI : Module.Finite c.pt D := hD.1
  haveI : Module.Projective c.pt D := hD.2.1
  haveI : Module.FinitePresentation c.pt D := Module.finitePresentation_of_projective c.pt D
  obtain ⟨j, A, _, _, _, he0⟩ := GlobalTheory.T.exists_finitePresentation_descent_of_isColimit J F c hc D inferInstance
  obtain ⟨k, B, _, _, _, actB, e, he⟩ := GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered J F c hc q hq j A D act he0
  letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra
  have hT : GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj k] B) q
      (GlobalTheory.TorsorColim.bcAct c.pt actB) := by
    refine GlobalTheory.TorsorColim.isZModTorsor_of_algEquiv c.pt D _ q act _ e.symm (fun g y => ?_) hD
    apply e.injective
    rw [he, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have h1 := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc k B hT.1
  have h2 := GlobalTheory.T.projective_eventually_filteredColimit_algebra J F c hc k B ⟨hT.1, hT.2.1⟩
  have h3 := GlobalTheory.T.exists_late_split_of_filteredColimit J F c hc k B ⟨hT.1, GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat _ _ hT.1 hT.2.1 hT.2.2.1⟩
  have h4 := GlobalTheory.T.eventually_zmodTorsorGaloisProductMap_bijective_colimit J F c hc q hq k B actB hT
  have h34 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; ∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h3 h4
  have h234 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h2 h34
  obtain ⟨m, f₀, hm⟩ := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Finite (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B) ∧ (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h1 h234
  obtain ⟨i1, i2, ⟨τ, hτ⟩, i4⟩ := hm m (𝟙 m)
  refine ⟨m, ?_⟩
  letI : Algebra (F.obj k) (F.obj m) := (F.map (f₀ ≫ 𝟙 m)).hom.toAlgebra
  letI : Algebra (F.obj m) c.pt := (c.ι.app m).hom.toAlgebra
  haveI : IsScalarTower (F.obj k) (F.obj m) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app k).hom x = (c.ι.app m).hom ((F.map (f₀ ≫ 𝟙 m)).hom x)
    rw [← c.w (f₀ ≫ 𝟙 m)]
    rfl)
  exact ⟨F.obj m ⊗[F.obj k] B, inferInstance, inferInstance, GlobalTheory.TorsorColim.bcAct (F.obj m) actB,
    ⟨i1, i2, GlobalTheory.TorsorColim.faithfullyFlat_of_split _ _ i2 ⟨τ, hτ⟩, i4⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange (F.obj k) (F.obj m) c.pt c.pt B).trans e⟩⟩

end GlobalTheory.TorsorColim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimitStatement

section

@[expose] public section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit  <;> assumption)
end
end
