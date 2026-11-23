module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfIsNilDP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFrobeniusSemilinearBijective
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFrobeniusSemilinearBijectiveStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystalline_thickening_pullback_bijective : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] [Module.Flat R D] (π : D →+* R) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : R, π (algebraMap R D a) = a) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (t : X ⟶ Sp D) (φ : X ⟶ X), Smooth s → IsSeparated s → QuasiCompact s → t = s ≫ spMap π → φ = 𝟙 X → ∀ m : IsMor (dp0 R) s κ t (algebraMap R D) φ, Function.Bijective (liftSemi m.pull1) := by
  first | exact @GlobalTheory.CrysFlatBC.bijective_liftSemi_pull1 | exact GlobalTheory.CrysFlatBC.bijective_liftSemi_pull1 | (intros; apply GlobalTheory.CrysFlatBC.bijective_liftSemi_pull1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiBijectiveOfExactLarge

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatKerLarge

theorem liftSemi_bijective_of_exact {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    [Module.Flat R R'] {Z M N Z' M' N' : Type*}
    [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']
    (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N')
    (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M')
    (fN : N →ₛₗ[algebraMap R R'] N')
    (hi : Function.Injective i) (hid : Function.Exact i d) (hi' : Function.Injective i')
    (hid' : Function.Exact i' d') (hZ : ∀ z, i' (fZ z) = fM (i z)) (hN : ∀ x, d' (fM x) = fN (d x))
    (hM : Function.Bijective (liftSemi fM)) (hNi : Function.Injective (liftSemi fN)) :
    Function.Bijective (liftSemi fZ) := by
  have sqZ : ∀ w, i' (liftSemi fZ w) = liftSemi fM (i.lTensor R' w) := fun w ↦ by
    induction w with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hZ]
  have sqN : ∀ w, d' (liftSemi fM w) = liftSemi fN (d.lTensor R' w) := fun w ↦ by
    induction w with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hN]
  have hinj : Function.Injective (i.lTensor R') :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (i.lTensor R') (d.lTensor R') := Module.Flat.lTensor_exact R' hid
  refine ⟨fun a b hab ↦ hinj (hM.1 ?_), fun z' ↦ ?_⟩
  · rw [← sqZ, ← sqZ, hab]
  · obtain ⟨m, hm⟩ := hM.2 (i' z')
    have h0 : d.lTensor R' m = 0 := hNi (by rw [← sqN, hm, hid'.apply_apply_eq_zero, map_zero])
    obtain ⟨w, rfl⟩ := (hex m).1 h0
    exact ⟨w, hi' (by rw [sqZ, hm])⟩

theorem liftSemi_bijective_of_exact_large : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type 1) [AddCommGroup Z] [Module R Z] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type 1) [AddCommGroup N] [Module R N] (Z' : Type 1) [AddCommGroup Z'] [Module R' Z'] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type 1) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi
  exact liftSemi_bijective_of_exact i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi

end GlobalTheory.FlatKerLarge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickenin

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem primCris_isBC_of_nilThick : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  intro A₀ _ g hA _ D _ _ π κ hκ hπ k
  haveI : Smooth A₀.hom := hA.smooth
  haveI : IsProper A₀.hom := hA.proper
  let P : Over (Sp ℂ) := A₀ ⊗ A₀
  haveI : Smooth P.hom := smooth_tensorObj_hom A₀ A₀
  haveI : IsProper P.hom := by
    change IsProper (A₀ ⊗ A₀).hom
    rw [Over.tensorObj_hom]; infer_instance
  have m2 : IsMor (dp0 ℂ) (P.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) (𝟙 P.left) :=
    ⟨k.dp, by rw [Category.assoc, ← k.base]; simp⟩
  have key : ∀ (f : P ⟶ A₀) (x : FirstDeRham (A₀.hom ≫ 𝟙 _)),
      pullOver κ (spMap π) f (k.isMor.pull1 x) = m2.pull1 (pullOver (dp0 ℂ) (𝟙 _) f x) := by
    intro f x
    have h'' : IsMor (dp0 ℂ) (A₀.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) f.left :=
      ⟨k.dp, by rw [← Category.assoc, Over.w f, Category.assoc, ← k.base]; simp⟩
    exact (IsMor.pullback1_comp k.isMor
        (IsMor.of_over κ (φ := f.left) (by rw [← Category.assoc, Over.w])) h'' (fun _ ↦ rfl)
        (by simp) x).trans
      (IsMor.pullback1_comp (IsMor.of_over (dp0 ℂ) (φ := f.left) (by rw [← Category.assoc, Over.w]))
        m2 h'' (fun _ ↦ rfl) (by simp) x).symm
  have hM : Function.Bijective (liftSemi k.isMor.pull1) :=
    GlobalTheory.T.crystalline_thickening_pullback_bijective ℂ D π κ hκ hπ A₀.left (A₀.hom ≫ 𝟙 _) (A₀.hom ≫ spMap π) (Over.Hom.left (𝟙 A₀))
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) (by simp) k.isMor
  have hN : Function.Bijective (liftSemi m2.pull1) :=
    GlobalTheory.T.crystalline_thickening_pullback_bijective ℂ D π κ hκ hπ P.left (P.hom ≫ 𝟙 _) (P.hom ≫ spMap π) (𝟙 P.left)
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) rfl m2
  have hZ : Function.Bijective (liftSemi k.pull) := by
    refine GlobalTheory.FlatKerLarge.liftSemi_bijective_of_exact_large ℂ D _ _ _ _ _ _ (prim (dp0 ℂ) (𝟙 _) A₀).subtype
      (pullOver (dp0 ℂ) (𝟙 _) μ[A₀] - pullOver (dp0 ℂ) (𝟙 _) (fst A₀ A₀) - pullOver (dp0 ℂ) (𝟙 _) (snd A₀ A₀))
      (prim κ (spMap π) A₀).subtype
      (pullOver κ (spMap π) μ[A₀] - pullOver κ (spMap π) (fst A₀ A₀) - pullOver κ (spMap π) (snd A₀ A₀))
      k.pull k.isMor.pull1 m2.pull1 (Submodule.injective_subtype _) ?_ (Submodule.injective_subtype _) ?_
      (fun _ ↦ rfl) ?_ hM hN.1
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro x
      simp only [LinearMap.sub_apply, map_sub, key]
  refine ⟨hZ, eq_top_iff.2 fun y _ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hZ.2 y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickeninStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  first | exact @GlobalTheory.primCris_isBC_of_nilThick | exact GlobalTheory.primCris_isBC_of_nilThick | (intros; apply GlobalTheory.primCris_isBC_of_nilThick <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PTaylor0

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnPer.TaylorClause

theorem isSep {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (h : IsAbelianScheme A) : A.left.IsSeparated := by
  have : IsProper A.hom := h.proper
  rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from A.hom]
  infer_instance

theorem of_core0 (core : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn) :
    PTaylor := by
  intro I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ h₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP D _ _ π κ hκ hπ N t ht hN j hj
    A' _ φ' h' m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g h₀ hA hg
  have hsp := (GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hm : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by rw [hsp]; trivial
  obtain ⟨m, dd, v, hv⟩ := Submodule.mem_span_set'.1 hm
  choose cs hcs using fun a ↦ (v a).2
  have n : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    have := m'.isMor.comp (liftMor κ h).isMor
    rwa [RingHom.id_comp, hi] at this
  have hn : n.pull1 c.1 = ∑ a, dd a • k.isMor.pull1 (cs a).1 := by
    rw [← IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor n (fun _ ↦ rfl) hi c.1]
    have := congrArg Subtype.val hv
    rw [Submodule.coe_sum] at this
    refine this.symm.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
    rw [← hcs a]
    rfl
  have key := core (F₀ := fibFam u₀) e (fibUnif u₀) (isSep 𝒜 hA) (isSep A₀ hA₀) h0 ⟨fun a ↦ a.elim, trivial⟩
    (fun l _ ↦ (hτ l).symm) φ₀ (fun p _ ↦ (hE p.2).symm) D π κ hκ hπ N t ht hN (j : B →+* D) hj
    (A₀.hom ≫ spMap π) (by rw [Category.comp_id]) n (Over.Hom.left (𝟙 A₀)) rfl k.isMor c.1 per hper m dd
    (fun a ↦ (cs a).1) (fun a l ↦ P₀ l (cs a)) _ (fun _ _ ↦ rfl) (fun a ↦ hP (cs a)) hn x

  rw [← key, crysToDR_apply, ← hv, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, ← hcs a, hd, smul_eq_mul]

theorem pTaylor0 : PTaylor := of_core0 GlobalTheory.AnPer.TaylorCore.main

end GlobalTheory.AnPer.TaylorClause
end
end
end
