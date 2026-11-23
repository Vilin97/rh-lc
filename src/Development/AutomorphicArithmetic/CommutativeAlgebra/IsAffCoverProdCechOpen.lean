module

public import Development.AutomorphicArithmetic.GenericGermInjectivity.CoverGeneric
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SchemeCechComparisonNaturalRefinementStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormPullbackDominant

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HodgeCoh

section Alg
open GlobalTheory.CechDR

theorem mem_closure_smul_ιMulti_D (k B : Type) [CommRing k] [CommRing B] [Algebra k B] (z : DR k B) :
    z ∈ AddSubgroup.closure {w : DR k B | ∃ (q : ℕ) (c : B) (v : Fin q → B),
      w = c • ExteriorAlgebra.ιMulti B q (fun i => D k B (v i))} := by
  set A := AddSubgroup.closure {w : DR k B | ∃ (q : ℕ) (c : B) (v : Fin q → B),
      w = c • ExteriorAlgebra.ιMulti B q (fun i => D k B (v i))} with hA
  have hsmul : ∀ (b : B) (a : DR k B), a ∈ A → b • a ∈ A := by
    intro b a ha
    induction ha using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨q, c, v, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨q, b * c, v, by rw [smul_smul]⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have key : ∀ z : DR k B, ∀ a ∈ A, z * a ∈ A := by
    intro z
    induction z using indDR with
    | h b => intro a ha; rw [← Algebra.smul_def]; exact hsmul b a ha
    | hd b =>
      intro a ha
      induction ha using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨q, c, v, rfl⟩ := hw
        refine AddSubgroup.subset_closure ⟨q + 1, c, Fin.cons b v, ?_⟩
        rw [mul_smul_comm, ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, Function.comp_def]
      | zero => rw [mul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
      | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | hm x y hx hy => intro a ha; rw [mul_assoc]; exact hx _ (hy a ha)
    | ha x y hx hy => intro a ha; rw [add_mul]; exact add_mem (hx a ha) (hy a ha)
  have h1 : (1 : DR k B) ∈ A :=
    AddSubgroup.subset_closure ⟨0, 1, Fin.elim0, by rw [ExteriorAlgebra.ιMulti_zero_apply, one_smul]⟩
  simpa using key z 1 h1

variable {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']

theorem SemiHom.mDR_ιMulti_D {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (q : ℕ) (v : Fin q → B) :
    h.mDR (ExteriorAlgebra.ιMulti B q fun i => D R B (v i)) =
      ExteriorAlgebra.ιMulti B' q fun i => D R' B' (α (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  exact (SemiHom.mDR_ι h _).trans (congrArg ι1 (SemiHom.m1_D h _))

theorem SemiHom.mDR_mDR {σ : R →+* R'} {α : B →+* B'} {τ : R' →+* R''} {β : B' →+* B''}
    {ρ : R →+* R''} {γ : B →+* B''} (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ)
    (e : ∀ b, β (α b) = γ b) (x : DR R B) : h'.mDR (h.mDR x) = h''.mDR x := by
  induction x using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => simp only [map_mul, hx, hy]
  | ha x y hx hy => simp only [map_add (f := _), hx, hy]

theorem isDRMap_mDR {k K K' : Type} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra k B] {g : B →+* K} {γ : B →+* K'} (hg : SemiHom (RingHom.id k) g)
    (hγ : SemiHom (RingHom.id k) γ) {ψ : K →ₐ[k] K'} {φ : DR k K →ₗ[k] DR k K'}
    (hφ : IsDRMap k ψ φ) (e : ∀ b, ψ (g b) = γ b) (z : DR k B) : φ (hg.mDR z) = hγ.mDR z := by
  induction mem_closure_smul_ιMulti_D k B z using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨q, c, v, rfl⟩ := hw
    rw [SemiHom.mDR_smul, SemiHom.mDR_ιMulti_D, hφ q (g c) (fun i => g (v i)), SemiHom.mDR_smul,
      SemiHom.mDR_ιMulti_D]
    simp only [e]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  | neg x _ hx => rw [map_neg, map_neg, hx, map_neg]

end Alg

theorem formGermI_res_mapOver : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (p : Z ⟶ Sp ℂ) (p' : Z' ⟶ Sp ℂ),
    letI := algΓ p; letI := algΓ p'
    ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField] (hinst : inst = ffAlg p)
      (hinst' : inst' = ffAlg p') (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
      (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField), IsDRMap ℂ ψ φ →
      (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) →
      ∀ (j : ℕ) (V : Z.Opens) (V' : Z'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
        (hη : genericPoint Z ∈ V) (hη' : genericPoint Z' ∈ V') (h : V' ≤ f ⁻¹ᵁ V)
        (y : sectionsOn (Omega p j) V),
        formGermI p' j hV' hη' hinst' (sectionsOn.res ℂ (Omega p' j) h
          (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
          φ (formGermI p j hV hη hinst y) := by
  intro Z Z' _ _ p p' inst inst' hinst hinst' f hf ψ φ hφ hψ j V V' hV hV' hη hη' h y
  subst hinst hinst'
  letI := algΓ p; letI := algΓ p'
  set x := (toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y) with hx
  have hy : sectionsOn.toΓ _ _ y = toOm p j V x := by
    exact (LinearEquiv.apply_symm_apply (toOmEquiv p j hV) _).symm
  have hz : sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p' j) h
      (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
      toOm p' j V' (formRes p' h j (formPull hf V j x)) := by
    have h2 : (omegaPull hf j).app V (toOm p j V x) = toOm p' j (f ⁻¹ᵁ V) (formPull hf V j x) :=
      omegaPull_toOmega hf j V x
    rw [sectionsOn.toΓ_res, sectionsOn.toΓ_mapOver, hy, h2, res_toOm]
  letI := ffAlg p; letI := ffAlg p'
  rw [formGermI_ffAlg, formGermI_ffAlg]
  simp only [formGerm, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hz, ← toOmEquiv_apply p' j hV', LinearEquiv.symm_apply_apply, ← hx]
  have hγ : SemiHom (RingHom.id ℂ) ((germSec p' (h hη')).comp (appSec p p' f V)) :=
    fun r b ↦ (semiHom_appSec hf V).comp (semiHom_germSec p' (h hη')) r b
  rw [isDRMap_mDR (semiHom_germSec p hη) hγ hφ (fun b ↦ hψ V hη (h hη') b)]
  change (semiHom_germSec p' hη').mDR ((SemiHom.of_algHom (Sec.res p' h)).mDR
    ((semiHom_appSec hf V).mDR (x : DR ℂ (Sec p V)))) = _
  rw [SemiHom.mDR_mDR (semiHom_appSec hf V) (SemiHom.of_algHom (Sec.res p' h))
    ((semiHom_appSec hf V).comp (SemiHom.of_algHom (Sec.res p' h))) (fun _ ↦ rfl)]
  refine SemiHom.mDR_mDR _ (semiHom_germSec p' hη') hγ (fun b ↦ ?_) _
  change (Z'.presheaf.germ V' (genericPoint Z') hη').hom
      ((Z'.presheaf.map (homOfLE h).op).hom ((f.app V).hom b)) =
    (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') (h hη')).hom ((f.app V).hom b)
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

end GlobalTheory.HodgeCoh
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermDifferentialFormPullbackDominantStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.genericGerm_differentialForm_pullback_dominant : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (p : Z ⟶ Sp ℂ) (p' : Z' ⟶ Sp ℂ),
    letI := algΓ p; letI := algΓ p'
    ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField] (hinst : inst = ffAlg p)
      (hinst' : inst' = ffAlg p') (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
      (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField), IsDRMap ℂ ψ φ →
      (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) →
      ∀ (j : ℕ) (V : Z.Opens) (V' : Z'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
        (hη : genericPoint Z ∈ V) (hη' : genericPoint Z' ∈ V') (h : V' ≤ f ⁻¹ᵁ V)
        (y : sectionsOn (Omega p j) V),
        formGermI p' j hV' hη' hinst' (sectionsOn.res ℂ (Omega p' j) h
          (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
          φ (formGermI p j hV hη hinst y) := by
  first | (exact @GlobalTheory.HodgeCoh.formGermI_res_mapOver) | (exact GlobalTheory.HodgeCoh.formGermI_res_mapOver) | (intros; apply GlobalTheory.HodgeCoh.formGermI_res_mapOver  <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffCoverProdCechOpen

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.GenericCoverClass

theorem UpperTheory.isAffCover_prod_cechOpen :
    ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B)
            (d' : ℕ) (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [SmoothOfRelativeDimension d' p'] [inst' : Algebra ℂ Z'.functionField] (κ : Type) [LinearOrder κ] [Fintype κ] (U' : κ → Z'.Opens) (B' : Finset κ → Subalgebra ℂ Z'.functionField) (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' U' B')
            (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField) (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι),
            IsDRMap ℂ ψ φ → (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)), ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) → (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) →
            ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Z.functionField (B I) a) (cech fun I => omB ℂ Z'.functionField (B' I) a) (pullC τ φ)) (z : hodgeH p a b),
              cmp d' p' hinst' hU' a b (hodgePull hf a b z) = Cx.hmap _ _ (pullC τ φ) hm b (cmp d p hinst hU a b z) := by
  classical
  intro d Z _ p _ inst ι _ _ U B hinst hU d' Z' _ p' _ inst' κ _ _ U' B' hinst' hU' f hf ψ φ τ hDR hψ hUU' a b hm z
  letI := algΓ p
  letI := algΓ p'
  have hσ := appTop_algebraMap (k := ℂ) hf
  have hcov : ⨆ i, U i = ⊤ := hU.cover
  have haff : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) := fun s hs => cover_biInf hU s hs
  have hcov' : ⨆ i, U' i = ⊤ := hU'.cover
  have haff' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i) := fun s hs => cover_biInf hU' s hs
  obtain ⟨x, hx⟩ := (cechClass_surjective (cechCube ℂ (Omega p a) ⊤ U) b)
    ((cechHEquivCoh ℂ hcov haff (Omega p a) b).symm z)
  have hz : cechHEquivCoh ℂ hcov haff (Omega p a) b (cechClass (cechCube ℂ (Omega p a) ⊤ U) b x) = z := by
    rw [hx]
    exact LinearEquiv.apply_symm_apply _ _
  obtain ⟨eZ, -, heZ, -⟩ := cube_exists d p hinst hU a b
  obtain ⟨w, hw⟩ := heZ x
  have hle : ∀ t : Finset κ, cechOpen ⊤ U' t ≤ f ⁻¹ᵁ cechOpen ⊤ U (Finset.image τ t) := by
    intro t y hy
    rw [mem_cechOpen] at hy
    show f.base y ∈ cechOpen ⊤ U (Finset.image τ t)
    rw [mem_cechOpen]
    refine ⟨trivial, fun i hi => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact hUU' k (hy.2 k hk)
  have hcard : ∀ t : {s : Finset κ // s.card = b + 1}, Set.InjOn τ t.1 → (Finset.image τ t.1).card = b + 1 :=
    fun t hinj => (Finset.card_image_of_injOn hinj).trans t.2
  let x' : (cechCube ℂ (Omega p' a) ⊤ U').Term (b + 1) := fun t =>
    if hinj : Set.InjOn τ t.1 then
      sortSign τ t.1 • sectionsOn.res ℂ (Omega p' a) (hle t.1)
        (sectionsOn.map ℂ (omegaPull hf a) (cechOpen ⊤ U (Finset.image τ t.1)) (x.1 ⟨_, hcard t hinj⟩))
    else 0
  have hwC := hm b w w.2.1
  have hw'mem : pullC τ φ (w : Finset ι → DR ℂ Z.functionField) ∈
      (cech fun I => omB ℂ Z'.functionField (B' I) a).Z b := by
    have hw0 : (cech fun I => omB ℂ Z.functionField (B I) a).D (w : Finset ι → DR ℂ Z.functionField) = 0 :=
      w.2.2
    have h0 : (cech fun I => omB ℂ Z'.functionField (B' I) a).D (pullC τ φ (w : Finset ι → DR ℂ Z.functionField)) = 0 := by
      rw [← hwC.2, hw0, map_zero]
    exact ⟨hwC.1, h0⟩
  let w' : ↥((cech fun I => omB ℂ Z'.functionField (B' I) a).Z b) := ⟨_, hw'mem⟩
  have hgm : ∀ t : {s : Finset κ // s.card = b + 1},
      (w' : Finset κ → DR ℂ Z'.functionField) t.1 = gm p' hinst' hU' a t.1 (x' t) := by
    intro t
    have ht : t.1.Nonempty := Finset.card_pos.mp (by rw [t.2]; omega)
    rw [gm_pos hinst' hU' a ht]
    by_cases hinj : Set.InjOn τ t.1
    · have hne : (Finset.image τ t.1).Nonempty := ht.image τ
      have e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 =
          sortSign τ t.1 • φ ((w : Finset ι → DR ℂ Z.functionField) (Finset.image τ t.1)) := by
        show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _
        simp only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_pos hinj]
      rw [e1, show x' t = _ from dif_pos hinj]
      refine Eq.trans ?_ (map_zsmul (formGermI p' a _ _ hinst') (sortSign τ t.1) _).symm
      rw [hw ⟨_, hcard t hinj⟩, gm_pos hinst hU a hne]
      congr 1
      exact (T.genericGerm_differentialForm_pullback_dominant Z Z' p p' hinst hinst' f hf ψ φ hDR hψ a _ _ _ _ _ _ (hle t.1) _).symm
    · have e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 = 0 := by
        show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _
        simp only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_neg hinj]
      rw [e1, show x' t = 0 from dif_neg hinj]
      exact (map_zero (formGermI p' a _ _ hinst')).symm
  obtain ⟨eY, -, -, hdY⟩ := cube_exists d' p' hinst' hU' a b
  have hker : x' ∈ ((cechCube ℂ (Omega p' a) ⊤ U').d (b + 1)).ker := hdY x' w' hgm
  have hR : cechHEquivCoh ℂ hcov' haff' (Omega p' a) b
      (cechClass (cechCube ℂ (Omega p' a) ⊤ U') b ⟨x', hker⟩) = hodgePull hf a b z := by
    refine (T.scheme_cechComparison_natural_refinement Z Z' ℂ f hσ _ _ (omegaPull hf a) ι κ U U' hcov haff hcov' haff' τ hUU' b x
      ⟨x', hker⟩ ?_ ?_).trans ?_
    · intro t s h hinj hs
      obtain ⟨s, hsc⟩ := s
      simp only at hs
      subst hs
      exact dif_pos hinj
    · intro t hinj
      exact dif_neg hinj
    · rw [hz]
      rfl
  rw [← hR, cmp_class d' p' hinst' hU' a b ⟨x', hker⟩ w' hgm, ← hz, cmp_class d p hinst hU a b x w hw]
  rfl
end
end
