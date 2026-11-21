module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModels

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull ev_res ev_appLE le_preimage_inf le_preimage_map le_preimage_mono)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.GrCl

section Frames

variable {X Z : Scheme.{0}} {F : X.Modules} {S : Type} [CommRing S]

def frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') : Matrix (Fin n) (Fin n') Γ(X, U) :=
  ((hm'.basis h').toMatrix (hm.basis h)).transpose

theorem sum_frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (l : Fin n) :
    resM F h (m l) = ∑ l', frMat hm hm' h h' l l' • resM F h' (m' l') := by
  simp only [frMat, Matrix.transpose_apply, Module.Basis.toMatrix_apply, ← hm'.basis_apply h']
  rw [Module.Basis.sum_repr, hm.basis_apply]

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Lin

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : X.Opens}

def tanLin (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) : TanM x t.G →ₗ[S] (Fin n → S) where
  toFun v l := tanEv t (isTan_tv v) h (s l)
  map_add' v w := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 2 (fun i => (tv (![v, w] i)).left) (fun i => isTan_tv _) ![1, 1] _
      (isTan_tv (v + w)) ((LieMet.isComb_iff _ _ _).2 (by simp)) (s l)
    simpa using this
  map_smul' a v := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 1 (fun _ => (tv v).left) (fun _ => isTan_tv _) (fun _ => a) _
      (isTan_tv (a • v)) ((LieMet.isComb_iff (fun _ => v) _ _).2 (by simp)) (s l)
    simpa using this

theorem tanLin_apply (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) (l : Fin n) :
    tanLin t h s v l = tanEv t (isTan_tv v) h (s l) := rfl

theorem tanEv_sum_smul (h : ⊤ ≤ x ⁻¹ᵁ V) {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) {n : ℕ}
    (a : Fin n → Γ(X, V)) (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t hv h (∑ l, a l • s l) = ∑ l, ev x V h (a l) * tanEv t hv h (s l) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have := tanEv_smul t hv h 0 0
    simpa using this
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tanEv_add, tanEv_smul, ih]; rfl

open TopologicalSpace MonoidalCategory MonObj GlobalTheory.LieVB GlobalTheory.Conormal in
open GlobalTheory.QCoh (pullbackSections) in
open GlobalTheory.DualPull (appLE_resG resG_appLE) in
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO) in
open GlobalTheory.CompanionTheory.Ar (dualMap) in
theorem tanLin_tanPull {S' : Type} [CommRing S'] (φ : S →+* S') {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ V)
    (h' : ⊤ ≤ x' ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) :
    tanLin t h' s (tanPull φ e v) = φ ∘ tanLin t h s v := by
  subst e
  funext l
  change tanEv t (isTan_tv (tanPull φ rfl v)) h' (s l) = φ (tanEv t (isTan_tv v) h (s l))
  let v₁ := (tv v).left
  let dφ := spMap (dualMap φ)
  have hv : IsTanAtG t x v₁ := isTan_tv v
  have hv' : IsTanAtG t (spMap φ ≫ x) (dφ ≫ v₁) := isTan_tv (tanPull φ rfl v)
  have hcomp : dφ ≫ (specO S (DualNumber S)).hom = (specO S' (DualNumber S')).hom ≫ spMap φ := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have heps : dφ.appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn S) = epsFn S' := by
    refine congr($(Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (dualMap φ))) DualNumber.eps).symm.trans ?_
    refine congrArg (Scheme.ΓSpecIso (.of (DualNumber S'))).inv.hom ?_
    change dualMap φ DualNumber.eps = _
    ext <;> simp [dualMap]
  let σ := s l
  have hform : ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' σ) : Γ(Sp S', ⊤)) =
      (spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h σ) : Γ(Sp S, ⊤)) := by
    have := t.semi
    have key (y : (⊤ : (Sp S').Opens)) : ∃ T' : (Sp S').Opens, y.1 ∈ T' ∧
        resG (Sp S') (le_top : T' ≤ ⊤) ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' σ) : Γ(Sp S', ⊤)) =
        resG (Sp S') (le_top : T' ≤ ⊤) ((spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
          ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h σ) : Γ(Sp S, ⊤))) := by
      obtain ⟨U, W, hU, hle, c⟩ := exists_isChart (sec_hom (MonObj.one (X := t.G))) (V := V)
        (x := x (spMap φ y.1)) (h trivial)
      obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap φ y.1) hU
      obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := t.G))) (resM _ hle σ)
      have hf' : dUnit t.G c.le f = resM (omega t.G) hle σ := hf
      have hTU' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ U := (spMap φ).preimage_mono hTU
      obtain ⟨⟨a, b⟩, hfibre⟩ := (bijective_add_mul_epsFn S T hT).2
        (v₁.appLE W _ (preimage_le_of_isTanAtG t hv c.le hTU) f)
      have h₁ := tanForm_dUnit t hv c.le hTU f a b hfibre.symm
      have hpre : (specO S' (DualNumber S')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
          dφ ⁻¹ᵁ (specO S (DualNumber S)).hom ⁻¹ᵁ T := (le_preimage_of_comp hcomp).2 le_rfl
      have hpre' : (specO S' (DualNumber S')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
          ((specO S' (DualNumber S')).hom ≫ spMap φ) ⁻¹ᵁ T := le_rfl
      have hcoeff (z : Γ(Sp S, T)) : dφ.appLE _ _ hpre
          ((specO S (DualNumber S)).hom.appLE T _ le_rfl z) =
          (specO S' (DualNumber S')).hom.appLE _ _ le_rfl ((spMap φ).appLE T _ le_rfl z) :=
        (appLE_appLE hcomp _ _ hpre' z).trans (appLE_appLE rfl _ _ hpre' z).symm
      have heps' : dφ.appLE _ _ hpre (resG _ le_top (epsFn S)) = resG _ le_top (epsFn S') :=
        (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans (congrArg _ heps))
      have h₂ := tanForm_dUnit t hv' c.le hTU' f ((spMap φ).appLE T _ le_rfl a)
        ((spMap φ).appLE T _ le_rfl b) (by
          refine (appLE_appLE rfl (preimage_le_of_isTanAtG t hv c.le hTU) hpre _ f).symm.trans ?_
          refine (congrArg (dφ.appLE _ _ hpre) hfibre.symm).trans ?_
          refine (map_add _ _ _).trans ?_
          exact congrArg₂ (· + ·) (hcoeff a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hcoeff b) heps')))
      rw [hf', QCoh.pullbackSections_res] at h₁ h₂
      refine ⟨spMap φ ⁻¹ᵁ T, hyT, ?_⟩
      refine (app_resM (tanForm t hv') le_top _).symm.trans ?_
      rw [QCoh.res_pullbackSections, h₂, ← h₁]
      refine .trans ?_ ((appLE_resG (spMap φ) (le_top : T ≤ ⊤) le_rfl _).trans
        (resG_appLE (spMap φ) le_top (le_preimage_top _ _) _).symm)
      refine congrArg _ ?_
      refine .trans ?_ (app_resM (tanForm t hv) le_top _)
      rw [QCoh.res_pullbackSections]
    choose T hT hs using key
    exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs
  unfold tanEv
  refine (congrArg (Scheme.ΓSpecIso (.of S')).hom hform).trans ?_
  refine (congrArg (Scheme.ΓSpecIso (.of S')).hom (appLE_top (spMap φ) _)).trans ?_
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) _)

theorem tanLin_injective (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) {U : X.Opens} (e : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hs : VB.IsFrame fun l => resM _ e (s l)) : Function.Injective (tanLin t h s) := fun v w hvw =>
  tan_ext ((GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x U hU n _ hs (tanLin t h s w)).unique
    ⟨isTan_tv v, fun l => (tanEv_resM t _ hU e _).trans (congrFun hvw l)⟩
    ⟨isTan_tv w, fun _ => tanEv_resM t _ hU e _⟩)

end Lin

section Phi

variable {X X' X₀ Z : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {t₀ : SAB H X₀} {τ : X ⟶ X₀} {τ' : X' ⟶ X₀}
  (mu : SABMap t t₀ τ) (mu' : SABMap t' t₀ τ') {π : Z ⟶ X} {g : Z ⟶ X'} (e : g ≫ τ' = π ≫ τ)
  {S : Type} [CommRing S]

end Phi

end GlobalTheory.GrCl
