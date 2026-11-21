module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsKSR (Φ : Finset (E →+* ℂ)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (x' : Sp (DualNumber S) ⟶ Xo.X) (M : HIx Dw Φ → S) : Prop :=
  ∃ (A : Over (Sp S)) (_ : GrpObj A) (A' : Over (Sp (DualNumber S))) (_ : GrpObj A')
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (epsRed S) i) (ψ : LinearMap.BilinForm S (HdR A))
    (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A),
    IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧
    IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
    (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧
    ∀ (τ : Φ) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, IsLieComb (fun b => M ⟨τ, a, b⟩) (ub τ.1) w ∧
      IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w

theorem isKSR_iff_isKS {Φ : Finset (E →+* ℂ)} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {x' : Sp (DualNumber K) ⟶ Xo.X} {M : HIx Dw Φ → K} : IsKSR Φ y x' M ↔ IsKS Φ y x' M := Iff.rfl

theorem IsKSR.baseChange (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {S S' : Type} [CommRing S] [Algebra c.F S]
    [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap ψ y y')
    {x : Sp (DualNumber S) ⟶ Xo.X} {M : HIx Dw Φ → S}
    (hM : IsKSR Φ y x M) : IsKSR Φ y' (spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ArcQ GlobalTheory.CompanionTheory.Ar in open scoped CategoryTheory.Obj CategoryTheory.MonObj in by
  letI {T : Scheme.{0}} (X Y : Over T) [GrpObj Y] : Monoid (X ⟶ Y) := CategoryTheory.Hom.monoid
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  letI : Algebra S S' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap S S'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap S S')))
  have e₀ : spMap (algebraMap S S') ≫ epsRed S = epsRed S' ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ epsRed S') ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap S S')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (epsRed S') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have abPull {T T' : Scheme.{0}} {G : Over T} {G' : Over T'} [GrpObj G] [GrpObj G']
      {f : T' ⟶ T} {φ : G'.left ⟶ G.left} (hG : IsAbelianScheme G)
      (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' := by
    have := hG.comm
    have hc : IsCommMonObj G' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro U
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 U x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 U y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl]
      letI : CommMonoid (Over.mk (U.hom ≫ f) ⟶ G) := CategoryTheory.Hom.commMonoid
      exact congrArg (·.left) (mul_comm (pushPt h.1.w x) (pushPt h.1.w y))
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected⟩
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := abPull hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := abPull hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 S A _ hA gA S' B φ hφ
  have hL := (P.2.1 S' B _ (abPull hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  have dual_over : spMap (dualMap (algebraMap S S')) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap (algebraMap S S') := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have dual_scale (a : S) : spMap (dualMap (algebraMap S S')) ≫ spMap (epsScaleR a) =
      spMap (epsScaleR (algebraMap S S' a)) ≫ spMap (dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext r <;> simp [dualMap, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have exBase (v : epsR S ⟶ A) : ∃ u : epsR S' ⟶ B,
      u.left ≫ φ = spMap (dualMap (algebraMap S S')) ≫ v.left := by
    have hv : v.left ≫ A.hom = spMap (algebraMap S (DualNumber S)) := Over.w v
    have ee : (spMap (dualMap (algebraMap S S')) ≫ v.left) ≫ A.hom =
        (epsR S').hom ≫ spMap (algebraMap S S') := by
      rw [Category.assoc, hv]; exact dual_over
    exact ⟨Over.homMk (hφ.1.lift _ _ ee) (hφ.1.lift_snd _ _ _), hφ.1.lift_fst _ _ _⟩
  choose tv htv using exBase
  let sc {R : Type} [CommRing R] (s : R) : epsR R ⟶ epsR R :=
    Over.homMk (spMap (epsScaleR s)) (by
      show spMap (epsScaleR s) ≫ spMap (algebraMap R (DualNumber R)) = _
      rw [← Cris.spMap_comp]
      congr 1
      ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
  have comb_iff {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
      (cf : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (z : epsR R ⟶ G) :
      IsLieComb cf v z ↔ z = (List.ofFn fun i => sc (cf i) ≫ v i).prod := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [show u = fun i => sc (cf i) ≫ v i from funext fun i => Over.OverMorphism.ext (hu i)]
    · rintro rfl
      exact ⟨_, fun i => rfl, rfl⟩
  have combBase {n : ℕ} {cf : Fin n → S} {v : Fin n → (epsR S ⟶ A)} {z : epsR S ⟶ A}
      {u : Fin n → (epsR S' ⟶ B)} {z' : epsR S' ⟶ B}
      (hu : ∀ i, (u i).left ≫ φ = spMap (dualMap (algebraMap S S')) ≫ (v i).left)
      (hz : z'.left ≫ φ = spMap (dualMap (algebraMap S S')) ≫ z.left)
      (hh : IsLieComb cf v z) : IsLieComb (fun i => algebraMap S S' (cf i)) u z' := by
    rw [comb_iff] at hh ⊢
    let U : Over.mk ((epsR S').hom ≫ spMap (algebraMap S S')) ⟶ epsR S :=
      Over.homMk (spMap (dualMap (algebraMap S S'))) dual_over
    have e₁ := map_list_prod (pushHom hφ (epsR S')) (List.ofFn fun i => sc (algebraMap S S' (cf i)) ≫ u i)
    have e₂ := map_list_prod (preHom (G := A) U) (List.ofFn fun i => sc (cf i) ≫ v i)
    rw [List.map_ofFn] at e₁ e₂
    have e₃ : (pushHom hφ (epsR S')) ∘ (fun i => sc (algebraMap S S' (cf i)) ≫ u i) =
        (preHom (G := A) U) ∘ fun i => sc (cf i) ≫ v i :=
      funext fun i => Over.OverMorphism.ext (by
        show (spMap (epsScaleR (algebraMap S S' (cf i))) ≫ (u i).left) ≫ φ =
          spMap (dualMap (algebraMap S S')) ≫ spMap (epsScaleR (cf i)) ≫ (v i).left
        rw [Category.assoc, hu, ← Category.assoc, ← Category.assoc, dual_scale])
    rw [e₃, ← e₂, ← hh] at e₁
    apply Over.OverMorphism.ext
    apply hφ.1.hom_ext
    · exact hz.trans (congrArg (·.left) e₁).symm
    · rw [Over.w, Over.w]
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1]
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, combBase (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp

end GlobalTheory.FlagTan
