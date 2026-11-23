module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCmpOfIsPullDeg
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PreUniformisationComparisonTorusInvariantStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreAbelianPartIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsComparisonCompAlongIdentity

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.Cmp

theorem Oφ_baseChange {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {x' : D'.X} {x : D.X}
    (hc : (D'.c x').left ≫ β = spMap φ ≫ (D.c x).left)
    {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of V))}
    (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left) (hp : p'.left ≫ β = h ≫ p.left) (κ : Fin 4) :
    D'.Oφ p' x' κ ≫ β = h ≫ D.Oφ p x κ := by
  have hb : h ≫ T.hom = T'.hom ≫ spMap φ := by
    rw [← Over.w p, ← Category.assoc, ← hp, Category.assoc, pb.1.w, ← Category.assoc, Over.w]
  let U : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h hb
  have e : pushPt pb.1.w p' = U ≫ p := Over.OverMorphism.ext hp
  have c : pushPt pb.1.w (toUnit T' ≫ D'.c x') = toUnit _ ≫ D.c x := Over.OverMorphism.ext (by
    show (T'.hom ≫ (D'.c x').left) ≫ β = (T'.hom ≫ spMap φ) ≫ (D.c x).left
    rw [Category.assoc, hc, ← Category.assoc])
  refine Eq.trans ?_ (WeightPf.Oφ_comp U p x κ).symm
  rw [← e]
  fin_cases κ
  · exact congrArg (fun q => q.left) ((map_mul (pushHom pb T') p' (toUnit T' ≫ D'.c x')).trans
      (congrArg (pushPt pb.1.w p' * ·) c))
  · exact congrArg (fun q => q.left) c
  · rfl
  · exact congrArg (fun q => q.left) (map_one (pushHom pb T'))

theorem exists_comp_id : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D₁ D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A₁ A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U₁ : PreU I' D₁ A₁ G') (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C₁ : Cmp φ U U₁ F) (C₂ : Cmp (RingHom.id V) U₁ U' (𝟙 G'.left)) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F C₁.pb.1.w wL → (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (j : U.P.L.L.ι) (i : U₁.P.L.L.ι) (k : U'.P.L.L.ι), F (r z) ∈ U.P.L.L.U j → r z ∈ U₁.P.L.L.U i → r z ∈ U'.P.L.L.U k → gw wL r z j k = gw C₁.wL r z j i * gw C₂.wL r z i k) → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro R V _ _ _ _ I I' φ D D₁ D' A A₁ A' G _ _ G' _ _ U U₁ U' F C₁ C₂ wL hmap hw
  have g₁ := (isGen_iff _).1 C₁.v_gen
  have g₂ := (isGen_iff _).1 C₂.v_gen
  obtain ⟨v, T⟩ := exists_comp D₁.P.isLB C₁.v C₂.v g₁ g₂ D.P.isLB D'.P.isLB
  have pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) (C₂.β ≫ C₁.β) := by
    have h := C₂.pbB.comp C₁.pbB
    rwa [spMap_ringHom_id, Category.id_comp] at h
  refine ⟨{
    pb := C₁.pb
    wL := wL
    wL_map := hmap
    β := C₂.β ≫ C₁.β
    pbB := pbB
    v := v
    v_gen := (isGen_iff _).2 (T.pgen_comp D₁.P.isLB g₁ g₂)
    xe := C₂.xe.trans C₁.xe
    c_pr := fun x => by
      rw [← Category.assoc, C₂.c_pr, spMap_ringHom_id, Category.id_comp, C₁.c_pr]
      rfl
    lev := fun e Z x' x hx => ?_
    map_le := C₁.map_le }, rfl⟩
  obtain ⟨a₁, b₁⟩ := C₁.lev e Z x' x hx
  obtain ⟨a₂, b₂⟩ := C₂.lev e Z x' x' (by rw [Category.comp_id])
  refine ⟨by rw [← a₁, reassoc_of% a₂], fun z J J' hJ hJ' => ?_⟩
  obtain ⟨J₁, hJ₁⟩ := exists_good_pt D₁.P.isLB z
  obtain ⟨c₁, d₁⟩ := b₁ z J J₁ hJ hJ₁
  obtain ⟨c₂, d₂⟩ := b₂ z J₁ J' hJ₁ hJ'
  have tri : ∀ f : Z ⟶ D'.P.A.left, gw v f z (J (f ≫ C₂.β ≫ C₁.β)) (J' f) =
      gw C₁.v (f ≫ C₂.β) z (J (f ≫ C₂.β ≫ C₁.β)) (J₁ (f ≫ C₂.β)) * gw C₂.v f z (J₁ (f ≫ C₂.β)) (J' f) :=
    fun f => T Z f z _ _ _ (hJ (f ≫ C₂.β ≫ C₁.β)) (hJ₁ (f ≫ C₂.β)) (hJ' f)
  refine ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩
  · have hp : (U'.gt e).pG.left ≫ C₂.β = 𝟙 _ ≫ (U₁.gt e).pG.left := by
      have := (C₂.lev e _ (𝟙 _) (𝟙 _) (by rw [Category.comp_id])).1
      rwa [Category.id_comp] at this
    have o : ∀ κ, D'.Oφ (U'.gt e).pG χ κ ≫ C₂.β = D₁.Oφ (U₁.gt e).pG (C₂.xe χ) κ := fun κ =>
      (Oφ_baseChange C₂.pbB (C₂.c_pr χ) _ _ _ hp κ).trans (Category.id_comp _)
    refine (c₁ (C₂.xe χ)).trans ?_
    rw [c₂ χ, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun κ _ => ?_)
    have t := tri (x' ≫ D'.Oφ (U'.gt e).pG χ κ)
    simp only [Category.assoc] at t
    rw [t, mul_zpow, mul_comm, ← o κ]
    simp only [Category.assoc]
  · obtain ⟨i, hi⟩ := exists_chart U₁.P.L.isLB ((fstG I' e G').left (x' z))
    have t := tri (x' ≫ (U'.gt e).pG.left)
    simp only [Category.assoc] at t
    have a : x' ≫ (U'.gt e).pG.left ≫ C₂.β ≫ C₁.β = x ≫ (U.gt e).pG.left := by rw [← a₁, reassoc_of% a₂]
    rw [a, a₂] at t
    have hk₂ : F ((x' ≫ (fstG I' e G').left) z) ∈ U.P.L.L.U k := by
      have : F ((x' ≫ (fstG I' e G').left) z) = (fstG I e G).left (x z) :=
        (congrArg (fun q : Z ⟶ G.left => q z) hx).symm
      rw [this]; exact hk
    rw [t, hw Z (x' ≫ (fstG I' e G').left) z k i k' hk₂ hi hk', _root_.mul_assoc, d₂ i k' hi hk',
      ← _root_.mul_assoc, d₁ k i hk hi, _root_.mul_assoc]

end GlobalTheory.LN.Cmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsComparisonCompAlongIdentityStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_comparison_comp_along_identity : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D₁ D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A₁ A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U₁ : PreU I' D₁ A₁ G') (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C₁ : Cmp φ U U₁ F) (C₂ : Cmp (RingHom.id V) U₁ U' (𝟙 G'.left)) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F C₁.pb.1.w wL → (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (j : U.P.L.L.ι) (i : U₁.P.L.L.ι) (k : U'.P.L.L.ι), F (r z) ∈ U.P.L.L.U j → r z ∈ U₁.P.L.L.U i → r z ∈ U'.P.L.L.U k → gw wL r z j k = gw C₁.wL r z j i * gw C₂.wL r z i k) → ∃ C : Cmp φ U U' F, C.wL = wL := by
  first | exact @GlobalTheory.LN.Cmp.exists_comp_id | exact GlobalTheory.LN.Cmp.exists_comp_id | (intros; apply GlobalTheory.LN.Cmp.exists_comp_id <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomOfPG

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreUnique

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R}
  {A A' : PolAV (Sp (FractionRing R))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_beta [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤) {e : ℕ} (g : GtCoord I D e G)
    (g' : GtCoord I D' e G) :
    ∃ β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A, IsMonHom β.hom ∧ g'.q ≫ β.hom = g.q := by
  have := g.q_affine
  have := g'.q_affine
  exact flatQuotient_iso_of_same_kernel _ _ _ _ _ _ g.q g.i g'.q g'.i g.q_hom g.i_hom g.q_flat g.q_surj
    inferInstance g.isKernel g'.q_hom g'.i_hom g'.q_flat g'.q_surj inferInstance g'.isKernel
    (gtCoord_i_comp_q hI _ _) (gtCoord_i_comp_q hI _ _)

variable (U : PreU I D A G) (U' : PreU I D' A' G)


open CharAgree in
theorem match_down {e : ℕ} {f : D'.X → D.X}
    (h : CharAgree.Match (U.gt (e + 1)) (U'.gt (e + 1)) f) : CharAgree.Match (U.gt e) (U'.gt e) f := by
  intro Z r z J J' hJ hJ' c c' x
  have t : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : ∀ {Y : Scheme.{0}} (p : (thickObj R I (e + 1) G).left ⟶ Y)
      (p₀ : (thickObj R I e G).left ⟶ Y) (s : G.left ⟶ Y), thickMap R I e G ≫ p = p₀ →
      r ≫ p₀ = r ≫ (fstG I e G).left ≫ s →
      (r ≫ thickMap R I e G) ≫ p = (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left ≫ s := by
    intro Y p p₀ s h₁ h₂
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h₁).trans (h₂.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ s) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G) z J J' hJ hJ' (up _ _ _ (U.gt_q e) c)
    (up _ _ _ (U'.gt_q e) c') x
  exact (val_corr hJ (U.gt_t e (f x)) r).symm.trans ((val_pull hJ _ _ _).trans (k.trans
    ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' (U'.gt_t e x) r))))


open CharAgree in
theorem exists_xe [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤) :
    ∃ xe : D'.X ≃+ D.X, ∀ e, CharAgree.Match (U.gt e) (U'.gt e) xe := by
  choose xe hxe using fun e => exists_match hI (U.gt e) (U'.gt e)
  have down : ∀ (e : ℕ) (f : D'.X → D.X), CharAgree.Match (U.gt e) (U'.gt e) f →
      CharAgree.Match (U.gt 0) (U'.gt 0) f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun h => ih (PreUnique.match_down U U' h)
  refine ⟨xe 0, fun e => ?_⟩
  have h := hxe e
  rw [match_unique hI _ _ (down e _ h) (hxe 0)] at h
  exact h

theorem trans_comp_q (e : ℕ) :
    thickMap R I e G ≫ (U.gt (e + 1)).q.left = (U.gt e).q.left ≫ thickMap R I e D.P.A := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((U.gt_q e).trans
      ((congrArg ((U.gt e).q.left ≫ ·) (UnifCompare.trans_comp_proj e D.P.A).symm).trans
        (Category.assoc _ _ _).symm))
  · have h₁ : (U.gt (e + 1)).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt (e + 1)).q
    have h₀ : (U.gt e).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt e).q
    have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg (thickMap R I e G ≫ ·) h₁).trans ((k G).trans
      ((congrArg (· ≫ thickTrans R I e) h₀.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg ((U.gt e).q.left ≫ ·) (k _).symm).trans (Category.assoc _ _ _).symm)))))

theorem gw_trans (e : ℕ) (y : (thickObj R I e G).left) (jM : D.P.L.ι) (jL : U.P.L.L.ι)
    (hM : (U.gt e).pG.left y ∈ D.P.L.U jM) (hL : (fstG I e G).left y ∈ U.P.L.L.U jL) :
    gw (U.w (e + 1)) (thickMap R I e G) y jM (fun _ => jL) = gw (U.w e) (𝟙 _) y jM (fun _ => jL) := by
  have := U.w_compat e _ (𝟙 _) y jM jL hM hL
  rwa [Category.id_comp] at this

variable (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}

theorem exists_level [IsLocalRing R] (hwL : IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL) (e : ℕ)
    (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A) (hq : (U'.gt e).q ≫ β.hom = (U.gt e).q) :
    ∃ v : LB.Iso (D'.P.L.pull (fstG I e D'.P.A).left) (D.P.L.pull (β.hom.left ≫ (fstG I e D.P.A).left)), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι)
      (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL' := by
  obtain ⟨u, hu, hu'⟩ := LevelComparison.exists_comparison D.P.isLB D'.P.isLB U.P.L.isLB U'.P.L.isLB
    (U.w_gen e) (U'.w_gen e) hwL.gen
  have inv := GlobalTheory.T.preUniformisation_comparison_torus_invariant R I D D' A A' G U U' wL hw hwL e β hq u hu hu'
  haveI := (U'.gt e).q_flat
  haveI := (U'.gt e).q_surj
  haveI := (U'.gt e).q_affine
  haveI := (U.gt e).q_hom
  have hql : (U'.gt e).q.left ≫ β.hom.left = (U.gt e).q.left := congrArg (·.left) hq
  obtain ⟨v, hv, hv'⟩ := LevelComparison.exists_iso_descend (U'.gt e).q.left (fstG I e D'.P.A).left
    (β.hom.left ≫ (fstG I e D.P.A).left) (p := (U.gt e).pG.left) (p' := (U'.gt e).pG.left)
    (by rw [← Category.assoc, hql]; rfl) rfl u hu (fun Z g₁ g₂ z j j' h a b => by
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U'.gt e).q, reassoc_of% h])
      have e₁ : k₁ ≫ (U'.gt e).q = k₂ ≫ (U'.gt e).q := Over.OverMorphism.ext h
      have e' : k₁ ≫ (U.gt e).q = k₂ ≫ (U.gt e).q := by rw [← hq, reassoc_of% e₁]
      have w : (k₁ * k₂⁻¹) ≫ (U.gt e).q = toUnit Z' ≫ η[thickObj R I e D.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
        rfl
      have ht : ((U.gt e).isKernel.lift _ _ w ≫ (U.gt e).i) * k₂ = k₁ := by
        rw [(U.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := inv Z' ((U.gt e).isKernel.lift _ _ w) k₂ z j j' a b
      rw [ht] at this
      exact this)
  refine ⟨v, hv, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  rw [← hu' Z r z jM jM' jL jL' a₁ a₂ a₃ a₄]
  exact congrArg (· * _) (hv' Z r z jM jM' a₁ a₂)


open UnifCompare hiding trans_comp_q gw_trans in
theorem exists_iso [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete I R] (hI : I ≠ ⊤) (hS : SecBaseChangeSt)
    (hA : AmpleSt) (hwL : IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL) :
    ∃ (Φ : D'.P.A ≅ D.P.A) (w : LB.Iso D'.P.L (D.P.L.pull Φ.hom.left)), w.IsGen ∧ ∀ e : ℕ,
      (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι)
      (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' →
      gw w (r ≫ (U'.gt e).pG.left) z jM jM' * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL' := by
  choose β hβm hβ using fun e => exists_beta hI (U.gt e) (U'.gt e)
  choose v hvg hv using fun e => exists_level U U' wL hwL e (β e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG I e D.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG I e D.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R I e D'.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R I e D.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q, Category.assoc, hβl,
      trans_comp_q, ← Category.assoc, hβl]
  obtain ⟨Φ, w, hw, H⟩ := exists_iso_of_compatible_thickenings hS hA R I D.P D'.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.P.A).left,
        y ∈ (D.P.L.pull ((β e).hom.left ≫ (fstG I e D.P.A).left)).U (fun _ => j) ⊓
          (D'.P.L.pull (fstG I e D'.P.A).left).U (fun _ => j') →
        thickMap R I e D'.P.A y ∈
          (D.P.L.pull ((β (e + 1)).hom.left ≫ (fstG I (e + 1) D.P.A).left)).U (fun _ => j) ⊓
          (D'.P.L.pull (fstG I (e + 1) D'.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.P.A ≫ (β (e + 1)).hom.left ≫ (fstG I (e + 1) D.P.A).left =
          (β e).hom.left ≫ (fstG I e D.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.P.L.pull ((β e).hom.left ≫ (fstG I e D.P.A).left)).U (fun _ => j) ⊓
          (D'.P.L.pull (fstG I e D'.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.P.L.isLB ((fstG I e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.P.L.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.P.L.U j :=
      (congrArg (fun g => g x ∈ D.P.L.U j) (hp e)).mp (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.P.L.U j' := mem_pull.1 hx.2
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.P.L.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.P.L.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', gw_trans U e x j jL hM hL, trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  refine ⟨Φ, w, hw, fun e => ⟨?_, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  · exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  · have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
      ((congrArg (fun g => g (r z) ∈ D.P.L.U jM) (hp e)).mpr hM) hM'
    rw [Category.assoc] at h
    exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

theorem isMonHom_of_pG [IsNoetherianRing R] [IsAdicComplete I R] (Φ : D'.P.A ≅ D.P.A)
    (H : ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) : IsMonHom Φ.hom := by
  refine AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D.P.isAb D'.P.isAb Φ.hom fun e => ?_
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U'.gt e).q_flat
  have := (U'.gt e).q_surj
  refine AbelianPartIso.isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
  refine pullback.hom_ext ?_ ?_
  · have k : ((Over.pullback (thick R I e)).map Φ.hom).left ≫
        pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D'.P.A.hom (thick R I e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
      ((Category.assoc _ _ _).symm.trans (H e)))
  · exact (Over.w _).trans (Over.w (U.gt e).q).symm


open CoordCompare in
theorem c_and_coord [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete I R] (hG : GlobalFnsSt)
    (Φ : D'.P.A ≅ D.P.A) (w : LB.Iso D'.P.L (D.P.L.pull Φ.hom.left)) (hw : w.IsGen) [IsMonHom Φ.hom]
    (hp : ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) (xe : D'.X ≃+ D.X)
    (hker : ∀ e, CharAgree.Match (U.gt e) (U'.gt e) xe) :
    (∀ x, D'.c x ≫ Φ.hom = D.c (xe x)) ∧ ∀ (e : ℕ) (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left)
      (z : Z) (J) (J'), Good D.P.L z J → Good D'.P.L z J' → val ((U.gt e).t (xe x)) r z J =
        wVal (U'.gt e) Φ.hom x w r z J J' * val ((U'.gt e).t x) r z J' := by
  have hw' := (isGen_iff w).1 hw
  have hp' : ∀ e, (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hp e)
  have desc := fun e x => exists_desc_gen (U.gt e) (U'.gt e) Φ.hom (hp' e) (xe x) x w hw'
    (fun Z r z J J' hJ hJ' h h' => hker e Z r z J J' hJ hJ' h h' x)
  have hc : ∀ x, D'.c x ≫ Φ.hom = D.c (xe x) := fun x => by
    have := D.P.isAb.smooth
    have := D.P.isAb.geomConnected
    have := D.P.isAb.proper
    have h := (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I)
      D.P.A).2 D.P.A (toUnit _ ≫ D'.c x ≫ Φ.hom) (toUnit _ ≫ D.c (xe x)) fun n => by
        obtain ⟨v, hv, -⟩ := desc n x
        have h₁ := thick_eq _ _ v hv
        have h₂ : (fstG I n D.P.A).left ≫ (toUnit D.P.A).left =
            pullback.snd D.P.A.hom (thick R I n) ≫ thick R I n := pullback.condition
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
    simpa using congrArg (η[D.P.A] ≫ ·) h
  refine ⟨hc, fun e x Z r z J J' hJ hJ' => ?_⟩
  obtain ⟨v, hv, hv'⟩ := desc e x
  have h₁ := val_eq_one hG _ _ (hc x) v hv (fun y J hJ => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB y
    have := (U.gt e).q_hom
    have h := hv' _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left
      y J J' hJ hJ'
    rwa [← Over.comp_left, MonObj.one_comp, wVal_one, TorusCoord.val_unit _ _ hJ,
      TorusCoord.val_unit _ _ hJ', inv_one, _root_.mul_one, _root_.mul_one] at h) _ (r ≫ (U.gt e).q.left) z J hJ
  have h₂ := (hv' _ r z J J' hJ hJ').symm.trans h₁
  rw [← _root_.mul_assoc, mul_inv_eq_one] at h₂
  exact h₂.symm

theorem exists_cmp_id : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∃ C : Cmp (RingHom.id R) U U' (𝟙 G.left), C.wL = wL := by
  intro hL R _ _ _ I hR D D' A A' G _ _ U U' wL hw hwL
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  obtain ⟨Φ, w, hg, H⟩ := exists_iso U U' wL hI hL.secBaseChange hL.ample hwL
  have := isMonHom_of_pG U U' Φ fun e => (H e).1
  obtain ⟨xe, hxe⟩ := exists_xe U U' hI
  obtain ⟨hc, ht⟩ := c_and_coord U U' hL.globalFns Φ w hg (fun e => (H e).1) xe hxe
  have hm : ∀ (f : Sp R ⟶ Sp R) (_ : f = 𝟙 _) (h), IsCPMap U'.P U.P f (𝟙 G.left) h wL := by
    rintro _ rfl _
    exact hwL
  refine ⟨⟨Cmp.grpPullback_id G Cmp.spMap_ringHom_id, wL, hm _ Cmp.spMap_ringHom_id _, Φ.hom.left,
    (isGrpPullback_of_iso Φ).congr Cmp.spMap_ringHom_id.symm rfl, w, hg, xe, fun x => ?_, fun e Z x' x hx => ?_,
    (Ideal.map_id _).le⟩, rfl⟩
  · rw [Cmp.spMap_ringHom_id, ← hc]
    exact (Category.id_comp _).symm
  · have := Cmp.mono_fstG I e G
    rw [Category.comp_id, cancel_mono] at hx
    subst hx
    refine ⟨congrArg (x ≫ ·) (H e).1, fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
    · refine (ht e χ Z x z J J' hJ hJ').trans ((mul_comm _ _).trans (congrArg _ ?_))
      simp only [CoordCompare.wVal, Category.assoc]
    · exact (H e).2 Z x z _ _ k k' (hJ (x ≫ (U.gt e).pG.left)) (hJ' (x ≫ (U'.gt e).pG.left)) hk hk'

end GlobalTheory.LN.PreUnique
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompareUniformisationDataPullback

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.PreCompare

theorem exists_cmp : Laws → Laws2 → Ega → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal R) (I' : Ideal V), AdmBase R I → AdmBase V I' → I' ≠ ⊤ → ∀ φ : R →+* V, I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro hL _ _ R V _ _ _ _ _ _ I I' _ hV _ φ hI D D' A A' G _ _ G' _ _ U U' F pb wL hw
  obtain ⟨D₁, U₁, C₁, hP, hC⟩ := PreBaseChange.exists_cmp_pull hL R V I I' φ hI D D' A A' G G' U U' F pb wL hw
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U'
  obtain rfl : U₁.P = P := hP
  obtain rfl : C₁.wL = wL := eq_of_heq hC
  obtain ⟨C₂, h₂⟩ := PreUnique.exists_cmp_id hL V I' hV D₁ D' A' A' G' U₁
    ⟨semi, gen, gen_hom, U₁.P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ (idIso U₁.P.L.L) (by simp)
    (IsCPMap.id U₁.P)
  refine GlobalTheory.T.exists_comparison_comp_along_identity R V I I' φ D D₁ D' A A' A' G G' U U₁ _ F C₁ C₂ C₁.wL hw fun Z r z j i k hj hi hk => ?_
  rw [h₂]
  have a := (isGen_iff _).1 C₁.wL_map.gen Z r z j j i k hj hj hi hk
  rw [gm_self U.P.L.isLB (r ≫ F) z hj, _root_.one_mul] at a
  exact ((congrArg₂ (· * ·) a (gw_idIso U₁.P.L.L r z hi hk)).trans (by rw [mul_comm, mul_inv_cancel_left])).symm

end GlobalTheory.LN.PreCompare
end
end
