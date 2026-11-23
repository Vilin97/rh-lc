module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ClassSubStructure
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChainVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAddFinrankOfKernel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusTorsionToAbelianTorsionThetaActionStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsConj

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.Weight

open GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev CompMod (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Type :=
  SecMod (fst (TF (R := R) F) D.P.A).left (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

theorem gs_scal {K : Type} [CommRing K] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (r : Z ⟶ Y) (z : Z)
    (c : K) : gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

theorem phiRaw_val (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) {s s' : Raw D F k}
    (h : PhiRaw D F k 0 g w s s') (α : D.X) (y : (DegPre.BF D F).left) (J) (hJ : Good D.P.L y J) :
    sval (s' α) (𝟙 _) y J = sval (s α) (DegPre.trPt D F g.b).left y J * (uVal D F k α g.b (𝟙 _) y J *
      val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (fst (TF (R := R) F) D.P.A).left y J).val := by
  obtain ⟨u, hu, hc⟩ := (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).1
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h α u hu hc) _ (𝟙 _) y J hJ
  have e' := hg.val_phi hG w hw α u hu hc _ (𝟙 _) y J hJ
  rw [Category.id_comp, Over.id_left] at e'
  rw [Category.id_comp] at e
  exact (congrArg (fun β => sval (s' β) (𝟙 _) y J) (add_zero α)).symm.trans
    (e.trans (congrArg (fun q => _ * Units.val q) e'))

theorem phiRaw_smul (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen)
    {s s' t t' : ∀ α, CompMod D F k α} (h : PhiRaw D F k 0 g w (fun α => (s α).sec) fun α => (s' α).sec)
    (h' : PhiRaw D F k 0 g w (fun α => (t α).sec) fun α => (t' α).sec) (α : D.X) (c : F) (e : s α = c • t α) :
    s' α = c • t' α := by
  refine SecOps.sec_ext (sec_ext_val D.P.isLB fun y J hJ => ?_)
  have a := phiRaw_val hG hg hw h α y J hJ
  have b := phiRaw_val hG hg hw h' α y J hJ
  have t₁ : (DegPre.trPt D F g.b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left :=
    (congrArg (fun q => q.left) (tr_fst D F g.b)).trans (Category.id_comp _).symm
  change sval (s' α).sec (𝟙 _) y J = sval (c • t' α).sec (𝟙 _) y J
  rw [SecMod.value_smul hJ, a, b, e, SecMod.value_smul hJ, gs_scal, gs_scal, _root_.mul_assoc]
  exact congrArg (fun q => gs q y ⊤ _ * _) t₁

theorem phiRaw_torus (hG : GlobalFnsSt) {k : ℕ} (τ : Multiplicative D.X →* Fˣ) {g : GtPtF D F}
    (hτ : g = torusPt D F (Additive.ofMul τ)) (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ s s' : ∀ α, CompMod D F k α, PhiRaw D F k 0 g w (fun α => (s α).sec) (fun α => (s' α).sec) →
      ∀ α, s' α = ((c * τ (Multiplicative.ofAdd α) : Fˣ) : F) • s α := by
  have hb : g.b = 1 := hτ ▸ torusPt_b _
  obtain ⟨y₀, J₀, hJ₀⟩ := exists_good_chart D F
  obtain ⟨c, hc⟩ := (stalkUnits (F := F) y₀).surjective (val w (𝟙 _) y₀ J₀)
  have vv : ∀ (u : Fˣ) {Z : Scheme.{0}} (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val (GlobalTheory.UU.scaleGen (unitOn u) (LB.oneGen D.P.L (Y := (TF (R := R) F).left))) r z J = gm r z ⊤ (unitOn u) :=
    fun u Z r z J hJ => (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))
  have hwv : ∀ y J, Good D.P.L y J → val w (𝟙 _) y J = stalkUnits (F := F) y c := fun y J hJ => by
    obtain rfl := pt_eq y₀ y
    refine (val_eq_of_val_eq (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_) hw
      (GlobalTheory.UU.scaleGen_isGen (unitOn c) oneGen_isGen) hJ₀ hJ (hc.symm.trans ((vv c _ _ _ hJ₀).trans (gm_unitOn _ c)).symm)).trans
      ((vv c _ _ _ hJ).trans (gm_unitOn _ c))
    rw [Fin.prod_univ_two, Fintype.prod_empty]
    show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ)) = 1
    rw [hb, zpow_neg, mul_inv_cancel]
  refine ⟨c, fun s s' h α => SecOps.sec_ext (sec_ext_val D.P.isLB fun y J hJ => ?_)⟩
  have cr : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s α) w)
      (GlobalTheory.UU.scaleGen (unitOn (c * τ (Multiplicative.ofAdd α))) (LB.oneGen D.P.L (Y := (TF (R := R) F).left))) :=
    corr_of_val D.P.isLB fun y J hJ => by
      have e : charVal g α y J = stalkUnits (F := F) y (τ (Multiplicative.ofAdd α)) := hτ ▸ torusPt_val τ α hJ
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e (hwv y J hJ))).trans
        (Eq.trans ?_ ((vv _ _ _ _ hJ).trans (gm_unitOn _ _)).symm)
      exact (mul_comm _ _).trans (map_mul (stalkUnits (F := F) y) _ _).symm
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have u₁ : uVal D F k α g.b (𝟙 _) y J = 1 := by
    rw [uVal_id, hb, MonObj.comp_one, C.face₃, inv_one, _root_.mul_one]
    exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  have t₁ : DegPre.trPt D F g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [tr_fst, Category.id_comp]
    · rw [tr_pr, hb, MonObj.comp_one, _root_.mul_one, Category.id_comp]
  have a := phiRaw_val hG hg hw h α y J hJ
  rw [u₁, _root_.one_mul, t₁, Over.id_left, (val_corr hJ cr _).trans (vv _ _ _ _ hJ)] at a
  change sval (s' α).sec (𝟙 _) y J = sval (((c * τ (Multiplicative.ofAdd α) : Fˣ) : F) • s α).sec (𝟙 _) y J
  rw [SecMod.value_smul hJ, gs_scal, Category.id_comp, mul_comm]
  exact a.trans (congrArg _ (gs_unit _ y ⊤ trivial _).symm)

theorem exists_conj {K K' E M : Type} [CommRing K] [CommRing K'] [AddCommGroup E] [Module K E] [AddCommGroup M]
    [Module K' M] (σ : K ≃+* K') (j : E ≃+ M) (hj : ∀ (c : K) v, j (c • v) = σ c • j v) (Φ : M ≃ₗ[K'] M) :
    ∃ Ψ : E ≃ₗ[K] E, ∀ v, j (Ψ v) = Φ (j v) :=
  ⟨{ j.trans (Φ.toAddEquiv.trans j.symm) with
      map_smul' := fun c v => j.injective (by
        show j (j.symm (Φ (j (c • v)))) = j (c • j.symm (Φ (j v)))
        rw [hj, hj, map_smul, j.apply_symm_apply, j.apply_symm_apply]) }, fun _ => j.apply_symm_apply _⟩

abbrev TorsPt {S : Scheme.{0}} (P : PolAV S) (T : Over S) (N : ℕ) : Subgroup (T ⟶ P.A) :=
  (powMonoidHom N : (T ⟶ P.A) →* (T ⟶ P.A)).ker

theorem exists_projective_rep (hL : Laws) (hL₂ : Laws2) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {F : Type} [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ (Φ : TorsPt P (Over.mk p) N → (SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p)) ≃ₗ[F]
        SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p))))
      (e : TorsPt P (Over.mk p) N → TorsPt P (Over.mk p) N → Fˣ),
      Module.finrank F (SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p))) = N ^ P.g ∧
      (∀ a, ∃ θ : ThetaGrp P.A P.L N (Over.mk p), θ.pt = a.1 ∧ ∀ v, IsActOf P.A P.L N θ v.sec (Φ a v).sec) ∧
      (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) ∧
      (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a = 1 := by
  obtain ⟨Φ, e, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL₂ S P F p N hN
  let σ : F ≃+* Γ((Over.mk p).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p)) ≃+ SecM P.A P.L N (Over.mk p) :=
    { toFun := fun v => SecM.ofSec P.A v.sec
      invFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (c • v) = σ c • j v := fun _ _ => rfl
  let u : Γ((Over.mk p).left, ⊤)ˣ ≃* Fˣ := Units.mapEquiv σ.symm.toMulEquiv
  have hu : ∀ r, σ (u r : F) = r.val := fun r => σ.apply_symm_apply _
  have hd := (congrArg Cardinal.toNat (rank_eq_of_equiv_equiv σ j σ.bijective hj)).trans h₁
  choose Ψ hΨ using fun a : TorsPt P (Over.mk p) N => exists_conj σ j hj (Φ a)
  refine ⟨Ψ, fun a b => u (e a b), hd, fun a => ?_, fun a b => ?_, fun a b v => ?_,
    fun a h => Subtype.ext (h₅ a fun b => u.injective ((h b).trans (map_one u).symm))⟩
  · obtain ⟨θ, h, h'⟩ := h₂ a
    refine ⟨θ, h, fun v => ?_⟩
    have := h' (j v)
    rw [← hΨ] at this
    exact this
  · obtain ⟨r, hr⟩ := h₃ a b (a * b : TorsPt P (Over.mk p) N) rfl
    refine ⟨u r, fun v => j.injective ?_⟩
    rw [hj, hΨ, hΨ, hΨ, hu]
    exact hr (j v)
  · apply j.injective
    beta_reduce
    rw [hj, hΨ, hΨ, hΨ, hΨ]
    exact ((h₄ a b).2 (j v)).trans (congrArg (fun c => c • Φ b (Φ a (j v))) (hu (e a b)).symm)

end GlobalTheory.UU.Weight
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpaces

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.Weight

open GlobalTheory.TorusExt GlobalTheory.ClassWeight

abbrev SecA {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  SecMod (F := F) (fst (TFK (R := R) F) A.A).left (LPow A.A A.L (k : ℤ) (TFK (R := R) F))

theorem exists_expansion (hL : Laws) (hL₂ : Laws2) : AllPre fun {V} _ _ _ {D} {A} {_} _ _ U =>
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
      ∃ S : ∀ α, SecA A F k →ₗ[F] CompMod D F k α,
        (∀ (v : SecA A F k) (s : Raw D F k), U.ExpF F k v.sec s ↔ s = fun α => (S α v).sec) ∧
        ∀ v, (∀ α, S α v = 0) → v = 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k hk
  choose x hx using GlobalTheory.T.exists_fourierJacobi_expansion_over_field hL hL₂ V hV D A G U F k hk
  have uq := GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k
  have lin := ExpLin.expF_linear V hV D A G U F k
  let S₀ : ∀ α, SecA A F k → CompMod D F k α := fun α v => SecMod.mk _ (x v.sec α)
  have comb : ∀ (c : F) (v v' : SecA A F k) α, S₀ α (c • v + v') = c • S₀ α v + S₀ α v' := fun c v v' =>
    congrFun ((uq _ _ _ _ (hx (c • v + v').sec) (lin v.sec v'.sec (c • v + v').sec _ _
      (fun α => (c • S₀ α v + S₀ α v').sec) c (hx v.sec) (hx v'.sec) (fun _ => rfl) fun _ _ => rfl)).1 rfl)
  have z : ∀ α, S₀ α 0 = 0 := fun α => by
    have := comb 1 0 0 α
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨fun α =>
    { toFun := S₀ α
      map_add' := fun v v' => by simpa only [one_smul] using comb 1 v v' α
      map_smul' := fun c v => by simpa only [add_zero, z, RingHom.id_apply] using comb c v 0 α },
    fun v s => ⟨fun h => (uq _ _ _ _ h (hx v.sec)).1 rfl, fun h => h ▸ hx v.sec⟩, fun v h => ?_⟩
  exact (uq _ _ _ _ (hx v.sec) (hx (0 : SecA A F k).sec)).2 (funext fun α => (h α).trans (z α).symm)

theorem exists_rep (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ (Φ : TorsPt A (TFK (R := R) F) N → (SecA A F N ≃ₗ[F] SecA A F N))
      (e : TorsPt A (TFK (R := R) F) N → TorsPt A (TFK (R := R) F) N → Fˣ),
      Module.finrank F (SecA A F N) = N ^ A.g ∧ Nat.card (TorsPt A (TFK (R := R) F) N) = N ^ (2 * A.g) ∧
      (∀ a, ∃ θ : ThetaGrp A.A A.L N (TFK (R := R) F), θ.pt = a.1 ∧ ∀ v, IsActOf A.A A.L N θ v.sec (Φ a v).sec) ∧
      (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) ∧
      (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a = 1 := by
  obtain ⟨Φ, e, hd, h⟩ := exists_projective_rep hL hL₂ A (jFK (R := R) F) hN
  exact ⟨Φ, e, hd, (hL.mulN _ A N (Nat.pos_of_ne_zero fun e => hN (by rw [e, Nat.cast_zero]))).2.2.2.2 F
    (jFK (R := R) F) hN, h⟩

attribute [local instance] gtGroup

theorem exists_range {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (N : ℕ) {A : Type} [CommGroup A] (m : {g : GtPtF D F // GtTors D N g} → A)
    (minj : Function.Injective m) (madd : ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') :
    ∃ (H : Subgroup A) (a : TorChar D.X F N →* A), (∀ h, h ∈ H ↔ ∃ g, m g = h) ∧
      Nat.card H = Nat.card {g : GtPtF D F // GtTors D N g} ∧ Function.Injective a ∧
      ∀ τ, ∃ g, a τ = m g ∧ g.1 = torusPt D F (Additive.ofMul τ.1) := by
  let K := (nsmulAddMonoidHom N : GtPtF D F →+ GtPtF D F).ker
  let κ : K ≃ {g : GtPtF D F // GtTors D N g} := Equiv.subtypeEquivRight fun g => (GtCount.gtTors_iff N g).symm
  let ν : Multiplicative K →* A :=
    MonoidHom.mk' (fun g => m (κ g.toAdd)) fun g g' => madd _ _ _ ((isAdd_iff_eq _ _ _).2 rfl)
  have hν : Function.Injective ν := fun g g' h => κ.injective (minj h)
  let i : TorChar D.X F N →* Multiplicative K := MonoidHom.mk' (fun τ => Multiplicative.ofAdd
    ⟨torusPt D F (Additive.ofMul τ.1), show N • torusPt D F (Additive.ofMul τ.1) = 0 by
      rw [← map_nsmul, ← ofMul_pow, show τ.1 ^ N = 1 from τ.2, ofMul_one, map_zero]⟩)
    fun τ τ' => Subtype.ext (map_add (torusPt D F) (Additive.ofMul τ.1) (Additive.ofMul τ'.1))
  have iinj : Function.Injective i := fun τ τ' h =>
    Subtype.ext (Additive.ofMul.injective (torusPt_injective (congrArg Subtype.val h)))
  exact ⟨ν.range, ν.comp i, fun h => ⟨fun ⟨g, e⟩ => ⟨_, e⟩, fun ⟨g, e⟩ =>
      ⟨Multiplicative.ofAdd (κ.symm g), (congrArg m (κ.apply_symm_apply g)).trans e⟩⟩,
    (Nat.card_congr (MonoidHom.ofInjective hν).toEquiv).symm.trans (Nat.card_congr κ), hν.comp iinj,
    fun τ => ⟨κ (i τ).toAdd, rfl, rfl⟩⟩

theorem structure_of_acts (hL : Laws) (hL₂ : Laws2) {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] {I : Ideal V}
    {D : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    [IsCommMonObj G] (U : PreU I D A G) (hg : A.g = D.P.g + D.rank) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing V) F] {N : ℕ} (hN : (N : F) ≠ 0) (S : ∀ α, SecA A F N →ₗ[F] CompMod D F N α)
    (hS : ∀ (v : SecA A F N) (s : Raw D F N), U.ExpF F N v.sec s ↔ s = fun α => (S α v).sec)
    (hS₀ : ∀ v, (∀ α, S α v = 0) → v = 0)
    (m : {g : GtPtF D F // GtTors D N g} → (TFK (R := V) F ⟶ A.A)) (minj : Function.Injective m)
    (mact : ∀ g, U.Acts F N 0 g.1 (m g)) (madd : ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') :
    ∃ Ψ : {g : GtPtF D F // GtTors D N g} → (SecA A F N ≃ₗ[F] SecA A F N), FiniteDimensional F (SecA A F N) ∧
      (∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
        ∀ v : SecA A F N, PhiRaw D F N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Ψ g v)).sec) ∧
      ∀ α, (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
        Module.finrank F (classSub S N α) = N ^ D.P.g ∧
        ∀ W : Submodule F (SecA A F N), W ≤ classSub S N α → (∀ g, ∀ v ∈ W, Ψ g v ∈ W) →
          W = ⊥ ∨ W = classSub S N α := by
  have hN0 : N ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hN1 : 0 < N := Nat.pos_of_ne_zero hN0
  obtain ⟨Φ, e, hd, cA, hθ, hm, hc, hn⟩ := exists_rep hL hL₂ A F hN
  have : Finite (TorsPt A (TFK (R := V) F) N) :=
    Nat.finite_of_card_ne_zero (cA.trans_ne (pow_ne_zero _ hN0))
  have fd : FiniteDimensional F (SecA A F N) :=
    Module.finite_of_finrank_pos ((pow_pos hN1 _).trans_eq hd.symm)
  obtain ⟨m', hm'⟩ : ∃ m' : {g : GtPtF D F // GtTors D N g} → TorsPt A (TFK (R := V) F) N,
    ∀ g, (m' g).1 = m g := ⟨fun g => ⟨m g, (mact g).1⟩, fun _ => rfl⟩
  have hΨ : ∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
      ∀ v : SecA A F N, PhiRaw D F N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Φ (m' g) v)).sec := fun g => by
    obtain ⟨θ, h₁, h₂⟩ := hθ (m' g)
    obtain ⟨w, hw, h⟩ := (mact g).2 θ (h₁.trans (hm' g))
    exact ⟨w, hw, fun v => h _ _ _ _ ((hS v _).2 rfl) ((hS _ _).2 rfl) (h₂ v)⟩
  obtain ⟨H, a, hH, cH, ainj, ha⟩ := exists_range D F N m'
    (fun g g' h => minj ((hm' g).symm.trans ((congrArg Subtype.val h).trans (hm' g'))))
    fun g g' g'' h => Subtype.ext ((hm' g'').trans ((madd g g' g'' h).trans
      (congrArg₂ (· * ·) (hm' g) (hm' g')).symm))
  have cT : Nat.card (TorChar D.X F N) = N ^ D.rank := GtCount.card_torus_torsion D.X F N hN
  rw [(GtCount.card_gtTors hL hL₂ V D F N hN).1] at cH
  have k₁ : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v :=
    fun τ => by
      obtain ⟨g, e₁, e₂⟩ := ha τ
      obtain ⟨w, hw, h⟩ := hΨ g
      obtain ⟨c, hc⟩ := phiRaw_torus hL.globalFns τ.1 e₂ g.2 hw
      rw [e₁]
      exact ⟨c, fun v => hc (fun α => S α v) (fun α => S α (Φ (m' g) v)) (h v)⟩
  have k₂ : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v') := by
    intro x hx β v v' c e
    obtain ⟨g, rfl⟩ := (hH x).1 hx
    obtain ⟨w, hw, h⟩ := hΨ g
    exact phiRaw_smul hL.globalFns g.2 hw (s := fun α => S α v) (s' := fun α => S α (Φ (m' g) v))
      (t := fun α => S α v') (t' := fun α => S α (Φ (m' g) v')) (h v) (h v') β c e
  refine ⟨fun g => Φ (m' g), fd, hΨ, fun α => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := classSub_structure hN e Φ (by rw [cA, Nat.cast_pow]; exact pow_ne_zero _ hN)
    (by rw [cA, hd, mul_comm, pow_mul]) hm hc hn S hS₀ a ainj k₁ H k₂ (by rw [cT, cH, cA, hg]; ring) α
  refine ⟨h₁, ?_, fun W hW hst => h₃ W hW fun x hx => ?_⟩
  · refine Nat.eq_of_mul_eq_mul_right (pow_pos hN1 D.rank) ?_
    rw [← cT, h₂, cT, ← pow_add, ← hg, hd]
  · obtain ⟨g, rfl⟩ := (hH x).1 hx
    exact hst g

theorem weight_structure (hL : Laws) (hL₂ : Laws2) : AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N →
    ∃ (S : ∀ α, SecA A (Kbar V) N →ₗ[Kbar V] CompMod D (Kbar V) N α)
      (Ψ : {g : GtPtF D (Kbar V) // GtTors D N g} → (SecA A (Kbar V) N ≃ₗ[Kbar V] SecA A (Kbar V) N)),
      FiniteDimensional (Kbar V) (SecA A (Kbar V) N) ∧
      (∀ (v : SecA A (Kbar V) N) (s : Raw D (Kbar V) N), U.ExpF (Kbar V) N v.sec s ↔ s = fun α => (S α v).sec) ∧
      (∀ v, (∀ α, S α v = 0) → v = 0) ∧
      (∀ g : {g : GtPtF D (Kbar V) // GtTors D N g},
        ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D (Kbar V) g.1.b) (DegPre.lineε N)), w.IsGen ∧
        ∀ v : SecA A (Kbar V) N, PhiRaw D (Kbar V) N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Ψ g v)).sec) ∧
      ∀ α, (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
        Module.finrank (Kbar V) (classSub S N α) = N ^ D.P.g ∧
        ∀ W : Submodule (Kbar V) (SecA A (Kbar V) N), W ≤ classSub S N α → (∀ g, ∀ v ∈ W, Ψ g v ∈ W) →
          W = ⊥ ∨ W = classSub S N α := by
  intro V _ _ _ hV D A G _ _ U N hN1
  have : IsNoetherianRing V := by have := hV.1; infer_instance
  have hN : (N : Kbar V) ≠ 0 := by
    have := hV.2.2
    have : CharZero (FractionRing V) := inferInstance
    exact Nat.cast_ne_zero.2 (by omega)
  obtain ⟨S, hS, hS₀⟩ := exists_expansion hL hL₂ V hV D A G U (Kbar V) N hN1
  obtain ⟨m, minj, mact, madd⟩ := GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action hL hL₂ V hV D A G U N hN1
  obtain ⟨Ψ, fd, h⟩ := structure_of_acts hL hL₂ U (PreU.dim_eq V hV D A G U) (Kbar V) hN S hS hS₀ m minj mact madd
  exact ⟨S, Ψ, fd, hS, hS₀, h⟩

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ (α : D.X) t s, U.ExpF (Kbar V) N t s → ∃ t' s', U.ExpF (Kbar V) N t' s' ∧ ∀ β, (∃ mu, β = α + N • mu) ∧ s' β = s β ∨ (¬ ∃ mu, β = α + N • mu) ∧ ∀ j, (s' β).f j = 0) ∧ (∀ α : D.X, ∃ mu, U.Supp (Kbar V) N (α + N • mu)) ∧ ∀ (α : D.X), U.Supp (Kbar V) N α → ∀ t s, U.ExpF (Kbar V) N t s → (∀ β, (¬ ∃ mu, β = α + N • mu) → ∀ j, (s β).f j = 0) → (∀ j, (s α).f j = 0) → ∀ j, t.f j = 0) := by
  intro hL hL₂ V _ _ _ hV D A G _ _ U N hN
  obtain ⟨S, Ψ, fd, hS, hS₀, hΨ, h⟩ := weight_structure hL hL₂ V hV D A G U N hN
  refine ⟨fun α t s hs => ?_, fun α => ?_, fun α ⟨t₀, s₀, h₀, j₀, hj₀⟩ t s hs hz hα => ?_⟩
  · obtain rfl := (hS (SecMod.mk _ t) s).1 hs
    obtain ⟨v', hv', e⟩ := (h α).1 (SecMod.mk _ t)
    refine ⟨v'.sec, _, (hS v' _).2 rfl, fun β => ?_⟩
    by_cases hβ : ∃ mu, β = α + N • mu
    · refine Or.inl ⟨hβ, ?_⟩
      obtain ⟨mu, rfl⟩ := hβ
      exact e mu
    · exact Or.inr ⟨hβ, (SecMod.eq_zero_iff_coord _).1 (hv' β hβ)⟩
  · have : Nontrivial (classSub S N α) :=
      Module.nontrivial_of_finrank_pos (R := Kbar V) ((pow_pos hN _).trans_eq (h α).2.1.symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : classSub S N α)
    obtain ⟨β, hβ⟩ := not_forall.1 fun e => hv (Subtype.ext (hS₀ v.1 e))
    obtain ⟨mu, rfl⟩ := not_not.1 fun e => hβ (v.2 β e)
    exact ⟨mu, v.1.sec, _, (hS v.1 _).2 rfl, not_forall.1 fun e => hβ ((SecMod.eq_zero_iff_coord _).2 e)⟩
  · obtain rfl := (hS (SecMod.mk _ t) s).1 hs
    obtain rfl := (hS (SecMod.mk _ t₀) s₀).1 h₀
    have st : ∀ g β v, S β v = 0 → S β (Ψ g v) = 0 := fun g β v e => by
      obtain ⟨w, hw, hp⟩ := hΨ g
      exact (phiRaw_smul hL.globalFns g.2 hw (s := fun α => S α v) (s' := fun α => S α (Ψ g v))
        (t := fun α => S α v) (t' := fun α => S α (Ψ g v)) (hp v) (hp v) β 0 (e.trans (zero_smul _ _).symm)).trans (zero_smul _ _)
    rcases (h α).2.2 (classSub S N α ⊓ LinearMap.ker (S α)) inf_le_left
      (fun g v hv => ⟨fun β hβ => st g β v (hv.1 β hβ), st g α v hv.2⟩) with e | e
    · have : SecMod.mk _ t ∈ classSub S N α ⊓ LinearMap.ker (S α) :=
        ⟨fun β hβ => (SecMod.eq_zero_iff_coord _).2 (hz β hβ), (SecMod.eq_zero_iff_coord _).2 hα⟩
      rw [e] at this
      exact (SecMod.eq_zero_iff_coord _).1 ((Submodule.mem_bot _).1 this)
    · obtain ⟨v', hv', e'⟩ := (h α).1 (SecMod.mk _ t₀)
      have e₁ : ∀ β, β = α + N • (0 : D.X) → S β v' = S β (SecMod.mk _ t₀) := fun β hβ => hβ ▸ e' 0
      have e₂ : S α v' = 0 := (e.symm ▸ hv' : v' ∈ classSub S N α ⊓ LinearMap.ker (S α)).2
      exact absurd ((SecMod.eq_zero_iff_coord _).1 ((e₁ α (by rw [nsmul_zero, add_zero])).symm.trans e₂) j₀) hj₀

end GlobalTheory.UU.Weight
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpacesStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ (α : D.X) t s, U.ExpF (Kbar V) N t s → ∃ t' s', U.ExpF (Kbar V) N t' s' ∧ ∀ β, (∃ mu, β = α + N • mu) ∧ s' β = s β ∨ (¬ ∃ mu, β = α + N • mu) ∧ ∀ j, (s' β).f j = 0) ∧ (∀ α : D.X, ∃ mu, U.Supp (Kbar V) N (α + N • mu)) ∧ ∀ (α : D.X), U.Supp (Kbar V) N α → ∀ t s, U.ExpF (Kbar V) N t s → (∀ β, (¬ ∃ mu, β = α + N • mu) → ∀ j, (s β).f j = 0) → (∀ j, (s α).f j = 0) → ∀ j, t.f j = 0) := by
  first | exact @GlobalTheory.UU.Weight.main | exact GlobalTheory.UU.Weight.main | (intros; apply GlobalTheory.UU.Weight.main <;> assumption)
end
end
