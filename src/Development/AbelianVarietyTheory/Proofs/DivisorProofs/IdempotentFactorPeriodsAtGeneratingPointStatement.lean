module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIsoStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodGeneratorOnOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauOnOpen

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens}

theorem tauW_isGen (ψW : PsiOn D W) (a b : D.X) : (ψW.tau a b).IsGen :=
  DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _) (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.rig_gen _))

theorem val_tauW_generic (ψW : PsiOn D W) (a b : D.X) (lam : (TK R).left ⟶ W.toScheme) (h : lam ≫ W.ι = jK R)
    (z : (TK R).left) (J) (hJ : Good D.P.L z J) : val (ψW.tau a b) lam z J = val (D.tau a b) (𝟙 _) z J := by
  have hW : lam ≫ W.ι = 𝟙 _ ≫ jK R := h.trans (Category.id_comp _).symm
  obtain ⟨mu, l₁, l₂⟩ : ∃ mu : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, mu ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      mu ≫ (jK R ∣_ W) = lam :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ hW,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have vψ : ∀ χ, val (ψW.psi χ) lam z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
    have e := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) mu).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at e
    exact e
  have vρ : val (D.rigW W) lam z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact congrArg (fun q => val D.rig q z J) hW
  refine (TauPull.val_tauW ψW lam hJ a b).trans (Eq.trans ?_ (TauPull.val_tau (𝟙 _) hJ a b).symm)
  rw [← vψ, ← vψ, ← vψ, ← vρ]

end GlobalTheory.TauOnOpen

namespace GlobalTheory

theorem exists_tau_onOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  intro R _ _ D W ψW a b
  obtain ⟨t, ht, hv⟩ : ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TW W).left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val (ψW.tau a b) r z J := by
    refine exists_gen D.P.isLB (fun U _ h => ?_) (ψW.tau a b) (TauOnOpen.tauW_isGen ψW a b)
    have e₁ : (toUnit (TW W) ≫ D.c (a + b)).left = ((toUnit (TW W) ≫ D.c a) * (toUnit (TW W) ≫ D.c b)).left := by
      rw [D.c_add]; exact congrArg (fun q : TW W ⟶ D.P.A => q.left) (MonObj.comp_mul (toUnit (TW W)) (D.c a) (D.c b))
    have e₂ : (toUnit (TW W)).left ≫ eSec D.P.A = (1 : TW W ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, e₁, e₂]
    simp [lamPts, negε]
  exact ⟨t, ht, hv, fun lam h z J hJ => (hv _ lam z J hJ).trans (TauOnOpen.val_tauW_generic ψW a b lam h z J hJ)⟩

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodGeneratorOnOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_period_generator_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  first | exact @GlobalTheory.exists_tau_onOpen | exact GlobalTheory.exists_tau_onOpen | (intros; apply GlobalTheory.exists_tau_onOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorProportionalitySpreadsFromGeneric

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenSpread

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} (hF : FormEq φ₁ ε₁ φ₂ ε₂)
    {t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)} {t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val t₁ r z J * (val t₂ r z J)⁻¹).val = gs r z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 (hF U h))
    (LB.mulGen L _ _ _ _ t₁ (LB.invGen L _ _ t₂)) (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ (DVR.invGen_isGen _ _ _ _ h₂))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

def fnOn {R : Type} [CommRing R] : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gs_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Sp S) (a : R) :
    gs (spMap f) z ⊤ (fnOn a) = gs (𝟙 (Sp S)) z ⊤ (fnOn (f a)) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have := gs_pull (𝟙 (Sp S)) (spMap f) z ⊤ trivial (fnOn a)
  rw [Category.id_comp] at this
  rw [← this]
  exact congrArg (gs (𝟙 (Sp S)) z ⊤) e.symm

def gsHom {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) : Γ(Y, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom

theorem gsHom_apply {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gsHom r z a = gs r z ⊤ a :=
  (gs_eq r z ⊤ trivial a).symm

theorem gs_res_fn {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (W : (Sp R).Opens) (r : Sp S ⟶ W.toScheme)
    (hr : r ≫ W.ι = spMap f) (z : Sp S) (a : R) :
    gsHom r z (W.ι.appTop.hom (fnOn a)) = gsHom (𝟙 (Sp S)) z (fnOn (f a)) := by
  rw [gsHom_apply, gsHom_apply, ← gs_spMap, ← hr]
  exact gs_pull r W.ι z ⊤ trivial _

theorem eq_zero_of_generic {R : Type} [CommRing R] [IsDomain R] (W : (Sp R).Opens)
    (lam : Sp (FractionRing R) ⟶ W.toScheme) (hl : lam ≫ W.ι = jK R) (z : Sp (FractionRing R))
    (d : Γ(W.toScheme, ⊤)) (hd : gsHom lam z d = 0) : d = 0 := by
  haveI : AlgebraicGeometry.IsReduced W.toScheme := isReduced_of_isOpenImmersion W.ι
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w, w ∈ W.toScheme.basicOpen d := by
    by_contra h
    exact hne (le_bot_iff.1 fun w hw => h ⟨w, hw⟩)
  have hsp : W.ι (lam z) ⤳ W.ι w := by
    have e : W.ι (lam z) = jK R z := by rw [← hl]; rfl
    rw [e]
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have hz : (z : PrimeSpectrum (FractionRing R)).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (PrimeSpectrum.isPrime z).ne_top
    have ha' : algebraMap R (FractionRing R) a ∈ (z : PrimeSpectrum (FractionRing R)).asIdeal := ha
    rw [hz, Ideal.mem_bot] at ha'
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (ha'.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  have hsp' : lam z ⤳ w := W.ι.isOpenEmbedding.isInducing.specializes_iff.1 hsp
  have hm : z ∈ lam ⁻¹ᵁ W.toScheme.basicOpen d := hsp'.mem_open (W.toScheme.basicOpen d).isOpen hw
  rw [Scheme.preimage_basicOpen] at hm
  have hu := (Scheme.mem_basicOpen _ (U := lam ⁻¹ᵁ ⊤) _ z trivial).1 hm
  exact not_isUnit_zero (hd ▸ hu : IsUnit (0 : (Sp (FractionRing R)).presheaf.stalk z))

theorem val_spread : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (W : (Sp R).Opens) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (W.toScheme ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (W.toScheme ⟶ X)) (ε₂ : K₂ → ℤ), (∀ (U : Type) [CommGroup U] (h : (W.toScheme ⟶ X) → U), ∏ i, h (φ₁ i) ^ ε₁ i = ∏ i, h (φ₂ i) ^ ε₂ i) → ∀ (t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)), t₁.IsGen → t₂.IsGen → ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good L z J → val t₁ lam z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val t₂ lam z J) → ∀ z J, Good L z J → val t₁ g z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val t₂ g z J := by
  intro R V _ _ _ _ θ W X L hL K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ hF t₁ t₂ h₁ h₂ lam hl g hg x y k k' hy hk hk' H z J hJ
  obtain ⟨c, hc⟩ := exists_ratio hL hF h₁ h₂
  have hu : ∀ {F : Type} [Field F] (u : Fˣ) (w : Sp F),
      (gm (𝟙 (Sp F)) w ⊤ (unitOn u)).val = gsHom (𝟙 (Sp F)) w (fnOn (u : F)) := fun u w =>
    ((gsHom_apply _ _ _).trans (gs_unit _ w ⊤ trivial (unitOn u))).symm
  let z₀ : Sp (FractionRing R) := (⊥ : PrimeSpectrum (FractionRing R))
  choose I hI using fun χ : (TK R).left ⟶ X => exists_chart hL (χ z₀)
  have e₀ : gsHom lam z₀ c = gsHom (𝟙 (Sp (FractionRing R))) z₀ (fnOn (k : FractionRing R)) := by
    have := hc _ lam z₀ I hI
    rw [H z₀ I hI, mul_inv_cancel_right] at this
    exact (gsHom_apply _ _ _).trans (this.symm.trans (hu k z₀))
  have e₁ : c * W.ι.appTop.hom (fnOn y) - W.ι.appTop.hom (fnOn x) = 0 := by
    refine eq_zero_of_generic W lam hl z₀ _ ?_
    rw [map_sub, map_mul, gs_res_fn (algebraMap R (FractionRing R)) W lam hl,
      gs_res_fn (algebraMap R (FractionRing R)) W lam hl, ← hk, map_mul, map_mul]
    exact sub_eq_zero.2 (congrArg (· * _) e₀)
  have hg' : g ≫ W.ι = spMap ((algebraMap V (FractionRing V)).comp θ) :=
    hg.trans (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  have e₂ := congrArg (gsHom (Z := Sp (FractionRing V)) g z) (sub_eq_zero.1 e₁)
  rw [map_mul, gs_res_fn _ W g hg', gs_res_fn _ W g hg', RingHom.comp_apply, RingHom.comp_apply, ← hk', map_mul,
    map_mul] at e₂
  have hy' : IsUnit (algebraMap V (FractionRing V) (θ y)) :=
    isUnit_iff_ne_zero.2 fun h => hy (IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm))
  have e₃ := ((hy'.map fnOn).map (gsHom (𝟙 (Sp (FractionRing V))) z)).mul_right_cancel e₂
  refine mul_inv_eq_iff_eq_mul.1 (Units.ext ?_)
  exact (hc _ g z J hJ).trans ((gsHom_apply _ _ _).symm.trans (e₃.trans (hu k' z).symm))

end GlobalTheory.GenSpread

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorProportionalitySpreadsFromGenericStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.generator_proportionality_spreads_from_generic : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (W : (Sp R).Opens) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (W.toScheme ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (W.toScheme ⟶ X)) (ε₂ : K₂ → ℤ), (∀ (U : Type) [CommGroup U] (h : (W.toScheme ⟶ X) → U), ∏ i, h (φ₁ i) ^ ε₁ i = ∏ i, h (φ₂ i) ^ ε₂ i) → ∀ (t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)), t₁.IsGen → t₂.IsGen → ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good L z J → val t₁ lam z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val t₂ lam z J) → ∀ z J, Good L z J → val t₁ g z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val t₂ g z J := by
  first | exact @GlobalTheory.GenSpread.val_spread | exact GlobalTheory.GenSpread.val_spread | (intros; apply GlobalTheory.GenSpread.val_spread <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.FactorPeriod



theorem factor_period : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  intro R V _ _ _ _ θ Q D₀ F W ψW g hg a b u x y k k' hu hy hk hk' hτ z J J' hJ hJ'
  letI := D₀.P.isAb.comm
  obtain ⟨t, ht, tv, tl⟩ := GlobalTheory.T.exists_period_generator_on_open R D₀ W ψW (F.xi a) (F.f • F.xi b)
  have hQ : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left ≫
      (lift (fst Q.B Q.B ≫ F.inc) (snd Q.B Q.B ≫ F.inc ≫ F.o.onB.act F.f) : G2 Q.B ⟶ G2 D₀.P.A).left =
      𝟙 _ ≫ (lift (toUnit T ≫ D₀.c (F.xi a)) (toUnit T ≫ D₀.c (F.f • F.xi b))).left := fun T => by
    rw [Category.id_comp, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, F.o.c_lin, F.c_xi, F.c_xi]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := GlobalTheory.T.exists_generator_transport_mumfordBundleIso _ _ Q.B D₀.P.A Q.M.L D₀.P.L Q.M.isLB D₀.P.isLB _ F.w F.w_gen (TW W) (TW W)
    (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b) _ _ (𝟙 _) (hQ (TW W)) t ht
  obtain ⟨lam, hlam⟩ : ∃ lam : (TK R).left ⟶ W.toScheme, lam ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact GlobalTheory.TauPull.jK_mem p _ ⟨(g z).1, (g z).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have hl : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left =
      T.hom ≫ (lift (Q.c a) (Q.c b)).left := fun T => by
    rw [← comp_lift]; rfl
  have H := GlobalTheory.T.generator_proportionality_spreads_from_generic R V θ W Q.B.left Q.M.L Q.M.isLB (Fin 4) (Fin 4)
    (lamPts (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)) negε
    (fun i => W.ι ≫ lamPts (Q.c a) (Q.c b) i) negε (fun U _ h => Finset.prod_congr rfl fun i _ => by
      congr 2
      fin_cases i
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TW W)) (Q.c a) (Q.c b)).symm
      · rfl
      · rfl
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TW W))).symm)
    t₁ (LB.pullGen Q.M.L _ _ u W.ι) ht₁ (DVR.pullGen_isGen _ _ _ _ hu _) lam hlam g hg x y k k' hy hk hk'
    (fun p I' hI' => by
      obtain ⟨I, hI⟩ := DegPull.exists_good' D₀.P.isLB p
      have e₁ := v₁ _ lam p I I' hI hI'
      have e₂ : lam ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
          (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left := by
        rw [hl, hl, ← Category.assoc]
        exact congrArg (· ≫ _) hlam
      rw [e₂] at e₁
      erw [Category.comp_id] at e₁
      refine e₁.trans ((congrArg (_ * ·) (tl lam hlam p I hI)).trans ((F.tau a b p I I' hI hI').symm.trans
        ((hτ p I' hI').trans (congrArg (_ * ·) ?_))))
      rw [val_pull hI', hlam]
      rfl) z J' hJ'
  have e₁ := v₁ _ g z J J' hJ hJ'
  have e₂ : g ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left := by
    rw [hl, ← Category.assoc]
    exact congrArg (· ≫ _) hg
  rw [e₂] at e₁
  erw [Category.comp_id] at e₁
  rw [val_pull hJ', hg] at H
  exact H.symm.trans (e₁.trans (congrArg (_ * ·) (tv _ g z J hJ)))

end GlobalTheory.FactorPeriod
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotent_factor_periods_at_generating_point : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  first | exact @GlobalTheory.FactorPeriod.factor_period | exact GlobalTheory.FactorPeriod.factor_period | (intros; apply GlobalTheory.FactorPeriod.factor_period <;> assumption)
end
end
