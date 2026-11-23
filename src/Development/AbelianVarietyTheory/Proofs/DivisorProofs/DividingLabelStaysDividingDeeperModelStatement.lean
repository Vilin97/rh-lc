module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTowerSameGenericFibreRealisations

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem Tower.same : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ 𝔗 : Tower X₁ act, GlobalTheory.Poinc.Same X₁.ρ act 𝔗.X₂.ρ 𝔗.act₂ 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  intro g n F W Z i X₁ act hact 𝔗
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let P₀ : PolAV (Sp 𝔗.X₂.Ω₁) :=
    { A := (Over.pullback f₂).obj 𝔗.X₂.ρ.P.A
      isAb := TLinPf.isAb_pullback f₂ _ 𝔗.X₂.ρ.P.isAb
      g := 𝔗.X₂.ρ.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂).1 𝔗.X₂.ρ.P.smoothDim
      L := 𝔗.X₂.ρ.P.L.pull (pullback.fst 𝔗.X₂.ρ.P.A.hom f₂)
      isLB := pull_isLB 𝔗.X₂.ρ.P.isLB _
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.sym
      ample := by
        haveI := 𝔗.X₂.ρ.P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback 𝔗.X₂.ρ.P.isLB 𝔗.X₂.ρ.P.ample
          (IsPullback.of_hasPullback 𝔗.X₂.ρ.P.A.hom f₂)
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB 𝔗.X₂.ρ.P.isLB (pullback.fst 𝔗.X₂.ρ.P.A.hom f₂))
        exact kTriv_pull (isGrpPullback_pullback 𝔗.X₂.ρ.P.A f₂) 𝔗.X₂.ρ.P.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) ((isGen_iff w).1 hw) 𝔗.X₂.ρ.P.ktriv }
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun E => (Over.pullback f₂).map (𝔗.act₂ E), ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    have h1 : ((Over.pullback f₂).map (𝔗.act₂ E)).left ≫ a' = a' ≫ (𝔗.act₂ E).left :=
      pullback.lift_fst _ _ _
    refine ⟨?_, h1⟩
    have h2 : (a' ≫ (𝔗.act₂ E).left) ≫ 𝔗.φ = a' ≫ 𝔗.φ ≫ (act E).left := by
      rw [Category.assoc, 𝔗.act_eq]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) h1).trans h2)
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _
end GlobalTheory.Poinc.Sep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTowerSameGenericFibreRealisationsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaSetupTower_same_genericFibre_realisations : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ 𝔗 : Tower X₁ act, GlobalTheory.Poinc.Same X₁.ρ act 𝔗.X₂.ρ 𝔗.act₂ 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.same | exact GlobalTheory.Poinc.Sep.Tower.same | (intros; apply GlobalTheory.Poinc.Sep.Tower.same <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelPersistsThetaSetupTower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem Tower.div_lam : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx V _ _ _ ev X _ m t δ _
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hdvd : X₁.S.r * X₁.S.N ∣ 𝔗.X₂.S.r * 𝔗.X₂.S.N := ⟨𝔗.d, 𝔗.lev⟩
  obtain ⟨a, ha, hdv⟩ := DivDeep.exists_div_torsion 𝔗.X₂ 𝔗.isAct z₂
    (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < 𝔗.X₂.S.r * 𝔗.X₂.S.N := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  choose x hxa using fun s => DivDeep.exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  have hd : 𝔗.X₂.S.r * 𝔗.X₂.S.N / (X₁.S.r * X₁.S.N) = 𝔗.d := by
    rw [𝔗.lev]; exact Nat.mul_div_cancel_left _ hk
  rw [hd] at hxa
  obtain ⟨b, hb⟩ := 𝔗.lam_range x
  obtain rfl : 𝔗.lam b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := DivDeep.same_ratio (GlobalTheory.T.thetaSetupTower_same_genericFibre_realisations g n F W Z i X₁ act hact 𝔗) x₀ b
  set φ := algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : 𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (𝔗.X₂.M.O z₂) := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := 𝔗.X₂.normal
    exact ⟨𝔗.X₂.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z₂
  have m₁ : 𝔗.X₂.S.th (𝔗.lam b) * φ (X₁.S.th x₀) / (𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b)) ∈ 𝔗.X₂.M.O z₂ :=
    DivDeep.root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ 𝔗.X₂.M.O z₂ := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, show 𝔗.p z₂ ∈ U from hz₂ ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
    rw [𝔗.p_pt, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp

end GlobalTheory.Poinc.Sep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelPersistsThetaSetupTowerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.dividingLabel_persists_thetaSetupTower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.div_lam | exact GlobalTheory.Poinc.Sep.Tower.div_lam | (intros; apply GlobalTheory.Poinc.Sep.Tower.div_lam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelStaysDividingDeeperModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.DeepDiv

end GlobalTheory.Poinc.Sep.DeepDiv

open GlobalTheory.Poinc.Sep

theorem GlobalTheory.Poinc.Sep.DeepDiv.div_lam : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ :=
  GlobalTheory.T.dividingLabel_persists_thetaSetupTower
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelStaysDividingDeeperModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.dividingLabel_stays_dividing_deeper_model : (∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  first | exact @GlobalTheory.Poinc.Sep.DeepDiv.div_lam | exact GlobalTheory.Poinc.Sep.DeepDiv.div_lam | (intros; apply GlobalTheory.Poinc.Sep.DeepDiv.div_lam <;> assumption)
end
end
