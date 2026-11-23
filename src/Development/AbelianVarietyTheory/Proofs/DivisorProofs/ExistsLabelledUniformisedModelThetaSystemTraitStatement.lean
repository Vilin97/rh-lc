module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.IdlAlongNeTopOfValOn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEight
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
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagEndIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteExtensionClassicalPointFactorsStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadNonnegOfInt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEightStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc Formalism.L2.Pj

theorem _root_.GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) := by
  first | exact @GlobalTheory.EighthTorsion.main | exact GlobalTheory.EighthTorsion.main | (intros; apply GlobalTheory.EighthTorsion.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackEighthPowerEndomorphismsFieldPoint

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DiagPull


open MonObj in
theorem isDiagEnd_pull {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A))
    (hS : IsDiagEnd F W P u ε) (hφ : IsGrpPullback P'.A P.A f φ) (hL : LBIso P'.L (P.L.pull φ))
    (hε' : ∀ E, (ε' E).left ≫ φ = φ ≫ (ε E).left) : IsDiagEnd F W P' (f ≫ u) ε' := by
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hε⟩ := hS
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n _ (zetaAway n) T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  refine ⟨c', hc'u, pr', hmon, huniv', ?_, fun E a => injψ ?_⟩
  swap
  · have e₁ : pushPt hφ.1.w (ε' E) = pushPt hφ.1.w (𝟙 P'.A) ≫ ε E := Over.OverMorphism.ext (by
      show (ε' E).left ≫ φ = ((𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ) ≫ (ε E).left
      rw [hε', Over.id_left, Category.id_comp])
    rw [push_comp, e₁, Category.assoc, hε]
    change diagPrecomp (M := c.A) (pushPt hφ.1.w (𝟙 P'.A)) _ = pushHom hψ _ _
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    refine (map_zpow (diagPrecomp (M := c.A) (pushPt hφ.1.w (𝟙 P'.A))) (pr b) (E a b)).trans
      (Eq.trans ?_ (map_zpow (pushHom hψ P'.A) (pr' b) (E a b)).symm)
    congr 1
    have e₂ := push_comp (𝟙 P'.A) b
    rw [Category.id_comp] at e₂
    exact e₂.symm
  let ε₀ : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c.P q ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε₀
  have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε₀
  have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε₀).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε₀
  have l3 : (LB.LinComb c'.P q' ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε₀
  have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε₀).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
  have i3 : LBIso ((LB.LinComb c.P q ε₀).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) :=
    LBIso.chartPull (chartPullOut c.P q ε₀ φ _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) (LB.LinComb (c.P.pull ψ₂) q' ε₀) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε₀ (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε₀) (LB.LinComb c'.P q' ε₀) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε₀
  have h1 := pull_isLB P.isLB φ
  have h2 := pull_isLB l0 φ
  exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))

theorem exists_pull_field : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] (P : PolAV (Sp R)) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (u' : Sp R ⟶ F.X), IsDiagEnd F W P u' ε → ∀ (K : Type) [Field K] (yK : R →+* K), ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ P.A.left) (_ : IsGrpPullback A.A P.A (spMap yK) φ) (_ : LBIso A.L (P.L.pull φ)) (εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A)), IsDiagEnd F W A (spMap yK ≫ u') εA ∧ ∀ (Y : Over (Sp K)) (x x' : Y ⟶ A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), x'.left ≫ φ = x.left ≫ φ ≫ (ε E).left → x' = x ≫ εA E := by
  intro g n F W R _ P ε u' hS K _ yK
  let A : PolAV (Sp K) := by
    open GlobalTheory GlobalTheory.Ex GlobalTheory.ModelData GlobalTheory.DegPull in
      exact {
        A := (Over.pullback (spMap yK)).obj P.A
        isAb := TLinPf.isAb_pullback (spMap yK) P.A P.isAb
        g := P.g
        smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
          (isGrpPullback_pullback P.A (spMap yK)).1 P.smoothDim
        L := P.L.pull (pullback.fst P.A.hom (spMap yK))
        isLB := pull_isLB P.isLB _
        rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A (spMap yK)) P.rigid
        sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A (spMap yK)) P.sym
        ample := by
          haveI := P.isAb.proper
          exact AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom (spMap yK))
        ktriv := by
          obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom (spMap yK)))
          exact kTriv_pull (isGrpPullback_pullback P.A (spMap yK)) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv }
  let φ : A.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap yK)
  have hφ : IsGrpPullback A.A P.A (spMap yK) φ := isGrpPullback_pullback P.A (spMap yK)
  have hL : LBIso A.L (P.L.pull φ) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ A.isLB
  have w : ∀ E, (φ ≫ (ε E).left) ≫ P.A.hom = A.A.hom ≫ spMap yK := fun E => by
    rw [Category.assoc, Over.w, hφ.1.w]
  let εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A) := fun E =>
    Over.homMk (hφ.1.lift (φ ≫ (ε E).left) A.A.hom (w E)) (hφ.1.lift_snd _ _ _)
  have hεA : ∀ E, (εA E).left ≫ φ = φ ≫ (ε E).left := fun E => hφ.1.lift_fst _ _ _
  refine ⟨A, φ, hφ, hL, εA, isDiagEnd_pull F W P A u' (spMap yK) φ ε εA hS hφ hL hεA, fun Y x x' E h => ?_⟩
  refine Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  rw [h, Over.comp_left, Category.assoc, hεA]

end GlobalTheory.Poinc.DiagPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackEighthPowerEndomorphismsFieldPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] (P : PolAV (Sp R)) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (u' : Sp R ⟶ F.X), IsDiagEnd F W P u' ε → ∀ (K : Type) [Field K] (yK : R →+* K), ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ P.A.left) (_ : IsGrpPullback A.A P.A (spMap yK) φ) (_ : LBIso A.L (P.L.pull φ)) (εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A)), IsDiagEnd F W A (spMap yK ≫ u') εA ∧ ∀ (Y : Over (Sp K)) (x x' : Y ⟶ A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), x'.left ≫ φ = x.left ≫ φ ≫ (ε E).left → x' = x ≫ εA E := by
  first | exact @GlobalTheory.Poinc.DiagPull.exists_pull_field | exact GlobalTheory.Poinc.DiagPull.exists_pull_field | (intros; apply GlobalTheory.Poinc.DiagPull.exists_pull_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoordStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.psi_value_fractionRing_of_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (r : R), Formalism.L2.Pj.PsiCoord D χ r → ∃ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧ valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  first | exact @GlobalTheory.Poinc.valF_psi_of_psiCoord | exact GlobalTheory.Poinc.valF_psi_of_psiCoord | (intros; apply GlobalTheory.Poinc.valF_psi_of_psiCoord <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem traitLabels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW o Ω _ _ _ _ S ρ ε u' hD p _ y₀ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hβ⟩ := GlobalTheory.T.exists_trait_finiteExtension_classicalPoint_factors g n F o Ω S u' p y₀ T ι hι hsp
  obtain ⟨A, φ, cart, lb, εA, hDA, huniq⟩ := GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point g n F W S.R ρ.P ε u' hD (FractionRing T'.V) yK
  rw [hy'] at hDA
  obtain ⟨G', _, _, hsemi, D', U', j', hpsi, hcong⟩ := GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight g n F W hW T' A εA hDA
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p y₀ := { V := T'.V, complete := T'.complete, norm_le := hι', yK := yK, fac := hfac, A := A, φ := φ, cart := cart, lb := lb, G := G', semi := hsemi, D := D', U := U' }
  obtain ⟨l⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p y₀ u hint
  let jj : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X) := j'.trans (AddEquiv.piCongrRight fun _ => e)
  refine ⟨u, l, jj, ?_, ?_⟩
  · intro χ

    obtain ⟨v, hv⟩ := hpsi χ
    obtain ⟨jc, hjc, hval⟩ := GlobalTheory.T.psi_value_fractionRing_of_psiCoord T'.V D'.toPre χ _ hv
    have hq := l.q_eq χ jc hjc
    change ‖algebraMap (FractionRing T'.V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing T'.V))) _ ((D'.toPre.psi χ).s jc).val)‖ = _ at hq
    rw [hval, RingHom.algebraMap_toAlgebra] at hq

    have hunit : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ = 1 := by
      have h1 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h2 : ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (v : T'.V))), norm_nonneg (ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V)))]
    set a := ‖ι' (algebraMap T'.V _ T'.ϖ)‖ with ha
    have hq0 : 0 ≤ qW W T'.β (j' χ) :=
      qW_nonneg_of_posW W hW.1 T'.β T'.symm (GlobalTheory.Poinc.Basic₂.trait_nonneg T') (j' χ)
    have hsc : qW W T'.β (j' χ) = (k : ℤ) * qW W T.β (jj χ) := by
      simp only [qW, hβ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply]
      ring
    rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
    rw [← ha] at hq
    have hN : ((qW W T'.β (j' χ)).toNat : ℝ) = ((k : ℤ) : ℝ) * (qW W T.β (jj χ) : ℝ) := by
      rw [← Int.cast_mul, ← hsc]
      exact_mod_cast Int.toNat_of_nonneg hq0
    have hapos : 0 < a := by
      rw [ha, norm_pos_iff]
      intro h0
      have : algebraMap T'.V (FractionRing T'.V) T'.ϖ = 0 := ι'.injective (by rw [h0, map_zero])
      exact T'.irr.ne_zero (IsFractionRing.injective T'.V (FractionRing T'.V) (by rw [this, map_zero]))
    have hl : -l.q χ = ((qW W T'.β (j' χ)).toNat : ℝ) * Real.log a := by
      rw [← Real.log_pow, hq, Real.log_exp]
    rw [hϖ, Real.log_pow]
    rw [hN] at hl
    push_cast at hl ⊢
    linarith
  · intro m pk pk' x x' E hm h1 h2 hx
    have hc := hcong (PadicAlgCl p) m pk pk' x x' E hm h1 h2 (huniq _ x x' E hx)
    obtain ⟨w, hw⟩ := hc
    refine ⟨fun a => e (w a), ?_⟩
    funext a
    have := congrFun hw a
    simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply] at this ⊢

    rw [this, map_add (f := _), map_sum, map_nsmul]
    simp [map_zsmul]

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_labelled_uniformisedModel_thetaSystem_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  first | exact @GlobalTheory.Poinc.traitLabels | exact GlobalTheory.Poinc.traitLabels | (intros; apply GlobalTheory.Poinc.traitLabels <;> assumption)
end
end
