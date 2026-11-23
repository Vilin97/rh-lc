module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
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
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisationsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartingsThetaSetupSameGeometricFibreAtTraitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullback
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed

-- Source module: Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsLatticePart

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelMove

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)

section Identification

variable (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
  (oP : letI := H.starRing; P.toPre.OAct (𝓞 E))

end Identification

theorem exists_lattice_part {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] (n : ℕ) (hn : 0 < n) (y : D.X) : ∃ p : QkPt D F n, p.y = y :=
  exists_qkPt GlobalTheory.abelianSchemeLaws_all.1.mulN (Or.inr GlobalTheory.abelianSchemeLaws_all.1.polBaseChange) hB hn.ne' y

end GlobalTheory.LevelMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndoPt

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (T : Over S') :
    ∃ E : (T ⟶ G') ≃* (Over.mk (T.hom ≫ g) ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ g) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ g
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have inj : Function.Injective F := fun x y e => by
    apply Over.OverMorphism.ext
    refine h.1.hom_ext ?_ ?_
    · rw [← hF, ← hF, e]
    · rw [Over.w x, Over.w y]
  have sur : Function.Surjective F := fun z => by
    have w : z.left ≫ G.hom = T.hom ≫ g := Over.w z
    refine ⟨Over.homMk (h.1.lift z.left T.hom w) (h.1.lift_snd _ _ w), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ w
  refine ⟨{ Equiv.ofBijective F ⟨inj, sur⟩ with map_mul' := fun x y => ?_ }, hF⟩
  apply Over.OverMorphism.ext
  exact (h.2 T x y (F x) (F y) rfl rfl).symm

theorem exists_point_of_isMonHom {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (f : G ⟶ G) [IsMonHom f] (m : ℕ) {T : Over S'}
    (x : T ⟶ G') (hx : x ^ m = 1) :
    ∃ x₂ : T ⟶ G', x₂.left ≫ φ = x.left ≫ φ ≫ f.left ∧ x₂ ^ m = 1 := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points h T
  refine ⟨E.symm (E x ≫ f), ?_, ?_⟩
  · rw [← hE, MulEquiv.apply_symm_apply, Over.comp_left, hE, Category.assoc]
  · rw [← map_pow, ← MonObj.pow_comp, ← map_pow, hx, map_one, MonObj.one_comp, map_one]

theorem exists_endo_point : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  intro o Ω _ _ _ S ρ p _ y₀ u f hf m x hx
  exact exists_point_of_isMonHom u.cart f m x hx

end GlobalTheory.EndoPt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  first | exact @GlobalTheory.EndoPt.exists_endo_point | exact GlobalTheory.EndoPt.exists_endo_point | (intros; apply GlobalTheory.EndoPt.exists_endo_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  first | exact @GlobalTheory.PtTrans.ptTrans | exact GlobalTheory.PtTrans.ptTrans | (intros; apply GlobalTheory.PtTrans.ptTrans <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (b : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left → x ^ (S.r * S.N) = 1 := by
  first | exact @GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | exact GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | (intros; apply GlobalTheory.LabelTorsion.pow_eq_one_of_over_label <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQWAutomorphismEighthPowerLatticeLabels

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GeomCore

section Cong
variable {X : Type} [AddCommGroup X]

theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong

open MonObj in
theorem core : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x ν, yy x = QuotientAddGroup.mk ν → yy' x = QuotientAddGroup.mk (θ ν)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := by
  intro g n F W Z i X ε hd p _ z c yy yy' h1 h2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', hS, -, hR, y₀, hy₀, u, l, j, hq, hyy, hall⟩ := h1
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', ε'', hS₁, -, hR₁, y₁, hy₁, u', l', j', hq', hyy', hall'⟩ := h2
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab, hε⟩ := GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait g n F W Z i X ε p z c c₀ hc R' fg frac hth hev ρ' ε' hS hR
    y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS₁ hR₁ y₁ hy₁ u u'
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) :=
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have tors : ∀ m, 1 ≤ m → (∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have tors' : ∀ m, 1 ≤ m → (∀ x : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have ord : ∀ m pk (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
      x ^ m = 1 := fun m pk x h => by
    obtain ⟨w, hw⟩ := u.U.ext
    exact (h w hw).1
  have hqe : ∀ χ, l'.q (e χ) = l.q χ := fun χ => by
    have h2 := (hψ χ _).1 (l.q_eq χ)
    have h3 := GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (l'.q_eq (e χ))
    exact (neg_injective (Real.exp_injective h3)).symm
  have hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), l.yy b = QuotientAddGroup.mk χ →
      l'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ) := fun b χ χ' h h' => by
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab b
    obtain ⟨pk, hpk⟩ := (tors _ hrN).1 x (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ' p y₀ u b x hx)
    obtain ⟨pk', hpk'⟩ := (tors' _ hrN).1 x' (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ'' p y₁ u' b x' hx')
    have e1 := l.yy_eq b pk x hpk hx
    have e2 := l'.yy_eq b pk' x' hpk' hx'
    have t := htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'
    have c1 : CongMod (X.S.r * X.S.N) χ pk.y := cm_of_mk (h.symm.trans e1)
    have c2 : CongMod (X.S.r * X.S.N) χ' pk'.y := cm_of_mk (h'.symm.trans e2)
    exact cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))
  have hcom : ∀ m, 1 ≤ m → ∀ E (χ : u.D.toPre.X), ∃ χ₂ : u.D.toPre.X,
      CongMod m (j χ₂) (matAct E (j χ)) ∧ CongMod m (j' (e χ₂)) (matAct E (j' (e χ))) := fun m hm E χ => by
    obtain ⟨pk, rfl⟩ := GlobalTheory.LevelMove.exists_lattice_part u.D.toPre u.D.tau_bimult (PadicAlgCl p) m hm χ
    obtain ⟨x, hQ⟩ := (tors m hm).2 pk
    obtain ⟨w, x', hw, hwa, hwa', hx'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x (ord m pk x hQ)
    obtain ⟨pk', hQ'⟩ := (tors' m hm).1 x' hx'
    have hmon := GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre g n F W Z i X ε hd c₀ hc R' fg frac hth hev ρ' ε' hS E
    obtain ⟨x₂, hx₂φ, hx₂⟩ := GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model _ ρ' p y₀ u (ε' E) hmon m x (ord m pk x hQ)
    obtain ⟨pk₂, hQ₂⟩ := (tors m hm).1 x₂ hx₂
    obtain ⟨w₂, x₂', hw₂, hw₂a, hw₂a', hx₂'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x₂ hx₂
    obtain ⟨pk₂', hQ₂'⟩ := (tors' m hm).1 x₂' hx₂'
    have hε₂ : x₂'.left ≫ u'.φ = x'.left ≫ u'.φ ≫ (ε'' E).left := by
      have := hε E w w₂ hw hw₂ (by rw [← Category.assoc, hw₂a, hx₂φ, ← hwa]; simp only [Category.assoc])
      rw [← hw₂a', ← hwa']
      simpa only [Category.assoc] using this
    have c1 := hall m pk pk₂ x x₂ E hm hQ hQ₂ hx₂φ
    have c2 := hall' m pk' pk₂' x' x₂' E hm hQ' hQ₂' hε₂
    have t1 := htor m pk pk' x x' w hm hQ hQ' hw hwa hwa'
    have t2 := htor m pk₂ pk₂' x₂ x₂' w₂ hm hQ₂ hQ₂' hw₂ hw₂a hw₂a'
    refine ⟨pk₂.y, c1, ?_⟩
    exact cm_trans (cm_symm (cm_map j'.toAddMonoidHom t2))
      (cm_trans c2 (cm_map (matAct E) (cm_map j'.toAddMonoidHom t1)))
  refine ⟨(j.symm.trans e).trans j', ?_, ?_, ?_⟩
  · intro v
    obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    have h1 := hq χ
    have h2 := hq' (e χ)
    rw [hqe] at h2
    have hs := c.scale_pos
    have h4 : ((qW W c.T.β (j' (e χ)) : ℤ) : ℝ) = ((qW W c.T.β (j χ) : ℤ) : ℝ) :=
      mul_left_cancel₀ hs.ne' (h2.symm.trans h1)
    exact_mod_cast h4
  · intro b ν hν
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    obtain ⟨χ', hχ'⟩ := QuotientAddGroup.mk_surjective (l'.yy b)
    have e1 := hyy b χ hχ.symm
    have e2 := hyy' b χ' hχ'.symm
    rw [e2]
    apply cm_mk
    have c0 : CongMod (X.S.r * X.S.N) ν (j χ) := cm_of_mk (hν.symm.trans e1)
    have c3 := hlabe b χ χ' hχ.symm hχ'.symm
    have c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ := by simpa using cm_map j.symm.toAddMonoidHom c0
    exact cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))
  · intro m hm E v
    obtain ⟨χ, rfl⟩ := j.surjective v
    obtain ⟨χ₂, c1, c2⟩ := hcom m hm E χ
    have c3 : CongMod m (j.symm (matAct E (j χ))) χ₂ := by
      simpa using cm_symm (cm_map j.symm.toAddMonoidHom c1)
    have c4 := cm_trans (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c3)) c2
    simpa [matAct] using c4

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (θ μ)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := core

end GlobalTheory.GeomCore
end
end
end
