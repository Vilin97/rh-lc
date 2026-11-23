module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsMonomialFamilyCoordsOverBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedWeightFiltrationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerDatumObjectComesFromBaseOfLinearPointsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeModuleActionHomomorphism

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivLocal

theorem exists_pow_eq {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (hc : IsAdicComplete (maximalIdeal V) V) (hk : IsAlgClosed (ResidueField V))
    (B : Over (Sp V)) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ) (hn : IsUnit (n : V))
    (P : 𝟙_ (Over (Sp V)) ⟶ B) : ∃ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = P := by
  have hn' : IsUnit (n : Γ(Sp V, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  obtain ⟨-, hfin, het, hsurj⟩ :=
    GlobalTheory.abelianScheme_id_pow_finite_etale_surjective (Sp V) B n hB hn'
  set m : B ⟶ B := (𝟙 B) ^ n with hm
  let U : Over (Sp V) := Over.mk (pullback.snd m.left P.left)
  have hU : Smooth U.hom := by dsimp [U]; infer_instance
  let r : Sp (ResidueField V) ⟶ Sp V := spMap (residue V)
  let P₀ : Sp (ResidueField V) ⟶ B.left := r ≫ P.left
  have : CompactSpace ↥(pullback m.left P₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd m.left P₀)
  obtain ⟨p, -⟩ := (pullback.snd m.left P₀).surjective (default : PrimeSpectrum (ResidueField V))
  obtain ⟨z, -, hz⟩ :=
    isClosed_univ.exists_closed_singleton (X := ↥(pullback m.left P₀)) ⟨p, trivial⟩
  have hw := pointOfClosedPoint_comp (pullback.snd m.left P₀) z hz
  let x₀ : Sp (ResidueField V) ⟶ U.left :=
    pullback.lift (pointOfClosedPoint (pullback.snd m.left P₀) z hz ≫ pullback.fst _ _) r (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp])
  have hx₀ : x₀ ≫ U.hom = spMap ((residue V).comp (RingHom.id V)) := by
    rw [RingHom.comp_id]
    exact pullback.lift_snd _ _ _
  obtain ⟨a, ha, -⟩ :=
    GlobalTheory.HenselLift.exists_lift_mem_open V V hc (RingHom.id V) U hU x₀ hx₀ ⊤ (by simp)
  have ha' : a ≫ pullback.snd m.left P.left = 𝟙 _ := by
    refine ha.trans ?_
    rw [spMap, show CommRingCat.ofHom (RingHom.id V) = 𝟙 (CommRingCat.of V) from rfl, Spec.map_id]
  have key : (a ≫ pullback.fst m.left P.left) ≫ m.left = P.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha', Category.id_comp]
  refine ⟨Over.homMk (a ≫ pullback.fst m.left P.left) ?_, ?_⟩
  · rw [← Over.w m, ← Category.assoc, key]
    exact Over.w P
  · have e : ∀ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = Q ≫ m := fun Q => by
      rw [hm, comp_pow, Category.comp_id]
    rw [e]
    exact Over.OverMorphism.ext key

end GlobalTheory.AbDivLocal

namespace GlobalTheory.AbDivLocal

abbrev ptsModule {S : Scheme.{0}} (T : Over S) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type)
    [CommRing O] (a : OAct O B) : Module O (Additive (T ⟶ B)) where
  smul o p := Additive.ofMul (p.toMul ≫ a.act o)
  one_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 1) = p
    rw [a.one, Category.comp_id]; rfl
  mul_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o * o')) =
      Additive.ofMul ((p.toMul ≫ a.act o') ≫ a.act o)
    rw [mul_comm, a.mul, Category.assoc]
  smul_zero o := by
    change Additive.ofMul ((1 : T ⟶ B) ≫ a.act o) = Additive.ofMul 1
    haveI := a.hom o
    rw [one_comp]
  smul_add o p q := by
    change Additive.ofMul ((p.toMul * q.toMul) ≫ a.act o) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (q.toMul ≫ a.act o))
    haveI := a.hom o
    rw [mul_comp]
  add_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o + o')) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (p.toMul ≫ a.act o'))
    rw [a.add, comp_mul]
  zero_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 0) = Additive.ofMul 1
    have h0 : a.act 0 = 1 := by
      have h := a.add 0 0
      rw [add_zero] at h
      exact (mul_eq_left.mp h.symm)
    rw [h0, comp_one]

theorem exists_divided_linear : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (x : X → (𝟙_ (Over (Sp V)) ⟶ B)), (∀ y z, x (y + z) = x y * x z) → (∀ (o : O) y, x (o • y) = x y ≫ a.act o) → ∀ n : ℕ, IsUnit (n : V) → ∃ x' : X → (𝟙_ (Over (Sp V)) ⟶ B), (∀ y z, x' (y + z) = x' y * x' z) ∧ (∀ (o : O) y, x' (o • y) = x' y ≫ a.act o) ∧ ∀ y, x' (n • y) = x y := by
  intro V _ _ _ _ hc hk B _ hB O _ _ _ a X _ _ _ _ x hadd hsmul n hn
  haveI := hB.comm
  letI := ptsModule (𝟙_ (Over (Sp V))) B O a
  let g : X →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    { toFun := fun y => Additive.ofMul (x y)
      map_add' := fun y z => by rw [hadd]; rfl
      map_smul' := fun o y => by rw [hsmul]; rfl }
  let f : Additive (𝟙_ (Over (Sp V)) ⟶ B) →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    n • LinearMap.id
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨Q, hQ⟩ := exists_pow_eq hc hk B hB n hn p.toMul
    refine ⟨Additive.ofMul Q, ?_⟩
    change n • Additive.ofMul Q = p
    rw [← ofMul_pow, hQ]; rfl
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  refine ⟨fun y => (h y).toMul, fun y z => by
      change (h (y + z)).toMul = (h y).toMul * (h z).toMul
      rw [map_add (f := _)]; rfl,
    fun o y => by
      change (h (o • y)).toMul = (h y).toMul ≫ a.act o
      rw [map_smul]; rfl, fun y => ?_⟩
  have e : n • h y = Additive.ofMul (x y) := LinearMap.congr_fun hh y
  change (h (n • y)).toMul = x y
  rw [map_nsmul, e]; rfl

end GlobalTheory.AbDivLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeModuleActionHomomorphismStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_scheme_module_action_homomorphism : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (x : X → (𝟙_ (Over (Sp V)) ⟶ B)), (∀ y z, x (y + z) = x y * x z) → (∀ (o : O) y, x (o • y) = x y ≫ a.act o) → ∀ n : ℕ, IsUnit (n : V) → ∃ x' : X → (𝟙_ (Over (Sp V)) ⟶ B), (∀ y z, x' (y + z) = x' y * x' z) ∧ (∀ (o : O) y, x' (o • y) = x' y ≫ a.act o) ∧ ∀ y, x' (n • y) = x y := by
  first | exact @GlobalTheory.AbDivLocal.exists_divided_linear | exact GlobalTheory.AbDivLocal.exists_divided_linear | (intros; apply GlobalTheory.AbDivLocal.exists_divided_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturatedStatement

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lower_datum_of_isotropic_saturated : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (Z : Submodule (𝓞 E) Dw.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → ∃ (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f ∧
    D'.p = Dw.p - Module.finrank (𝓞 E) Z ∧ D'.q = Dw.q - Module.finrank (𝓞 E) Z := by
  first | exact @GlobalTheory.LowDat.exists_lowerDatum | exact GlobalTheory.LowDat.exists_lowerDatum | (intros; apply GlobalTheory.LowDat.exists_lowerDatum <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometryStatement

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → GlobalTheory.LowDat.IsLower Dw D' Z f →
  Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X →
  D'.p = Dw.p - Module.finrank (𝓞 E) Z → D'.q = Dw.q - Module.finrank (𝓞 E) Z →
  ∀ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
  (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I) →
  ∃ (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.FiltGraded C Z F I →
      ∃ I' : GlobalTheory.LowDat.LowTate C D' o' F, GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  first | exact @GlobalTheory.LowDat.LowObj.exists_lowObj | exact GlobalTheory.LowDat.LowObj.exists_lowObj | (intros; apply GlobalTheory.LowDat.LowObj.exists_lowObj <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailExtra

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LowDat.exists_lower : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
  GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R, 1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    GlobalTheory.LowDat.IsLower Dw D' Z f ∧ D'.p = Dw.p - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    D'.q = Dw.q - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : GlobalTheory.LowDat.LowTate C D' o' F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I ∧
          GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨Z, hZ, hrk, tK, m1, m2, hI⟩ := GlobalTheory.T.exists_isotropic_saturated_weight_filtration Xo c R hR C hr
  obtain ⟨D', f, hf, hp, hq⟩ := GlobalTheory.T.exists_lower_datum_of_isotropic_saturated Dw Z hZ
  obtain ⟨o', φB, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry Xo c R hR C Z D' f hZ hf hrk hp hq tK m1 m2 hI
  refine ⟨Z, D', f, o', φB, hZ, hrk, hf, hrk ▸ hp, hrk ▸ hq, h1, h2, h3, tK, m1, m2, ?_⟩
  intro F _ _ _
  obtain ⟨I, hI1, hI2⟩ := hI F
  obtain ⟨I', hI'⟩ := h4 F I hI1 hI2
  exact ⟨I, I', hI1, hI2, hI'⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegeneratingFamilyDataFromBaseAlgClosedResidue

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VData

theorem exists_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (s : Fin C.m ⊕ Fin N → V), D'.p + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.p ∧ D'.q + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.q ∧ IsLocalHom θ₀ ∧ θ₀.comp L.b = C.b ∧ (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) ∧ (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C hX
  haveI : IsNoetherianRing V := hV.1.1
  haveI : CharZero V := hV.2
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  haveI : Module.Finite (𝓞 E) C.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hr : 1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X := Module.finrank_pos
  obtain ⟨Z, D', f, o', φB, -, -, -, hp, hq, hpb, hact, hw, -⟩ := GlobalTheory.LowDat.exists_lower Xo c V hV C.toFam hr
  have hrk := C.rank
  haveI : IsMonHom (Iso.refl C.P.D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨i, hi, hiφ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl C.P.D.toPre.P.A)) hpb
  have hiφ' : i.hom.left ≫ φB = 𝟙 _ := hiφ
  have hia : ∀ a : 𝓞 E, (letI := H.starRing; C.P.oD.onB.act a) ≫ i.hom = i.hom ≫ o'.t.act.act a := by
    intro a
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hiφ', hact, ← Category.assoc, hiφ',
        Category.comp_id, Category.id_comp]
    · rw [Over.w, Over.w]
  have hM : IsUnit ((l.M' : ℕ) : V) := by
    have h1 : IsUnit ((l.M' : ℕ) : c.F) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 (level_pos l).ne')
    simpa using h1.map C.b
  obtain ⟨x', hx₁, hx₂, hx₃⟩ := GlobalTheory.T.abelian_scheme_module_action_homomorphism V hV.1.2.2.2 hk o'.t.G
    ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩ (𝓞 E) o'.t.act
    C.P.D.toPre.X (fun y => C.P.D.toPre.c y ≫ i.hom)
    (fun y z => by
      rw [C.P.D.toPre.c_add, ← MonObj.mul_comp]; rfl)
    (fun a y => by
      letI := H.starRing
      rw [C.P.oD.c_lin, Category.assoc, hia, Category.assoc]) l.M' hM
  obtain ⟨L, θ₀, e, m, hθ, hb, hc⟩ := GlobalTheory.T.lowerDatumObject_comes_from_base_of_linearPoints D' c V C.b o' C.P.D.toPre.X x' hx₁ hx₂
  obtain ⟨N, b, hbas⟩ := C.cone.basis
  let ε := b.map (pullBalEquiv H.bar e).symm
  have hε : ∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := fun j => by
    have h1 : pullBalEquiv H.bar e (ε (.inl j)) = ⟨C.δ j, C.cone.mem j⟩ := by
      simp [ε, hbas]
    exact (congrArg Subtype.val h1).symm
  have hPL := C.P.D.toPre.P.isLB
  have l₁ : LBIso C.P.D.toPre.P.L (o'.t.PP.L.pull i.hom.left) :=
    LBIso.trans hPL (pull_isLB hPL _) (pull_isLB o'.t.PP.isLB _)
      ((GlobalTheory.PolBaseChange.lbIso_refl hPL).chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl))
      (GenSpread.lbIso_pull_of_lbIso hw i.hom.left hiφ'.symm).symm
  have l₂ : LBIso o'.t.PP.L (L.o.t.PP.L.pull m.toSABMap.φ) := m.lin.imp fun _ h => h.1
  have l₃ : LBIso o'.t.PP.L (L.D.P.L.pull (m.toSABMap.φ ≫ L.φB)) :=
    LBIso.trans o'.t.PP.isLB (pull_isLB L.o.t.PP.isLB _) (pull_isLB L.D.P.isLB _) l₂ (GenSpread.lbIso_pull_of_lbIso L.ab.2.2 _ rfl)
  obtain ⟨s, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_periods_monomialFamily_coords_over_base Xo c φ V hV hk C D' L θ₀ e (i.hom.left ≫ m.toSABMap.φ ≫ L.φB)
    (((isGrpPullback_of_iso i).comp (m.cart.comp L.ab.1)).congr (by simp) rfl)
    (fun a => by
      have h1 := congrArg (·.left) (hia a)
      simp only [Over.comp_left] at h1
      rw [← Category.assoc, h1, Category.assoc, ← Category.assoc _ m.toSABMap.φ, m.act, Category.assoc, L.ab.2.1]
      simp only [Category.assoc])
    (LBIso.trans hPL (pull_isLB o'.t.PP.isLB _) (pull_isLB L.D.P.isLB _) l₁ (GenSpread.lbIso_pull_of_lbIso l₃ _ rfl))
    (fun y => by
      rw [← map_nsmul, ← hc, hx₃, Over.comp_left, Category.assoc]) N ε hε
  exact ⟨D', L, θ₀, N, ε, e, s, by omega, by omega, hθ, hb, hε, h₁, h₂, h₃⟩

end GlobalTheory.VData
end
end
