module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerPullbackSemiAbelianMap
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecAppLETopEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstAlongOfKodairaSpencerZeroChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageOfClosedPoint

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerPullbackSemiAbelianMapStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechKodairaSpencer_pullback_semiAbelianMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (g : X' ⟶ X) (mu : SABMap t' t g) (V : X.Opens) (V' : X'.Opens) (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1), U'.1 ⊓ V' ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ i, IsTanAtG t' (chart U') (v' i)) → (∀ i, v' i ≫ mu.φ = spMap (dualMap (g.appLE U.1 U'.1 hU).hom) ≫ v i) → ∀ (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ Θ : Matrix (Fin n) (Fin n) Γ(X, U.1), IsKS t V U v D Θ → IsKS t' V' U' v' D' ((g.appLE U.1 U'.1 hU).hom.mapMatrix Θ) := by
  first | exact @GlobalTheory.KSBaseChange.isKS_pull | exact GlobalTheory.KSBaseChange.isKS_pull | (intros; apply GlobalTheory.KSBaseChange.isKS_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpen

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg.BasisPull

theorem exists_basis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t0 : SAB H X) (U : X.affineOpens) (R : Type) [CommRing R] (ρ : Γ(X, U.1) →+* R) (t : SAB H (Sp R)) (f : Sp R ⟶ X), f = spMap ρ ≫ chart U → ∀ (φ : SABMap t t0 f) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t0.G.left)), (∀ i, IsTanAtG t0 (chart U) (v i)) → (∀ w, IsTanAtG t0 (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t0 (chart U) v cf w) → ∃ vR : Fin n → (Sp (DualNumber Γ(Sp R, ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (vR i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) w → ∃! cf : Fin n → Γ(Sp R, ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) vR cf w) ∧ ∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ)) ≫ v i := by
  intro E _ _ _ H X t0 U R _ ρ t f hf φ n v hv hb
  let ψ : Γ(X, U.1) →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ
  have hx : spMap ψ ≫ chart U = chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) ≫ f := by
    rw [hf, ← Category.assoc]
    congr 1
    rw [chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hv' := fun i => GlobalTheory.LieMet.isTan_map ψ hx (hv i)
  have hb' := GlobalTheory.GradedPieces.basis_map ψ hx hv hb
  choose vR hvR1 hvR2 using fun i => GlobalTheory.ShFam.OpenReg.exists_lift φ
    (spMap (algebraMap Γ(Sp R, ⊤) (DualNumber Γ(Sp R, ⊤))) ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    (spMap (dualMap ψ) ≫ v i) (by rw [(hv' i).1, Category.assoc])
  refine ⟨vR, fun i => (GlobalTheory.ShFam.OpenReg.tan_iff φ rfl (hvR1 i)).1 (by rw [hvR2]; exact hv' i), fun w hw => ?_, hvR2⟩
  have e : (fun i => spMap (dualMap ψ) ≫ v i) = fun i => vR i ≫ φ.φ := funext fun i => (hvR2 i).symm
  have h := hb' (w ≫ φ.φ) ((GlobalTheory.ShFam.OpenReg.tan_iff φ rfl hw.1).2 hw)
  rw [e] at h
  exact (existsUnique_congr fun cf => GlobalTheory.ShFam.OpenReg.comb_iff φ rfl hvR1 cf hw.1).1 h

end GlobalTheory.LocReg.BasisPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstAlongOfKodairaSpencerZeroChartStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isConstAlong_of_kodairaSpencer_zero_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  first | exact @GlobalTheory.KSConst.isConstAlong_of_ks_zero | exact GlobalTheory.KSConst.isConstAlong_of_ks_zero | (intros; apply GlobalTheory.KSConst.isConstAlong_of_ks_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationConstantOfLogKodairaSpencerMem

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartConst

theorem exists_derivation_top {R : Type} [CommRing R] [Algebra ℤ R] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤), ⇑D' = fun r =>
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)) := by
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply r
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' := fun x y => by rw [map_add (f := _), map_add (f := _), map_add (f := _)] }) fun a b => ?_, rfl⟩
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (a * b))) =
    a • (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)) +
      b • (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a))
  rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, e, e, smul_eq_mul, smul_eq_mul]

theorem valR_mem_maximalIdeal {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (g : Sp R ⟶ X) (U : X.Opens)
    (hU : ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) (hf : g (closedPoint R) ∉ X.basicOpen f) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U ⊤ hU).hom f) ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply r
  rw [e] at h1
  have h2 := (Sp R).basicOpen_of_isUnit h1
  have h3 := Scheme.basicOpen_appLE g ⊤ U hU f
  have h4 : closedPoint R ∈ (⊤ : (Sp R).Opens) ⊓ g ⁻¹ᵁ X.basicOpen f := by
    rw [← h3]
    exact h2.ge trivial
  exact hf h4.2

theorem isConstAlong_of_ks_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → ∀ (t : SAB H (Sp (ChartRing k m' d))) (P : PELUnif (maximalIdeal (ChartRing k m' d)) t) (gam : Fin m' → levelForms H l.M' P.D.toPre.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → Nonempty (SABMap t Y.t (ξ ≫ genι Y)) → IsMonomial P.D.toPre (bdParam k m' d) (fun i => gam i) → IsPartOfBasis gam → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → ∀ ρ : ChartRing k m' d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (DR r))) → ∃ c₀ : ℚ, c₀ ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m' d) (fun i => gam i) ρ (fun i => (c₀ : k) * MvPowerSeries.constantCoeff (a i)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc U n v A hv hb hA D Θ m hm x hxi hxU hxm hKS hΘ k _ m' d ξ x' hξ hx'x t P gam
    hEt hId hBd ⟨φ⟩ hMon hPart hU DR a hDR ha ρ hρ
  subst hξ hx'x
  have hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := hxU
  have : CharZero k := GlobalTheory.LocReg.charZero_of_chart E H Dw l Xo c Y k m' d ξ
  have hfac := GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom E H Dw l Xo c Y U k m' d ξ hx
  obtain ⟨vR, hvR, hbR, hcomp⟩ := GlobalTheory.LocReg.BasisPull.exists_basis_pull E H Y.X Y.t U _ (GlobalTheory.LocReg.chartHom Y U ξ hx) t _ hfac φ n v hv hb
  have hab := GlobalTheory.ChartAbLocus.mem_abLocus_iff E H Dw l Xo c Y k m' d ξ t φ hBd
  have hlin : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    hPart.linearIndependent.map' (Submodule.subtype _) (by simp)
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom_inv_id_apply r
  have hval : ∀ r, valR (ξ ≫ genι Y) U.1 r = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom
      (((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom r) := fun r => dif_pos hU
  have hch : ∀ r, valR (ξ ≫ genι Y) U.1 r = GlobalTheory.LocReg.chartHom Y U ξ hx r := fun r => by
    have h := GlobalTheory.CechKSSmul.valR_spMap_chart U (GlobalTheory.LocReg.chartHom Y U ξ hx) r
    rwa [← hfac] at h
  have happ : (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx) =
      ((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom := RingHom.ext fun r => by
    rw [RingHom.comp_apply, ← hch, hval, e]
  obtain ⟨D', hD'⟩ := exists_derivation_top DR
  have hV : (⊤ : (Sp (ChartRing k m' d)).Opens) ⊓ (Sp (ChartRing k m' d)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (∏ i, bdParam k m' d i)) ≤
      (ξ ≫ genι Y) ⁻¹ᵁ interior Y := by
    intro p hp
    have h1 : p ∈ (Sp (ChartRing k m' d)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (∏ i, bdParam k m' d i)) := hp.2
    have h2 := basicOpen_eq_of_affine (R := CommRingCat.of (ChartRing k m' d)) (∏ i, bdParam k m' d i)
    have h3 : p ∈ PrimeSpectrum.basicOpen (∏ i, bdParam k m' d i) := h2.le h1
    have h4 : ξ p ∉ genBd Y := fun h => h3 ((hBd p).1 h)
    rw [mem_genBd_iff, not_not, ← coe_interior] at h4
    exact h4
  have hK := GlobalTheory.T.cechKodairaSpencer_pullback_semiAbelianMap E H Y.X (Sp (ChartRing k m' d)) Y.t t (ξ ≫ genι Y) φ (interior Y) _ U
    (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m' d)).affineOpens) hU hV n v vR hv hvR
    (fun i => by rw [hcomp i, happ]) D.1 D' (fun r => by
      rw [hD']
      show (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (DR
        ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom (((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom r))) =
        ((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom (D.1 r)
      rw [← hval, hDR, hval, e]) Θ hKS
  rw [hD'] at hK
  exact GlobalTheory.T.isConstAlong_of_kodairaSpencer_zero_chart E H k m' d t P (fun i => gam i) hMon hlin hab n vR hvR hbR DR a ha _ hK
    (fun a b => valR_mem_maximalIdeal (ξ ≫ genι Y) U.1 hU (Θ a b) (hxm _ (hΘ a b))) ρ hρ

end GlobalTheory.ChartConst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationConstantOfLogKodairaSpencerMemStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

theorem _root_.GlobalTheory.T.degeneration_constant_of_logKodairaSpencer_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → ∀ (t : SAB H (Sp (ChartRing k m' d))) (P : PELUnif (maximalIdeal (ChartRing k m' d)) t) (gam : Fin m' → levelForms H l.M' P.D.toPre.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → Nonempty (SABMap t Y.t (ξ ≫ genι Y)) → IsMonomial P.D.toPre (bdParam k m' d) (fun i => gam i) → IsPartOfBasis gam → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → ∀ ρ : ChartRing k m' d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (DR r))) → ∃ c₀ : ℚ, c₀ ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m' d) (fun i => gam i) ρ (fun i => (c₀ : k) * MvPowerSeries.constantCoeff (a i)) := by
  first | exact @GlobalTheory.ChartConst.isConstAlong_of_ks_mem | exact GlobalTheory.ChartConst.isConstAlong_of_ks_mem | (intros; apply GlobalTheory.ChartConst.isConstAlong_of_ks_mem <;> assumption)
end
end
