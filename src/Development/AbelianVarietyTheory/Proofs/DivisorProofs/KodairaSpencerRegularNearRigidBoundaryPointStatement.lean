module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibre
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenInteriorContainingToricChartGenerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerOfLogDerivationChartStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonGenericFibreOfMaximalAffineOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfLeAffineOpenToroidalModelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPoint
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartRingMapFlatAndComapMaximalIdealStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibreStatement

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

theorem _root_.GlobalTheory.T.charZero_of_toricChart_to_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y), CharZero k := by
  first | exact @GlobalTheory.LocReg.charZero_of_chart | exact GlobalTheory.LocReg.charZero_of_chart | (intros; apply GlobalTheory.LocReg.charZero_of_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpenStatement

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

theorem _root_.GlobalTheory.T.exists_tangentBasis_pullback_to_spec_of_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t0 : SAB H X) (U : X.affineOpens) (R : Type) [CommRing R] (ρ : Γ(X, U.1) →+* R) (t : SAB H (Sp R)) (f : Sp R ⟶ X), f = spMap ρ ≫ chart U → ∀ (φ : SABMap t t0 f) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t0.G.left)), (∀ i, IsTanAtG t0 (chart U) (v i)) → (∀ w, IsTanAtG t0 (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t0 (chart U) v cf w) → ∃ vR : Fin n → (Sp (DualNumber Γ(Sp R, ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (vR i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) w → ∃! cf : Fin n → Γ(Sp R, ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) vR cf w) ∧ ∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ)) ≫ v i := by
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
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPointStatement

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

theorem _root_.GlobalTheory.T.kodairaSpencer_chart_eq_at_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (k : Type) [Field k] [CharZero k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) (t : SAB H (Sp (ChartRing k m d))) (φ : SABMap t Y.t (ξ ≫ genι Y)), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ vR : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (vR i)) → (∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx))) ≫ v i) → ∀ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (GlobalTheory.LocReg.chartHom Y U ξ hx r) = GlobalTheory.LocReg.chartHom Y U ξ hx (D.1 r)) → ∀ ΘR : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) vR (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) ΘR → ∀ (h : Γ(Y.X, U.1)) (hh : Y.X.basicOpen h ≤ W.1), GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 → ∀ (a b : Fin n) (s : Γ(Y.X, U.1)) (N : ℕ), (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N) * (Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b) → GlobalTheory.LocReg.chartHom Y U ξ hx s = GlobalTheory.LocReg.chartHom Y U ξ hx h ^ N * (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b) := by
  first | exact @GlobalTheory.LocRegCmp.ks_chart_eq | exact GlobalTheory.LocRegCmp.ks_chart_eq | (intros; apply GlobalTheory.LocRegCmp.ks_chart_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRingStatement

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

theorem _root_.GlobalTheory.T.logDerivation_extends_completed_toricChart_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} → ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) r) = ((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) (D.1 r)) ∧ ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  first | exact @GlobalTheory.ChartDer.logDer_extend_chartRing | exact GlobalTheory.ChartDer.logDer_extend_chartRing | (intros; apply GlobalTheory.ChartDer.logDer_extend_chartRing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundaryStatement

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

theorem _root_.GlobalTheory.T.mem_abelianLocus_toricChart_iff_not_mem_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m d))), SABMap t Y.t (ξ ≫ genι Y) → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal := by
  first | exact @GlobalTheory.ChartAbLocus.mem_abLocus_iff | exact GlobalTheory.ChartAbLocus.mem_abLocus_iff | (intros; apply GlobalTheory.ChartAbLocus.mem_abLocus_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMaStatement

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

theorem _root_.GlobalTheory.T.toricChart_comp_genericFibreInclusion_eq_spec_chartMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  first | exact @GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom | exact GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom | (intros; apply GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRegularNearRigidBoundaryPoint

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

noncomputable section

namespace GlobalTheory.LocRegRig

theorem isKS_regular_at_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ Y.X.basicOpen f) ∧ x ∉ interior Y) → ∃ g ∉ m, ∀ a b, ∃ s : Γ(Y.X, U.1), (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * Θ a b := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hchart U W hW n v hv hbasis D DW Θ hDW hKS m hm hx0
  obtain ⟨x, hxU, hxm, hxint⟩ := hx0
  haveI := isIso_fst Y
  obtain ⟨x', rfl⟩ := (genι Y).surjective x
  have hbd : x' ∈ genBd Y := mem_genBd_iff.2 fun h => hxint (by
    rw [← SetLike.mem_coe, coe_interior]; exact h)
  have hcl : IsClosed ({x'} : Set (gen Y)) := GlobalTheory.T.isClosed_singleton_genericFibre_of_maximal_affineOpen E H Dw l Xo c Y U m hm x' hxU hxm
  obtain ⟨k, _, m', d, ξ, t, P, gam, h₀, h₁, h₂, h₃, ⟨φ⟩, h₅, h₆, -⟩ := hchart x' hbd hcl
  subst h₀
  have hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := hxU
  haveI : CharZero k := GlobalTheory.T.charZero_of_toricChart_to_genericFibre E H Dw l Xo c Y k m' d ξ
  obtain ⟨D', hD', hDlog⟩ := GlobalTheory.T.logDerivation_extends_completed_toricChart_ring E H Dw l Xo c Y U D k m' d ξ hx h₁ h₂
  have hfac := GlobalTheory.T.toricChart_comp_genericFibreInclusion_eq_spec_chartMap E H Dw l Xo c Y U k m' d ξ hx
  obtain ⟨vR, hvR, hbR, hcomp⟩ := GlobalTheory.T.exists_tangentBasis_pullback_to_spec_of_affineOpen E H Y.X Y.t U _ (GlobalTheory.LocReg.chartHom Y U ξ hx) t _ hfac φ n v hv hbasis
  have hab := GlobalTheory.T.mem_abelianLocus_toricChart_iff_not_mem_boundary E H Dw l Xo c Y k m' d ξ t φ h₃
  have hlin : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    h₆.linearIndependent.map' (Submodule.subtype _) (by simp)
  obtain ⟨ΘR, hΘR⟩ := GlobalTheory.T.exists_kodairaSpencer_of_logDerivation_chart E H k m' d t P (fun i => gam i) h₅ hlin hab n vR hvR hbR D' hDlog
  obtain ⟨h, hhW, hh0⟩ := GlobalTheory.T.exists_basicOpen_interior_containing_toricChart_generic E H Dw l Xo c Y U W hW k m' d ξ hx h₃
  obtain ⟨hflat, hcomap⟩ := GlobalTheory.T.toricChart_ringMap_flat_and_comap_maximalIdeal E H Dw l Xo c Y U k m' d ξ hx h₁ m hm hxm
  have hWc := GlobalTheory.T.isCompact_of_le_affineOpen_toroidalModel E H Dw l Xo c Y U W.1 (hW.le.trans inf_le_left)
  obtain ⟨g, hg, hs⟩ := GlobalTheory.T.sections_descend_along_flat_map_to_localDomain Y.X U W.1 (hW.le.trans inf_le_left) hWc _ (GlobalTheory.LocReg.chartHom Y U ξ hx) hflat m hcomap
    h hhW hh0 (Fin n × Fin n) (fun p => Θ p.1 p.2) (fun p s N e => Dvd.intro _
      (GlobalTheory.T.kodairaSpencer_chart_eq_at_generic_point E H Dw l Xo c Y hpq hsm U W hW n v hv hbasis D DW Θ hDW hKS k m' d ξ hx t φ h₁ h₃ vR hvR hcomp D' hD' ΘR hΘR
        h hhW hh0 p.1 p.2 s N e).symm)
  exact ⟨g, hg, fun a b => hs (a, b)⟩

end GlobalTheory.LocRegRig
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRegularNearRigidBoundaryPointStatement

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

theorem _root_.GlobalTheory.T.kodairaSpencer_regular_near_rigid_boundary_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ Y.X.basicOpen f) ∧ x ∉ interior Y) → ∃ g ∉ m, ∀ a b, ∃ s : Γ(Y.X, U.1), (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * Θ a b := by
  first | exact @GlobalTheory.LocRegRig.isKS_regular_at_boundary | exact GlobalTheory.LocRegRig.isKS_regular_at_boundary | (intros; apply GlobalTheory.LocRegRig.isKS_regular_at_boundary <;> assumption)
end
end
