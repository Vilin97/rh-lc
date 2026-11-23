module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLEEqIffStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeyInputAtChartPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitCoefOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpen

theorem glue_units {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens) (P : Z.Opens → Prop)
    (hP : ∀ p ∈ V, ∃ W : Z.Opens, IsAffineOpen W ∧ W ≤ V ∧ P W ∧ p ∈ W)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → P W → ∃ a : Γ(Z, W)ˣ,
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a.val)) :
    ∃ a : Γ(Z, V)ˣ, ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a.val) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V ∧ P W}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2.1 i.2.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨W, hW, hWV, hPW, hpW⟩ := hP p hp
    exact ⟨⟨W, hW, hWV, hPW⟩, hpW⟩
  have hcov : V ≤ iSup fun i : I => i.1 := fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)
  have key : ∀ (i j : I) (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (i.1 ⊓ j.1)),
      ev z _ hz (resG Z inf_le_left (a i).val) = ev z _ hz (resG Z inf_le_right (a j).val) := by
    intro i j L _ z hz
    have hi := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
    have hj := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
    rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
    exact uniq L z (GlobalTheory.FlagMod.le_preimage_mono i.2.2.1 hi) _ _ (ha i L z hi) (ha j L z hj)
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i).val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i).val) (b := resG Z inf_le_right (a j).val)
        fun L _ z hz => key i j L z hz)
  obtain ⟨t, ht, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i)⁻¹.val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i)⁻¹.val) (b := resG Z inf_le_right (a j)⁻¹.val)
        fun L _ z hz => by
          have e := key i j L z hz
          have e₁ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_left)) : Γ(Z, i.1) →+* L) (a i)
          have e₂ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_right)) : Γ(Z, j.1) →+* L) (a j)
          simp only [RingHom.coe_comp, Function.comp_apply] at e₁ e₂
          rw [e₁, e₂, e])
  obtain ⟨s, t, hs, ht⟩ : ∃ s t : Γ(Z, V), (∀ i : I, resG Z i.2.2.1 s = (a i).val) ∧
      ∀ i : I, resG Z i.2.2.1 t = (a i)⁻¹.val := ⟨s, t, hs, ht⟩
  have hval : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ∃ i : I, ∃ hi : ⊤ ≤ z ⁻¹ᵁ i.1,
      ev z V hz s = ev z i.1 hi (a i).val ∧ ev z V hz t = ev z i.1 hi (a i)⁻¹.val := by
    intro L _ z hz
    obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
    have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
    exact ⟨i, hi', (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz s).symm.trans (congrArg _ (hs i)),
      (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz t).symm.trans (congrArg _ (ht i))⟩
  have hst : s * t = 1 := GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => by
    obtain ⟨i, hi, e₁, e₂⟩ := hval L z hz
    rw [map_mul, map_one, e₁, e₂, ← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, fun L _ z hz => ?_⟩
  obtain ⟨i, hi, e₁, -⟩ := hval L z hz
  show R L z (ev z V hz s)
  rw [e₁]
  exact ha i L z hi

end GlobalTheory.KeyOpen

namespace GlobalTheory.KeyOpen

end GlobalTheory.KeyOpen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitThetaKeyRuleOpenModelChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpenModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem charZero_of_range [IsOpenImmersion Y.j] {R : Type} [CommRing R] [Nontrivial R] (z : Sp R ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : CharZero R :=
  charZero_of_injective_ringHom (Spec.preimage (IsOpenImmersion.lift Y.j z h ≫ pullback.snd _ _)).hom.injective

theorem exists_keyAt_of_range [IsOpenImmersion Y.j] (hpq : 1 ≤ D.p + D.q) (M : GChart Y) {R : Type} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (h : Set.range z ⊆ Set.range Y.j) :
    ∃ x : KeyIn R, KeyAt M z hz x := by
  obtain ⟨t, ⟨m⟩⟩ := exists_sab z Y.t
  have e : IsOpenImmersion.lift Y.j z h ≫ Y.j = z := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t Y.j (IsOpenImmersion.lift Y.j z h) Y.m (e.symm ▸ m)
  have hp₀ := Y.oF.proper
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp₀
  have hA : Out.RelAmple t.G t.PP.L := by
    have h₁ := AmpleBaseChange.relAmple_of_isPullback Y.oF.t.PP.isLB Y.oF.ample m'.cart.1
    refine (GlobalTheory.KeyAtFam.relAmple_iff_of_cls (pull_isLB Y.oF.t.PP.isLB m'.φ) t.PP.isLB le_rfl ?_).2 h₁
    rw [one_smul]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m')
  have := charZero_of_range z h
  have : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h₂ := IsTotallyComplex.finrank E
    exact Nat.mul_pos (by omega) hpq
  obtain ⟨x₀, -, h₀⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (spMap (algebraMap R (FractionRing R)) ≫ z)
    (le_preimage_comp _ hz) (by
      rintro _ ⟨s, rfl⟩
      exact h ⟨_, rfl⟩) hpos
  obtain ⟨x, -, hx⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hz m hp hA _ h₀
  exact ⟨x, hx⟩

theorem exists_unit_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y hO hj hpq κ hκ M
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have : IsReduced Y.X := by
    have (x : Y.X) : _root_.IsReduced (Y.X.presheaf.stalk x) := by
      have := GlobalTheory.IsNormalScheme.isDomain_stalk x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  let W₀ : Y.X.Opens := M.U ⊓ Y.j.opensRange
  have hW₀ : ∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j := fun x => Iff.rfl
  have hr : ∀ {R : Type} [CommRing R] (z : Sp R ⟶ Y.X), ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := by
    rintro R _ z hz _ ⟨s, rfl⟩
    exact ((hW₀ _).1 (hz (Set.mem_univ s))).2
  let P : Y.X.Opens → Prop := fun W => IsDomain Γ(Y.X, W)
  have hP : ∀ q ∈ W₀, ∃ W : Y.X.Opens, IsAffineOpen W ∧ W ≤ W₀ ∧ P W ∧ q ∈ W := fun q hq => by
    obtain ⟨D', hqD, hD⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X q
    obtain ⟨_, ⟨W, hW, rfl⟩, hqW, hle⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show q ∈ ((W₀ ⊓ D' : Y.X.Opens) : Set Y.X) from ⟨hq, hqD⟩) (W₀ ⊓ D').isOpen
    exact ⟨W, hW, fun r hr => (hle hr).1, hD W hqW fun r hr => (hle hr).2, hqW⟩
  have loc₁ : ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (hWV : W ≤ W₀), P W →
      ∃ (y : KeyIn Γ(Y.X, W)) (u : Γ(Y.X, W)ˣ),
        KeyAt M (tau hW) (tau_le hW (hWV.trans inf_le_left)) y ∧ GlobalTheory.KeyCl.IsValue κ y (u : Γ(Y.X, W)) := by
    intro W hW hWV hdom
    have : IsDomain Γ(Y.X, W) := hdom
    have : IsNoetherianRing Γ(Y.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : IsIntegrallyClosed Γ(Y.X, W) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
    have : CharZero Γ(Y.X, W) := charZero_of_range (tau hW) (hr _ (tau_le hW hWV))
    obtain ⟨y, hy⟩ := exists_keyAt_of_range hpq M (tau hW) (tau_le hW (hWV.trans inf_le_left)) (hr _ (tau_le hW hWV))
    obtain ⟨u, hu⟩ := GlobalTheory.KeyFamUnit.famUnit κ hκ.2.1 hκ.2.2.1 Γ(Y.X, W) y
    exact ⟨y, u, hy, hu⟩
  obtain ⟨f, hf⟩ := GlobalTheory.KeyOpen.glue_units W₀ P hP
    (fun L _ z v => ∀ (hc : CharZero L) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn L), KeyAt M z hz' x → v = (κ L x : L))
    (fun L _ z hz v w hv hw => by
      have hc : CharZero L := charZero_of_range z (hr z hz)
      have hz' : ⊤ ≤ z ⁻¹ᵁ M.U := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      obtain ⟨x, hx⟩ := exists_keyAt_of_range hpq M z hz' (hr z hz)
      exact (hv hc _ x hx).trans (hw hc _ x hx).symm)
    (fun W hW hWV hPW => by
      obtain ⟨y, u, hy, hu⟩ := loc₁ W hW hWV hPW
      refine ⟨u, fun L _ z hz hc hz' x hx => ?_⟩
      have e : spMap (ev z W hz) ≫ tau hW = z := GlobalTheory.FlagMod.spMap_ev z hW hz
      generalize ev z W hz = φ at e ⊢
      subst e
      exact (hu L φ x (GlobalTheory.KeyAtBC.keyPB_of_keyAt hy hx)).symm)
  exact ⟨W₀, f, hW₀, fun K _ hK z hz hz' x hx => hf K z hz hK hz' x hx⟩

end GlobalTheory.KeyOpenModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitThetaKeyRuleOpenModelChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_unit_thetaKeyRule_open_model_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  first | exact @GlobalTheory.KeyOpenModel.exists_unit_open | exact GlobalTheory.KeyOpenModel.exists_unit_open | (intros; apply GlobalTheory.KeyOpenModel.exists_unit_open <;> assumption)
end
end
