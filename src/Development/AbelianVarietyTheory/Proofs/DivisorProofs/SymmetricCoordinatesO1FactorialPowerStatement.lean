module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatio
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingElementarySymmetricUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatioStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.homogeneousCoords_in_standardChart_ratio : ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (a : Fin (n + 1)), PCrd x v → ⊤ ≤ x ⁻¹ᵁ ProjSpace.chart o n a → v a ≠ 0 ∧ ∀ b, valR x (ProjSpace.chart o n a) (ProjSpace.ratio o n a b) = v b / v a := by
  first | exact @GlobalTheory.UMin.CrdChart.pCrd_chart | exact GlobalTheory.UMin.CrdChart.pCrd_chart | (intros; apply GlobalTheory.UMin.CrdChart.pCrd_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDivPowFactorialIsUnit

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (A : Subalgebra k Ω) [IsLocalRing A] (N : ℕ) (c : Fin N → Ω) (a j : Fin N), c a ≠ 0 → (∀ b, c b / c a ∈ A) → symTup c j ≠ 0 → (∀ b, symTup c b / symTup c j ∈ A) → symTup c j / c a ^ N.factorial ≠ 0 ∧ symTup c j / c a ^ N.factorial ∈ A ∧ (symTup c j / c a ^ N.factorial)⁻¹ ∈ A := by
  intro k Ω _ _ _ A _ N c a j hca hcb hj hjb
  have hpow : c a ^ N.factorial ≠ 0 := pow_ne_zero _ hca
  let d : Fin N → A := fun b => ⟨c b / c a, hcb b⟩
  have hd : ∀ j' : Fin N, symTup c j' / c a ^ N.factorial = ((symTup d j' : A) : Ω) := by
    intro j'
    have h1 : c = fun b => c a * ((d b : A) : Ω) := by
      funext b; show c b = c a * (c b / c a); field_simp
    have h2 := (GlobalTheory.UMin.symTup_basic).1 Ω N (fun b => ((d b : A) : Ω)) (c a) j'
    have h3 := (GlobalTheory.UMin.symTup_basic).2.2.1 A Ω A.val.toRingHom N d j'
    have h4 : symTup c j' = c a ^ N.factorial * symTup (fun b => ((d b : A) : Ω)) j' := by
      rw [← h2, ← h1]
    rw [h4, mul_div_cancel_left₀ _ hpow]
    exact h3.symm
  have hda : d a = 1 := Subtype.ext (by show c a / c a = 1; exact div_self hca)
  obtain ⟨k0, hk1, hk2, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one A (Fin N) d a hda
  rw [Fintype.card_fin] at hk2
  let j' : Fin N := ⟨k0 - 1, by omega⟩
  have hk0 : (j' : ℕ) + 1 = k0 := by show k0 - 1 + 1 = k0; omega
  have hu : IsUnit (symTup d j') := by
    unfold symTup; rw [hk0]; exact hku.pow _
  let x : A := ⟨symTup c j / c a ^ N.factorial, by rw [hd j]; exact (symTup d j).2⟩
  let z : A := ⟨symTup c j' / symTup c j, hjb j'⟩
  have hxz : symTup d j' = x * z := by
    apply Subtype.ext
    show ((symTup d j' : A) : Ω) = (symTup c j / c a ^ N.factorial) * (symTup c j' / symTup c j)
    rw [← hd j']
    field_simp
  rw [hxz] at hu
  have hx : IsUnit x := isUnit_of_mul_isUnit_left hu
  refine ⟨div_ne_zero hj hpow, x.2, ?_⟩
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  have hv' : (symTup c j / c a ^ N.factorial) * (v : Ω) = 1 := by
    have := congrArg (fun t : A => (t : Ω)) hv
    simpa using this
  rw [← eq_inv_of_mul_eq_one_right hv']
  exact v.2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDivPowFactorialIsUnitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.thetaSymmetricFunctions_div_pow_factorial_isUnit : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (A : Subalgebra k Ω) [IsLocalRing A] (N : ℕ) (c : Fin N → Ω) (a j : Fin N), c a ≠ 0 → (∀ b, c b / c a ∈ A) → symTup c j ≠ 0 → (∀ b, symTup c b / symTup c j ∈ A) → symTup c j / c a ^ N.factorial ≠ 0 ∧ symTup c j / c a ^ N.factorial ∈ A ∧ (symTup c j / c a ^ N.factorial)⁻¹ ∈ A := by
  first | exact @GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd | exact GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd | (intros; apply GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCoordinatesO1FactorialPower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdSym

open GlobalTheory.Points GlobalTheory.ProjSpace

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω]

theorem div_mem_O {o : Type} [CommRing o] {M : RatModel k Ω} {n : ℕ} {h : M.Z ⟶ PSpace o n}
    {c : Fin (n + 1) → Ω} (hc : PCrd (M.pt ≫ h) c) {a : Fin (n + 1)} {z : M.Z}
    (hz : z ∈ h ⁻¹ᵁ ProjSpace.chart o n a) : c a ≠ 0 ∧ ∀ b, c b / c a ∈ M.O z := by
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ (h ⁻¹ᵁ ProjSpace.chart o n a) := M.top_le_preimage_pt ⟨z, hz⟩
  obtain ⟨h0, hv⟩ := GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o Ω n (M.pt ≫ h) c a hc (le_preimage_comp M.pt h le_rfl hW)
  refine ⟨h0, fun b => ?_⟩
  have e : valF M.pt (h ⁻¹ᵁ ProjSpace.chart o n a) (ProjSpace.pullRatio h _ a le_rfl b) = c b / c a :=
    (Points.valR_appLE M.pt h le_rfl hW _).trans (hv b)
  exact e ▸ M.valF_mem_O hz _

theorem valR_pullO1_g {L : Type} [Field L] {X : Scheme.{0}} {o : Type} [CommRing o] {r : ℕ} (y0 : Sp L ⟶ X)
    (π : X ⟶ PSpace o r) {t : Fin (r + 1) → L} (ht : PCrd (y0 ≫ π) t) (i j : PUnit → Fin (r + 1))
    (h : ⊤ ≤ y0 ⁻¹ᵁ (((ProjSpace.O1 o r).pull π).U i ⊓ ((ProjSpace.O1 o r).pull π).U j)) :
    valR y0 _ (((ProjSpace.O1 o r).pull π).g i j).val = t (j PUnit.unit) / t (i PUnit.unit) := by
  have h1 : ⊤ ≤ (y0 ≫ π) ⁻¹ᵁ (ProjSpace.chart o r (i PUnit.unit) ⊓ ProjSpace.chart o r (j PUnit.unit)) :=
    le_preimage_comp y0 π (inf_le_inf (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) i PUnit.unit)
      (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) j PUnit.unit)) h
  refine (TuplePoint.valR_linComb_g y0 (ProjSpace.O1 o r) π 1 i j h).trans ((zpow_one _).trans ?_)
  refine (valR_res (y0 ≫ π) inf_le_left h1 (ProjSpace.ratio o r (i PUnit.unit) (j PUnit.unit))).trans ?_
  exact (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o L r (y0 ≫ π) t _ ht (le_preimage_mono _ inf_le_left h1)).2 _


open Classical in
def unitOf (M : RatModel k Ω) (U : M.Z.Opens) (x : Ω) (hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z) :
    Γ(M.Z, U)ˣ :=
  if hU : (U : Set M.Z).Nonempty then
    Units.map (M.sectionsEquiv U hU).symm.toMonoidHom
      ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩, ⟨x⁻¹, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.2⟩,
        Subtype.ext (mul_inv_cancel₀ (hx _ hU.some_mem).1), Subtype.ext (inv_mul_cancel₀ (hx _ hU.some_mem).1)⟩
  else 1

theorem valR_unitOf {M : RatModel k Ω} {U : M.Z.Opens} {x : Ω} {hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z}
    (h : ⊤ ≤ M.pt ⁻¹ᵁ U) : valR M.pt U (unitOf M U x hx).val = x := by
  have hU : (U : Set M.Z).Nonempty := ⟨_, h (x := IsLocalRing.closedPoint Ω) trivial⟩
  rw [unitOf, dite_eq_left hU]
  have := M.coe_sectionsEquiv U hU ((M.sectionsEquiv U hU).symm ⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UMin.CrdSym
end

namespace GlobalTheory.UMin.CrdSym
open GlobalTheory.Points GlobalTheory.ProjSpace

theorem lbIso_symTup : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  intro k Ω o _ _ _ _ M n h g c hc he
  set D := (n + 1).factorial
  set L := (ProjSpace.O1 o n).pull g
  set L' := lbPow ((ProjSpace.O1 k n).pull h) D
  have h2 : ∀ a : L'.ι, L'.U a ≤ ((ProjSpace.O1 k n).pull h).U (a PUnit.unit) := fun a =>
    LB.wchart_le ((ProjSpace.O1 k n).pull h) (fun _ => 𝟙 M.Z) a PUnit.unit
  have hL' : ∀ a : L'.ι, L'.U a ≤ h ⁻¹ᵁ ProjSpace.chart k n (a PUnit.unit PUnit.unit) := fun a =>
    (h2 a).trans (LB.wchart_le (ProjSpace.O1 k n) (fun _ => h) _ PUnit.unit)
  have hL : ∀ j : L.ι, L.U j ≤ g ⁻¹ᵁ ProjSpace.chart o n (j PUnit.unit) := fun j =>
    LB.wchart_le (ProjSpace.O1 o n) (fun _ => g) j PUnit.unit
  let x : L'.ι × L.ι → Ω := fun p => symTup c (p.2 PUnit.unit) / c (p.1 PUnit.unit PUnit.unit) ^ D
  have hx : ∀ p : L'.ι × L.ι, ∀ z ∈ (LB.div L' L).U p, x p ≠ 0 ∧ x p ∈ M.O z ∧ (x p)⁻¹ ∈ M.O z := by
    rintro ⟨a, j⟩ z ⟨hza, hzj⟩
    obtain ⟨h1, h3⟩ := div_mem_O hc (hL' a hza)
    obtain ⟨h4, h5⟩ := div_mem_O he (hL j hzj)
    exact GlobalTheory.T.thetaSymmetricFunctions_div_pow_factorial_isUnit k Ω (M.O z) (n + 1) c _ _ h1 h3 h4 h5
  have nzh : ∀ a : L'.ι, ⊤ ≤ M.pt ⁻¹ᵁ L'.U a → c (a PUnit.unit PUnit.unit) ≠ 0 := fun a ha =>
    (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio k Ω n (M.pt ≫ h) c _ hc (le_preimage_comp M.pt h (hL' a) ha)).1
  have nzg : ∀ j : L.ι, ⊤ ≤ M.pt ⁻¹ᵁ L.U j → symTup c (j PUnit.unit) ≠ 0 := fun j hj =>
    (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o Ω n (M.pt ≫ g) (symTup c) _ he (le_preimage_comp M.pt g (hL j) hj)).1
  let w : LB.Iso L L' := ⟨fun p => unitOf M ((LB.div L' L).U p) (x p) (hx p)⟩
  refine ⟨w, ?_⟩
  rintro ⟨a, j⟩ ⟨a', j'⟩
  refine Units.ext (TuplePoint.ext_of_dense M.pt fun hW => ?_)
  have ha := le_preimage_mono M.pt inf_le_left hW
  have hb := le_preimage_mono M.pt inf_le_right hW
  have hk : ⊤ ≤ M.pt ⁻¹ᵁ (L'.U a ⊓ L'.U a') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) hW
  have hj : ⊤ ≤ M.pt ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hW
  have e1 := TuplePoint.valR_linComb_g M.pt ((ProjSpace.O1 k n).pull h) (𝟙 M.Z) D a a' hk
  rw [Category.comp_id, valR_pullO1_g M.pt h hc _ _ (le_preimage_mono M.pt (inf_le_inf (h2 a) (h2 a')) hk),
    zpow_natCast] at e1
  have e2 := valR_pullO1_g M.pt g he j j' hj
  have n1 := nzh a (le_preimage_mono M.pt inf_le_left ha)
  have n2 := nzh a' (le_preimage_mono M.pt inf_le_left hb)
  have n3 := nzg j (le_preimage_mono M.pt inf_le_right ha)
  have n4 := nzg j' (le_preimage_mono M.pt inf_le_right hb)
  refine (TuplePoint.valR_res_unit M.pt _ hW _).trans ((valR_unitOf (hx := hx (a, j)) ha).trans (Eq.symm ?_))
  refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
  have eg : valR M.pt _ ((LB.div L' L).g (a, j) (a', j')).val =
      (c (a' PUnit.unit PUnit.unit) / c (a PUnit.unit PUnit.unit)) ^ D *
        (symTup c (j' PUnit.unit) / symTup c (j PUnit.unit))⁻¹ := by
    refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
    exact congrArg₂ (· * ·) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e1)
      ((TuplePoint.valR_inv_unit M.pt hW _).trans (congrArg (·⁻¹) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e2)))
  rw [eg, TuplePoint.valR_res_unit M.pt _ hW, valR_unitOf (hx := hx (a', j')) hb]
  simp only [x]
  rw [div_pow]
  field_simp

end GlobalTheory.UMin.CrdSym
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCoordinatesO1FactorialPowerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetric_coordinates_O1_factorial_power : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  exact GlobalTheory.UMin.CrdSym.lbIso_symTup
end
end
