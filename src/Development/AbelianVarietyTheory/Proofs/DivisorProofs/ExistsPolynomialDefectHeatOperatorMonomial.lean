module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHomInvariantFieldKillsWeightZeroStatement
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermValuesEqOfLocalIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorsDifferenceGlobalStatement
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateHeatOperatorPeriodShiftStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjUnitPowCorrections

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

namespace GlobalTheory.HeatConj

section Ring

variable {A : Type} [CommRing A] (δ : A → A)
  (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = x * δ y + y * δ x)
include hadd hmul

theorem der_natCast (k : ℕ) : δ (k : A) = 0 := by
  have h0 : δ 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    linear_combination -this
  have h1 : δ 1 = 0 := by
    have := hmul 1 1
    rw [_root_.one_mul] at this
    linear_combination -this
  induction k with
  | zero => simpa using h0
  | succ k ih => rw [Nat.cast_succ, hadd, ih, h1, add_zero]

theorem der_pow (g g' : A) (hg : g * g' = 1) (k : ℕ) : δ (g ^ k) = (k : A) * g ^ k * (δ g * g') := by
  induction k with
  | zero =>
    have := hmul 1 1
    rw [_root_.one_mul] at this
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -this
  | succ k ih =>
    rw [pow_succ, hmul, ih]
    push_cast
    linear_combination -(δ g * g ^ k) * hg

theorem der_pow_mul (g g' : A) (hg : g * g' = 1) (k : ℕ) (f : A) :
    δ (g ^ k * f) = g ^ k * (δ f + (k : A) * (δ g * g') * f) := by
  rw [hmul, der_pow δ hadd hmul g g' hg]
  ring

theorem der_natCast_mul (k : ℕ) (x : A) : δ ((k : A) * x) = (k : A) * δ x := by
  rw [hmul, der_natCast δ hadd hmul]
  ring

end Ring

end GlobalTheory.HeatConj

namespace GlobalTheory.HeatConj

theorem op_pow_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (dd : Fin n → Fld G.left) (Θ : Matrix (Fin n) (Fin n) R), Θᵀ = Θ → ∀ (u : Fin n → R) (d : Fld G.left) (W₀ Wp Wo : G.left.Opens) (p p' : Γ(G.left, Wp)) (k : ℕ) (g g' : Γ(G.left, Wo)), g * g' = 1 → Wo ≤ W₀ → IsField W₀ d → (∀ a, IsField W₀ (dd a)) → ∀ f, op G dd Θ u d p p' k Wo (g ^ k * f) = g ^ k * (op G dd Θ u d p p' k Wo f - 2 * (k : Γ(G.left, Wo)) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) ^ 2 * (2 * (d Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) + (k : Γ(G.left, Wo)) * (2 * ∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g'))) * f) := by
  intro R _ G _ _ n dd Θ hΘ u d W₀ Wp Wo p p' k g g' hg hWo hd hdd f
  have E3 := der_pow_mul (d Wo) (hd.1 Wo hWo) (hd.2.1 Wo hWo) g g' hg k f
  have E2 : ∀ a, dd a Wo (g ^ k * f) = g ^ k * (dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * f) :=
    fun a => der_pow_mul (dd a Wo) ((hdd a).1 Wo hWo) ((hdd a).2.1 Wo hWo) g g' hg k f
  have E1 : ∀ a b, dd a Wo (dd b Wo (g ^ k * f)) = g ^ k * (dd a Wo (dd b Wo f) +
      (k : Γ(G.left, Wo)) * (dd b Wo g * g') * dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * dd b Wo f +
      (k : Γ(G.left, Wo)) * dd a Wo (dd b Wo g * g') * f +
      (k : Γ(G.left, Wo)) ^ 2 * (dd a Wo g * g') * (dd b Wo g * g') * f) := by
    intro a b
    have ha := (hdd a).1 Wo hWo
    have hm := (hdd a).2.1 Wo hWo
    rw [E2 b, der_pow_mul (dd a Wo) ha hm g g' hg k, ha, mul_assoc (k : Γ(G.left, Wo)),
      der_natCast_mul (dd a Wo) ha hm, hm]
    ring
  have hsym : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f =
      ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : Θ b a = Θ a b := by
      have := congrFun (congrFun hΘ a) b
      simpa [Matrix.transpose_apply] using this
    rw [this]
  have hS : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo (g ^ k * f)) =
      g ^ k * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo f) +
      ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g')) * f +
      ((k : Γ(G.left, Wo)) ^ 2 * g ^ k) *
        (∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) * f := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [E1]
    ring
  have hU : ∑ a, constFn G.hom Wo (u a) * dd a Wo (g ^ k * f) =
      g ^ k * ∑ a, constFn G.hom Wo (u a) * dd a Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g')) * f := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [E2]
    ring
  unfold op
  rw [E3]
  linear_combination -hS + 2 * hU - ((k : Γ(G.left, Wo)) * g ^ k) * hsym

end GlobalTheory.HeatConj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjUnitPowCorrectionsStatement

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

theorem _root_.GlobalTheory.T.heatOperator_conj_unitPow_corrections : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (dd : Fin n → Fld G.left) (Θ : Matrix (Fin n) (Fin n) R), Θᵀ = Θ → ∀ (u : Fin n → R) (d : Fld G.left) (W₀ Wp Wo : G.left.Opens) (p p' : Γ(G.left, Wp)) (k : ℕ) (g g' : Γ(G.left, Wo)), g * g' = 1 → Wo ≤ W₀ → IsField W₀ d → (∀ a, IsField W₀ (dd a)) → ∀ f, op G dd Θ u d p p' k Wo (g ^ k * f) = g ^ k * (op G dd Θ u d p p' k Wo f - 2 * (k : Γ(G.left, Wo)) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) ^ 2 * (2 * (d Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) + (k : Γ(G.left, Wo)) * (2 * ∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g'))) * f) := by
  first | exact @GlobalTheory.HeatConj.op_pow_mul | exact GlobalTheory.HeatConj.op_pow_mul | (intros; apply GlobalTheory.HeatConj.op_pow_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineScalarTorusInvariantHeatOperators

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

namespace GlobalTheory.HeatUniq

theorem exists_affine_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (ℓ : Q.X →+ R) (π π' : R), ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π')) * sval σ x.left z J := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hdd D h' h hb' hb hΘ' hu'
  have hΘ : h.Θ = h'.Θ := hΘ'.symm
  have hu : h.u = h'.u := hu'.symm
  obtain ⟨e, π, π', hT, hG⟩ := GlobalTheory.T.torusInvariant_heatOperators_difference_global R Q O oa Y n v dd hdd D h h' hb hb' hΘ hu
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_addHom_invariantField_kills_weightZero R Q O oa Y n v dd hdd e hT
  refine ⟨ℓ, π, π', ?_⟩
  intro k α σ σ'' σ' h1' h1 T x z J hJ
  refine GlobalTheory.T.heat_operator_fourier_term_values_eq_of_local_identity R Q O oa Y n v dd hdd D h h' hb hb'
    (fun k α => 2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') ?_ k α σ σ' σ'' h1 h1' T x z J hJ
  intro i i' k α V hV f hf
  obtain ⟨h2d, h3, h4⟩ := hG i i' _ hV
  simp only [dlg] at h2d h3 h4
  have hle : Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) := fun pt hpt =>
    ⟨h.le i (hV hpt).1, h'.le i' (hV hpt).2⟩
  have hg : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) *
      pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ V) = 1 := by
    unfold pbT
    rw [dite_eq_left hle, dite_eq_left hle, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have mono : ∀ (δ : Fld Y.H.left) {W₁ W₂ : Y.H.left.Opens}, W₁ ≤ W₂ → IsField W₂ δ → IsField W₁ δ :=
    fun δ W₁ W₂ hle H => ⟨fun W hW => H.1 W (hW.trans hle), fun W hW => H.2.1 W (hW.trans hle),
      fun W W' hh hW => H.2.2 W W' hh (hW.trans hle)⟩
  rw [GlobalTheory.T.heatOperator_conj_unitPow_corrections R Y.H n dd h.Θ h.symm h.u (h.d i) (h.W i) (h.W i) _ (h.p i) (h.p' i) k _ _ hg (hV.trans inf_le_left)
    (h.lift i).1 (fun a => mono _ le_top (hdd a).1) f]
  congr 1
  have hc : constFn Y.H.hom (Y.q.left ⁻¹ᵁ V) (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') =
      2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ (ℓ α) +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * constFn Y.H.hom _ π +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ π' := by
    simp only [constFn, map_add (f := _), map_mul, map_pow, map_natCast, map_ofNat]
  simp only [hc]
  have hl := hℓ α V f hf
  unfold op
  rw [← hΘ, ← hu]
  linear_combination (2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V))) * h2d f + (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * f * h3 +
    (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * f * h4 + 2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * hl

end GlobalTheory.HeatUniq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineScalarTorusInvariantHeatOperatorsStatement

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

theorem _root_.GlobalTheory.T.exists_affine_scalar_torusInvariant_heatOperators : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (ℓ : Q.X →+ R) (π π' : R), ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π')) * sval σ x.left z J := by
  first | exact @GlobalTheory.HeatUniq.exists_affine_scalar | exact GlobalTheory.HeatUniq.exists_affine_scalar | (intros; apply GlobalTheory.HeatUniq.exists_affine_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorDefectPolynomialMonomialPeriods

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

namespace GlobalTheory.HeatDefect

theorem shiftEq_add {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {mu α : Q.X}
    {σ σ' σ'' : Q.SecB k α} {σ₁ σ₁' : Q.SecB k (α + k • mu)} {c₁ c₂ : R}
    (h0 : ShiftEq Q k mu α σ σ₁ 0 σ₁) (h1 : ShiftEq Q k mu α σ'' σ₁' c₁ σ₁)
    (h2 : ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J →
      sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom c₂) * sval σ x.left z J) :
    ShiftEq Q k mu α σ' σ₁' (c₁ + c₂) σ₁ := by
  intro u hu hc z J hJ
  have a := h1 u hu hc z J hJ
  have b := h0 u hu hc z J hJ
  have e := h2 _ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)) z J hJ
  have hz : (𝟙 (DegPre.BF Q (FractionRing R)).left) z ∈ (⊤ : (DegPre.BF Q (FractionRing R)).left.Opens) := trivial
  have g0 : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (0 : R)) = 0 := by
    rw [gs_eq _ z ⊤ hz]; simp only [Out.scal, map_zero]
  have gadd : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (c₁ + c₂)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₁) +
        gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₂) := by
    rw [← gs_add _ z ⊤ hz]; simp only [Out.scal, map_add (f := _)]
  rw [g0, zero_mul, add_zero] at b
  rw [a, e, gadd]
  linear_combination (-(gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₂))) * b

end GlobalTheory.HeatDefect

theorem GlobalTheory.HeatDefect.defect_polynomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb
  have hA := fun mu => GlobalTheory.T.exists_conjugate_heatOperator_periodShift R Dd O oa Y n v dd hv m t gam hm ht D hD h hb mu
  choose h' w₁ π₁ π₁' hb' hΘ hu hrel using hA
  have hU := fun mu => GlobalTheory.T.exists_affine_scalar_torusInvariant_heatOperators R Dd.toPre O oa Y n v dd hv D h (h' mu) hb (hb' mu) (hΘ mu).symm (hu mu).symm
  choose ℓ π₂ π₂' hU using hU
  refine ⟨fun mu => w₁ mu + ℓ mu, fun mu => π₁ mu + π₂ mu, fun mu => π₁' mu + π₂' mu, ?_⟩
  intro k mu α σ σ' σ₁ σ₁' hk hs ht₀ ht₁
  obtain ⟨σ'', hσ'', hsh⟩ := hrel mu k α σ σ₁ σ₁' hk hs ht₁
  have key := GlobalTheory.HeatDefect.shiftEq_add hs hsh (hU mu k α σ σ' σ'' ht₀ hσ'')
  refine (congrArg (fun c => ShiftEq Dd.toPre k mu α σ' σ₁' c σ₁) ?_).mpr key
  simp only [AddMonoidHom.add_apply]
  ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorDefectPolynomialMonomialPeriodsStatement

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

theorem _root_.GlobalTheory.T.heatOperator_defect_polynomial_monomial_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  first | exact @GlobalTheory.HeatDefect.defect_polynomial | exact GlobalTheory.HeatDefect.defect_polynomial | (intros; apply GlobalTheory.HeatDefect.defect_polynomial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialDefectHeatOperatorMonomial

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

theorem _root_.GlobalTheory.Heat.exists_polynomial_defect_of_isMonomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) :=
  GlobalTheory.T.heatOperator_defect_polynomial_monomial_periods
end
end
