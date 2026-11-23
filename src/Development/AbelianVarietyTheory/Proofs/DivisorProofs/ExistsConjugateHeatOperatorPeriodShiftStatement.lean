module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjTranslationGauge
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFourierTermTranslationGaugeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTermsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjTranslationGaugeStatement

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

theorem _root_.GlobalTheory.T.heatOperator_conj_translation_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (τ τ' ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → h.Acts k τ τ' → h'.Acts k ρ ρ' := by
  first | exact @GlobalTheory.Heat.ConjGauge.conj_gauge | exact GlobalTheory.Heat.ConjGauge.conj_gauge | (intros; apply GlobalTheory.Heat.ConjGauge.conj_gauge <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeibnizAlongBaseConstantsAtPoints

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

namespace GlobalTheory.Heat

theorem Heat.acts_const_at_points : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (v : Fin n → TanM (𝟙 (Sp R)) G) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat G m L dd ⇑D) (k : ℕ) (a b : R) (ρ τ ρ' τ' : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ r z J) → h.Acts k ρ ρ' → h.Acts k τ τ' → ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D b)) * sval τ r z J := by
  intro R _ G _ _ n X m L hL v dd hinv D h k a b ρ τ ρ' τ' hpt hρ hτ

  have cTop : ∀ c : R, constFn G.hom ⊤ c = scal G.hom c := fun c => by
    simp only [constFn, Out.scal, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have gsR : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) {O O₀ : G.left.Opens} (hle : O ≤ O₀) (hz : r z ∈ O)
      (s : Γ(G.left, O₀)), gs r z O (rsT s O) = gs r z O₀ s := fun r z _ _ hle hz s => by
    rw [GlobalTheory.KS.rsT_of_le hle]; exact gs_res r z hle hz s
  have gsC : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) (O : G.left.Opens) (hz : r z ∈ O) (c : R),
      gs r z O (constFn G.hom O c) = gs r z ⊤ (scal G.hom c) := fun r z O hz c => by
    rw [← GlobalTheory.KS.rsT_constFn G.hom (le_top : O ≤ ⊤) c, gsR r z le_top hz, cTop]
  have cMul : ∀ (O : G.left.Opens) (c : R),
      constFn G.hom O (2 * (k : R) * c) = 2 * (k : Γ(G.left, O)) * constFn G.hom O c := fun O c => by
    simp [constFn, map_mul, map_natCast, map_ofNat]
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => Glue.le_wchart _ (h.le i)

  have leib : ∀ i (c : R) (F : Γ(G.left, h.W i)),
      op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (constFn G.hom (h.W i) c * F) =
        constFn G.hom (h.W i) c * op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) F +
          constFn G.hom (h.W i) (2 * (k : R) * D c) * F := by
    intro i c F
    have hd := (h.lift i).1.2.1 (h.W i) le_rfl (constFn G.hom (h.W i) c) F
    have hdc := (h.lift i).2 (h.W i) le_rfl c
    have hdd : ∀ a' (f : Γ(G.left, h.W i)), dd a' (h.W i) (constFn G.hom (h.W i) c * f) =
        constFn G.hom (h.W i) c * dd a' (h.W i) f := fun a' f => by
      rw [(hinv a').1.2.1 (h.W i) le_top, IsInv.apply_constFn G (v a') (dd a') (hinv a'), mul_zero, add_zero]
    have hs : ∀ (f : Γ(G.left, h.W i)),
        ∑ a', ∑ b', constFn G.hom (h.W i) (h.Θ a' b') * dd a' (h.W i) (dd b' (h.W i) (constFn G.hom (h.W i) c * f)) =
          constFn G.hom (h.W i) c * ∑ a', ∑ b', constFn G.hom (h.W i) (h.Θ a' b') * dd a' (h.W i) (dd b' (h.W i) f) := by
      intro f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hdd, hdd]; ring
    have hs' : ∑ a', constFn G.hom (h.W i) (h.u a') * dd a' (h.W i) (constFn G.hom (h.W i) c * F) =
        constFn G.hom (h.W i) c * ∑ a', constFn G.hom (h.W i) (h.u a') * dd a' (h.W i) F := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [hdd]; ring
    simp only [op]
    rw [hs, hs', hd, hdc, cMul]
    ring

  have onW : ∀ i, constFn G.hom (h.W i) a * rsT (ρ'.f fun _ => h.j i) (h.W i) +
      constFn G.hom (h.W i) (2 * (k : R) * D a) * rsT (ρ.f fun _ => h.j i) (h.W i) =
      constFn G.hom (h.W i) b * rsT (τ'.f fun _ => h.j i) (h.W i) +
      constFn G.hom (h.W i) (2 * (k : R) * D b) * rsT (τ.f fun _ => h.j i) (h.W i) := by
    intro i
    have hA : constFn G.hom (h.W i) a * rsT (ρ.f fun _ => h.j i) (h.W i) =
        constFn G.hom (h.W i) b * rsT (τ.f fun _ => h.j i) (h.W i) := by
      refine fn_ext fun x hx => ?_
      obtain ⟨J, hJ, e⟩ := exists_good L hL x (fun _ : Fin 1 => m) (fun _ => h.j i) (fun _ _ _ => rfl)
        (fun _ => h.le i hx)
      have hp := hpt G.left (𝟙 _) x J hJ
      have s1 : ∀ σ : SecM m L k, sval σ (𝟙 G.left) x J = gs (𝟙 G.left) x (h.W i) (rsT (σ.f fun _ => h.j i) (h.W i)) :=
        fun σ => by
          rw [sval_of σ (𝟙 G.left) x J (fun _ => h.j i) (fun q => by rw [Category.id_comp]; exact e q)]
          exact (gsR (𝟙 G.left) x (hWc i) hx _).symm
      rw [s1, s1] at hp
      rw [gs_mul _ x _ hx, gs_mul _ x _ hx, gsC _ x _ hx, gsC _ x _ hx]
      exact hp
    rw [hρ i, hτ i, ← leib, ← leib, hA]

  intro Z r z J hJ
  obtain ⟨i, hi⟩ : ∃ i, r z ∈ h.W i := by
    have : r z ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hz1 := hJ.mem (fun _ : Fin 1 => m) r
  have hz2 : r z ∈ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := hWc i hi
  have sv : ∀ σ : SecM m L k, sval σ r z J =
      (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ m)) (fun _ => h.j i)).val *
        gs r z (h.W i) (rsT (σ.f fun _ => h.j i) (h.W i)) := fun σ => by
    exact (sec_trans σ r z hz1 hz2).trans (congrArg _ (gsR r z (hWc i) hi _).symm)
  have E := congrArg (gs r z (h.W i)) (onW i)
  simp only [gs_add r z _ hi, gs_mul r z _ hi, gsC r z _ hi] at E
  rw [sv ρ, sv τ, sv ρ', sv τ']
  linear_combination (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ m)) (fun _ => h.j i)).val * E

end GlobalTheory.Heat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeibnizAlongBaseConstantsAtPointsStatement

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

theorem _root_.GlobalTheory.T.leibniz_along_baseConstants_at_points : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (v : Fin n → TanM (𝟙 (Sp R)) G) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat G m L dd ⇑D) (k : ℕ) (a b : R) (ρ τ ρ' τ' : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ r z J) → h.Acts k ρ ρ' → h.Acts k τ τ' → ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D b)) * sval τ r z J := by
  first | exact @GlobalTheory.Heat.Heat.acts_const_at_points | exact GlobalTheory.Heat.Heat.acts_const_at_points | (intros; apply GlobalTheory.Heat.Heat.acts_const_at_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateHeatOperatorPeriodShift

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

namespace GlobalTheory.HeatDefect

theorem exists_gauge_translate : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])), e.IsGen → ∀ (k : ℕ) (τ : SecM Y.q.left Q.P.L k), ∃ ρ : SecM Y.q.left Q.P.L k, (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) := by
  intro R _ _ Q O _ _ _ oa Y x e he k τ
  obtain ⟨ρ, hρ⟩ := exists_sec (L := Q.P.L) Q.P.isLB
    (φ' := fun _ : Fin 1 => Y.q.left) (ε' := fun _ => (k : ℤ))
    (by
      intro U _ g
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [zpow_mul, zpow_mul, zpow_one, zpow_neg_one, _root_.mul_comm]
      exact inv_mul_cancel_right _ _)
    (pullMulSec τ (𝟙 Y.H * (toUnit Y.H ≫ x)).left (GeneratorPullback.powGen Q.P.L _ _ e k) (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ e he k))
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  rw [hρ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ]
  congr 1
  exact congrArg Units.val (map_pow _ _ _)

theorem exists_conj_shift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∀ mu : Dd.toPre.X, ∃ (h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X →+ R) (π π' : R), IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) (σ₁ σ₁' : Dd.toPre.SecB k (α + k • mu)), 1 ≤ k → ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → TActs Y h k (α + k • mu) σ₁ σ₁' → ∃ σ'' : Dd.toPre.SecB k α, TActs Y h' k α σ σ'' ∧ ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb mu
  obtain ⟨x, e, β, w, π, π', he, hwe, hTR⟩ := GlobalTheory.T.thetaShift_fourierTerm_translation_gauge R Dd O oa Y m t gam hm ht D hD mu
  obtain ⟨h', hb', hΘ, hu, hint⟩ :=
    GlobalTheory.T.heatOperator_conj_translation_gauge R Dd.toPre O oa Y n (fun a => v a) dd hv D h hb x e β he hwe
  refine ⟨h', w, π, π', hb', hΘ, hu, ?_⟩
  intro k α σ σ₁ σ₁' hk hs hA
  obtain ⟨τ₁, τ₁', hτ₁, hτ₁', hA₁⟩ := hA
  obtain ⟨σ'', τ, τ'', hτ, hτ'', hA'⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h' hb' k α σ
  obtain ⟨ρ, hρ⟩ := exists_gauge_translate Y x e he k τ₁
  obtain ⟨ρ', hρ'⟩ := exists_gauge_translate Y x e he k τ₁'
  have hAρ := hint k τ₁ τ₁' ρ ρ' hρ hρ' hA₁
  obtain ⟨a, b, -, hab⟩ := hTR k α hk
  obtain ⟨h1, h2⟩ := hab σ σ₁ τ τ₁ ρ hs hτ hτ₁ hρ
  exact ⟨σ'', ⟨τ, τ'', hτ, hτ'', hA'⟩, h2 σ'' σ₁' τ'' τ₁' ρ' hτ'' hτ₁' hρ'
    (GlobalTheory.T.leibniz_along_baseConstants_at_points Y.H Y.q.left Dd.toPre.P.L Dd.toPre.P.isLB (fun a => v a) dd hv D h' k a b ρ τ ρ' τ'' h1 hAρ hA')⟩

end GlobalTheory.HeatDefect
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateHeatOperatorPeriodShiftStatement

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

theorem _root_.GlobalTheory.T.exists_conjugate_heatOperator_periodShift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∀ mu : Dd.toPre.X, ∃ (h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X →+ R) (π π' : R), IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) (σ₁ σ₁' : Dd.toPre.SecB k (α + k • mu)), 1 ≤ k → ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → TActs Y h k (α + k • mu) σ₁ σ₁' → ∃ σ'' : Dd.toPre.SecB k α, TActs Y h' k α σ σ'' ∧ ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  first | exact @GlobalTheory.HeatDefect.exists_conj_shift | exact GlobalTheory.HeatDefect.exists_conj_shift | (intros; apply GlobalTheory.HeatDefect.exists_conj_shift <;> assumption)
end
end
