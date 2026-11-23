module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaugedTorusInvariantHeatOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageTrQ
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldCommutesPointTranslationStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionRelOfTranslateSectionValues

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

namespace GlobalTheory.HeatTrans

theorem chart_rel_of_sval : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (k : ℕ) (σ : SecM (GlobalTheory.HeatTrans.tr Y.H x ≫ Y.q.left) Q.P.L k) (τ : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ GlobalTheory.HeatTrans.tr Y.H x) z J) → ∀ (c : Q.P.L.ι) (U : Y.H.left.Opens), U ≤ Y.q.left ⁻¹ᵁ Q.P.L.U c → rsT (σ.f fun _ => c) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) = pbT (GlobalTheory.HeatTrans.tr Y.H x) (rsT (τ.f fun _ => c) U) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) := by
  intro R _ _ Q O _ _ _ oa Y x k σ τ hst c U hU
  have hWσ : tr Y.H x ⁻¹ᵁ U ≤ LB.wchart Q.P.L (fun _ : Fin 1 => tr Y.H x ≫ Y.q.left) (fun _ => c) := fun y hy =>
    Set.mem_iInter.2 fun _ => hU hy
  have hWτ : U ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => c) := fun y hy =>
    Set.mem_iInter.2 fun _ => hU hy
  have e1 : rsT (σ.f fun _ => c) (tr Y.H x ⁻¹ᵁ U) = resG _ hWσ (σ.f fun _ => c) := GlobalTheory.KS.rsT_of_le hWσ _
  have e2 : rsT (τ.f fun _ => c) U = resG _ hWτ (τ.f fun _ => c) := GlobalTheory.KS.rsT_of_le hWτ _
  rw [e1, e2, GlobalTheory.KS.pbT_of_le (tr Y.H x) le_rfl]
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, hJc⟩ := exists_good Q.P.L Q.P.isLB y (K := Fin 1) (fun _ => tr Y.H x ≫ Y.q.left) (fun _ => c)
    (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 (hWσ hy) 0)
  have h1 := hst Y.H.left (𝟙 _) y J hJ
  rw [sval_of σ (𝟙 _) y J (fun _ => c) (fun _ => by rw [Category.id_comp]; exact hJc 0),
    sval_of τ (𝟙 _ ≫ tr Y.H x) y J (fun _ => c) (fun _ => by rw [Category.id_comp]; exact hJc 0)] at h1
  have hTy : (tr Y.H x) ((𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y) ∈ U := hy
  refine (gs_res (𝟙 _) y hWσ hy _).trans (h1.trans ?_)
  rw [← Scheme.Hom.app_eq_appLE]
  exact ((gs_pull (𝟙 _) (tr Y.H x) y U hTy _).trans (gs_res _ y hWτ hTy _)).symm

end GlobalTheory.HeatTrans
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionRelOfTranslateSectionValuesStatement

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

theorem _root_.GlobalTheory.T.chartFunction_rel_of_translate_section_values : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (k : ℕ) (σ : SecM (GlobalTheory.HeatTrans.tr Y.H x ≫ Y.q.left) Q.P.L k) (τ : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ GlobalTheory.HeatTrans.tr Y.H x) z J) → ∀ (c : Q.P.L.ι) (U : Y.H.left.Opens), U ≤ Y.q.left ⁻¹ᵁ Q.P.L.U c → rsT (σ.f fun _ => c) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) = pbT (GlobalTheory.HeatTrans.tr Y.H x) (rsT (τ.f fun _ => c) U) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) := by
  first | exact @GlobalTheory.HeatTrans.chart_rel_of_sval | exact GlobalTheory.HeatTrans.chart_rel_of_sval | (intros; apply GlobalTheory.HeatTrans.chart_rel_of_sval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightPullbackPointTranslation

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

namespace GlobalTheory.HeatTransWt

theorem valR_pbT_le {A : Type} [CommRing A] {X Z : Scheme.{0}} (w : Sp A ⟶ Z) (T : Z ⟶ X) {U : X.Opens}
    {U' : Z.Opens} (hU : U' ≤ T ⁻¹ᵁ U) (h : ⊤ ≤ w ⁻¹ᵁ U') (f : Γ(X, U)) :
    valR w U' (pbT T f U') = valR (w ≫ T) U f := by
  have h' : ⊤ ≤ (w ≫ T) ⁻¹ᵁ U := h.trans (w.preimage_mono hU)
  unfold valR
  rw [dite_eq_left h, dite_eq_left h', GlobalTheory.KS.pbT_of_le T hU]
  rw [← Scheme.Hom.appLE_comp_appLE w T U U' ⊤ hU h]
  rfl

theorem isWt_pbT_tr : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (α : Q.X) (U U' : Y.H.left.Opens), U' ≤ GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U → ∀ f : Γ(Y.H.left, U), IsWt Y α U f → IsWt Y α U' (pbT (GlobalTheory.HeatTrans.tr Y.H x) f U') := by
  intro R _ _ Q O _ _ _ oa Y x α U U' hU f hf S _ φ x₁ x₁' c a a' ha ha' hV hV' hq hc
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  let z : Over.mk (spMap φ) ⟶ Y.H := toUnit _ ≫ x
  have hleft : ∀ w : Over.mk (spMap φ) ⟶ Y.H, (w * z).left = w.left ≫ GlobalTheory.HeatTrans.tr Y.H x := fun w => by
    have e : w ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)) = w * z := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (w ≫ toUnit Y.H) (toUnit _)]
    rw [← e]; rfl
  rw [valR_pbT_le a' _ hU hV', valR_pbT_le a _ hU hV]
  subst ha ha'
  rw [← hleft, ← hleft]
  refine hf S φ (x₁ * z) (x₁' * z) c _ _ rfl rfl ?_ ?_ ?_ ?_
  · rw [hleft]; exact hV.trans (x₁.left.preimage_mono hU)
  · rw [hleft]; exact hV'.trans (x₁'.left.preimage_mono hU)
  · rw [MonObj.mul_comp, MonObj.mul_comp, hq]
  · intro χ y J hJ
    have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ z)).2 χ y J hJ
    have h1' := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' z)).2 χ y J hJ
    simp only [Y.Φ_b, GlobalTheory.TorusModel.cv] at h1 h1'
    rw [hq] at h1'
    refine mul_right_cancel (h1'.trans ?_)
    rw [hc χ y J hJ, _root_.mul_assoc, ← h1, _root_.mul_assoc]

end GlobalTheory.HeatTransWt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightPullbackPointTranslationStatement

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

theorem _root_.GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (α : Q.X) (U U' : Y.H.left.Opens), U' ≤ GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U → ∀ f : Γ(Y.H.left, U), IsWt Y α U f → IsWt Y α U' (pbT (GlobalTheory.HeatTrans.tr Y.H x) f U') := by
  first | exact @GlobalTheory.HeatTransWt.isWt_pbT_tr | exact GlobalTheory.HeatTransWt.isWt_pbT_tr | (intros; apply GlobalTheory.HeatTransWt.isWt_pbT_tr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedTorusInvariantHeatOperator

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


open GlobalTheory.HeatTrans in
theorem GlobalTheory.HeatTrans.exists_heat_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), ∃ h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D, h₁.Θ = h.Θ ∧ h₁.u = h.u ∧ (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) ∧ ∀ (k : ℕ) (τ τ' : SecM Y.q.left Q.P.L k) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J) → h.Acts k τ τ' → h₁.Acts k σ σ' := by
  intro R _ _ Q O _ _ _ oa Y n v dd hinv D h hB x
  have hTeq : (𝟙 Y.H * (toUnit Y.H ≫ x)).left = tr Y.H x := rfl
  rw [hTeq]
  have hTS := tr_tr_inv Y.H x
  have hST := tr_inv_tr Y.H x
  have hT := tr_hom Y.H x
  have hS := tr_hom Y.H x⁻¹
  set T := tr Y.H x with hTd
  set S := tr Y.H x⁻¹ with hSd
  have hdd : ∀ a (O O' : Y.H.left.Opens), O' ≤ T ⁻¹ᵁ O → ∀ f : Γ(Y.H.left, O),
      dd a O' (pbT T f O') = pbT T (dd a O f) O' := fun a => GlobalTheory.T.invariantVectorField_commutes_pointTranslation R Y.H (v a) (dd a) (hinv a) x
  have hpre : ∀ U : Y.H.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : Y.H.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  refine ⟨⟨h.Θ, h.symm, h.u, h.J, (fun i => T ⁻¹ᵁ h.W i), h.j, (fun i => conjF T S (h.d i)),
    (fun i => pbT T (h.p i) (T ⁻¹ᵁ h.W i)), (fun i => pbT T (h.p' i) (T ⁻¹ᵁ h.W i)), ?_, ?_, ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
  · refine top_le_iff.1 fun z _ => ?_
    have hz : T z ∈ ⨆ i, h.W i := h.cover ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  · intro i
    rw [Scheme.Hom.comp_preimage]
    exact T.preimage_mono (h.le i)
  · intro i
    exact isLift_conjF Y.H D hTS hST hT hS (h.lift i)
  · intro k i i' O₁ hO f
    have hOi : O₁ ≤ T ⁻¹ᵁ h.W i := hO.trans inf_le_left
    have hOi' : O₁ ≤ T ⁻¹ᵁ h.W i' := hO.trans inf_le_right
    have hSO : S ⁻¹ᵁ O₁ ≤ h.W i ⊓ h.W i' :=
      le_inf ((S.preimage_mono hOi).trans (hpre _).le) ((S.preimage_mono hOi').trans (hpre _).le)
    have hg : S ⁻¹ᵁ O₁ ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) :=
      le_inf (hSO.trans (inf_le_left.trans (h.le i))) (hSO.trans (inf_le_right.trans (h.le i')))
    have hg' : O₁ ≤ (T ≫ Y.q.left) ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) := by
      rw [Scheme.Hom.comp_preimage, ← hpre' O₁]
      exact T.preimage_mono hg
    have hOO : O₁ ≤ T ⁻¹ᵁ (S ⁻¹ᵁ O₁) := (hpre' O₁).ge
    rw [op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i) (h.p i) (h.p' i) k hOi,
      op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i') (h.p i') (h.p' i') k hOi',
      GlobalTheory.KS.pbT_mul, pbT_pow S le_rfl _ _, pbT_pbT S (T ≫ Y.q.left) hg' le_rfl]
    have hSTq : S ≫ T ≫ Y.q.left = Y.q.left := by rw [← Category.assoc, hST, Category.id_comp]
    rw [hSTq, h.glue k i i' _ hSO, GlobalTheory.KS.pbT_mul, pbT_pow T hOO, pbT_pbT T Y.q.left hg hOO]
  · intro i
    obtain ⟨⟨V, hV⟩, hp, hp', hd⟩ := hB i
    refine ⟨?_, GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x 0 _ _ le_rfl _ hp, GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x 0 _ _ le_rfl _ hp', ?_⟩
    · exact ⟨_, (congrArg (T ⁻¹ᵁ ·) hV).trans (preimage_tr_q Y x V)⟩
    · intro α V₁ hV₁ f hf
      obtain ⟨V₂, hV₂⟩ : ∃ V₂, S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁) = Y.q.left ⁻¹ᵁ V₂ := ⟨_, preimage_tr_q Y x⁻¹ V₁⟩
      have hle : S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁) ≤ h.W i := (S.preimage_mono hV₁).trans (hpre _).le
      have hf' : IsWt Y α (S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁)) (pbT S f (S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁))) :=
        GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x⁻¹ α _ _ le_rfl f hf
      have gen : ∀ (U : Y.H.left.Opens), U = Y.q.left ⁻¹ᵁ V₂ → ∀ g : Γ(Y.H.left, U), U ≤ h.W i → IsWt Y α U g →
          IsWt Y α U (h.d i U g) := by
        rintro U rfl g hU hg
        exact hd α V₂ hU g hg
      exact GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x α _ _ (hpre' _).ge _ (gen _ hV₂ _ hle hf')
  · intro k τ τ' σ σ' hσ hσ' hA i
    have hW : S ⁻¹ᵁ (T ⁻¹ᵁ h.W i) ≤ h.W i := (hpre _).le
    show rsT (σ'.f fun _ => h.j i) (T ⁻¹ᵁ h.W i) = op Y.H dd h.Θ h.u (conjF T S (h.d i)) (pbT T (h.p i) (T ⁻¹ᵁ h.W i))
      (pbT T (h.p' i) (T ⁻¹ᵁ h.W i)) k (T ⁻¹ᵁ h.W i) (rsT (σ.f fun _ => h.j i) (T ⁻¹ᵁ h.W i))
    rw [GlobalTheory.T.chartFunction_rel_of_translate_section_values R Q O oa Y x k σ' τ' hσ' (h.j i) (h.W i) (h.le i), GlobalTheory.T.chartFunction_rel_of_translate_section_values R Q O oa Y x k σ τ hσ (h.j i) (h.W i) (h.le i),
      op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (le_rfl : T ⁻¹ᵁ h.W i ≤ T ⁻¹ᵁ h.W i),
      pbT_pbT S T le_rfl le_rfl, hST, pbT_id hW,
      op_rsT Y.H dd (fun a => (hinv a).1) h.Θ h.u (h.d i) (h.lift i).1 (h.p i) (h.p' i) k hW le_rfl,
      GlobalTheory.KS.pbT_rsT T hW (hpre' _).ge, hA i]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedTorusInvariantHeatOperatorStatement

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

theorem _root_.GlobalTheory.T.exists_translated_torus_invariant_heat_operator : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), ∃ h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D, h₁.Θ = h.Θ ∧ h₁.u = h.u ∧ (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) ∧ ∀ (k : ℕ) (τ τ' : SecM Y.q.left Q.P.L k) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J) → h.Acts k τ τ' → h₁.Acts k σ σ' := by
  first | exact @GlobalTheory.HeatTrans.exists_heat_translate | exact GlobalTheory.HeatTrans.exists_heat_translate | (intros; apply GlobalTheory.HeatTrans.exists_heat_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjTranslationGauge

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

namespace GlobalTheory.Heat.ConjGauge
open ReciprocityTheory.ChartRestriction.G.Semi

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem exists_pullSec {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (m : Y ⟶ X) (T : Y ⟶ Y) (k : ℕ)
    (τ : SecM m L k) : ∃ σ : SecM (T ≫ m) L k, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → sval σ r z J = sval τ (r ≫ T) z J := by
  have hF : FormEq (K := Fin 1 ⊕ PEmpty.{1}) (Sum.elim (fun _ : Fin 1 => T ≫ m) PEmpty.elim)
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) PEmpty.elim) (K' := Fin 1) (fun _ => T ≫ m) (fun _ => (k : ℤ)) := by
    intro U _ h
    simp [Fintype.prod_sum_type]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF (pullMulSec τ T (LB.oneGen L (Y := Y)) (oneGen_isGen L))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  rw [hσ Z r z J hJ, sval_pullMulSec τ T _ _ r z hJ, val_one, Units.val_one, _root_.mul_one]

theorem conj_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (τ τ' ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → h.Acts k τ τ' → h'.Acts k ρ ρ' := by
  intro R _ _ _ Q O _ _ _ oa Y n v dd hv D h hB x e β he hwt
  obtain ⟨h₁, hΘ₁, hu₁, hB₁, hA₁⟩ := GlobalTheory.T.exists_translated_torus_invariant_heat_operator R Q O oa Y n v dd hv D h hB x
  obtain ⟨h', hB', hΘ', hu', hA'⟩ := GlobalTheory.T.exists_gauged_torusInvariant_heatOperator R Q O oa Y n v dd hv D x h₁ hB₁ e β he hwt
  refine ⟨h', hB', hΘ'.trans hΘ₁, hu'.trans hu₁, fun k τ τ' ρ ρ' hρ hρ' hact => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_pullSec Q.P.L Q.P.isLB Y.q.left (𝟙 Y.H * (toUnit Y.H ≫ x)).left k τ
  obtain ⟨σ', hσ'⟩ := exists_pullSec Q.P.L Q.P.isLB Y.q.left (𝟙 Y.H * (toUnit Y.H ≫ x)).left k τ'
  exact hA' k σ σ' ρ ρ' (fun Z r z J hJ => by rw [hσ Z r z J hJ]; exact hρ Z r z J hJ)
    (fun Z r z J hJ => by rw [hσ' Z r z J hJ]; exact hρ' Z r z J hJ) (hA₁ k τ τ' σ σ' hσ hσ' hact)

end GlobalTheory.Heat.ConjGauge
end
end
