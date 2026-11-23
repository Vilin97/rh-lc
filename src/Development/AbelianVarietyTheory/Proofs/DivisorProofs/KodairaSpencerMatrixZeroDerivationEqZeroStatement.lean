module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreimageTranslate
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVe

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDerBridge

theorem valR_add_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f + g) = valR a O f + valR a O g := by
  simp only [valR, dif_pos ha, map_add (f := _)]

theorem valR_mul_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f * g) = valR a O f * valR a O g := by
  simp only [valR, dif_pos ha, map_mul]

theorem isInvDer_of_isInv : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  intro K _ A _ _ v u dd hu ht hd W f
  have hpre : ((fst (epsR K) A ≫ u) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W :=
    GlobalTheory.InvFieldBasis.preimage_translate ht W
  refine GlobalTheory.LogKSBal.ext_valR _ _ fun B _ x hx => ?_
  obtain ⟨β, hβ⟩ : ∃ β : DualNumber K →+* B, x ≫ (fst (epsR K) A).left = spMap β :=
    ⟨(Spec.preimage (x ≫ (fst (epsR K) A).left)).hom, (Spec.map_preimage _).symm⟩
  letI : Algebra K B := (β.comp (algebraMap K (DualNumber K))).toAlgebra
  set e : B := β DualNumber.eps with he_def
  have he : e * e = 0 := by rw [he_def, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  let βa : DualNumber K →ₐ[K] B := { β with commutes' := fun _ => rfl }
  have hβe : βa = GlobalTheory.SqZero.epsTo K e he := DualNumber.algHom_ext (by simp [βa, e])
  have hxw : x ≫ (epsR K ⊗ A).hom = (Chart.sp (R₀ := K) B).hom := by
    rw [← Over.w (fst (epsR K) A), ← Category.assoc, hβ]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let xt : Chart.sp (R₀ := K) B ⟶ epsR K ⊗ A := Over.homMk x hxw
  let z : Chart.sp (R₀ := K) B ⟶ A := xt ≫ snd (epsR K) A
  have hfst : xt ≫ fst (epsR K) A = Chart.spMap (GlobalTheory.SqZero.epsTo K e he) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Chart.spMap_left, ← hβe]
    exact hβ
  have hmu : x ≫ ((fst (epsR K) A ≫ u) * snd (epsR K) A).left =
      ((Chart.spMap (GlobalTheory.SqZero.epsTo K e he) ≫ u : Chart.sp (R₀ := K) B ⟶ A) * z).left := by
    rw [← hfst, Category.assoc, ← MonObj.comp_mul]
    rfl
  have hz : ⊤ ≤ z.left ⁻¹ᵁ W := fun p hp => hx hp
  obtain ⟨-, H⟩ := GlobalTheory.Heat.DlogIndep.valR_translate hu ht hd e he z W hz
  rw [GlobalTheory.LogKSBal.valR_pbT x _ hpre.ge hx, hmu, H, valR_add_of x hx, valR_mul_of x hx,
    GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx, GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx,
    GlobalTheory.LogKSBal.valR_constFn _ x hx hβ]
  rfl

end GlobalTheory.InvDerBridge
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isInvariantField_dualNumber_of_isInvariant_tangentVector : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  first | exact @GlobalTheory.InvDerBridge.isInvDer_of_isInv | exact GlobalTheory.InvDerBridge.isInvDer_of_isInv | (intros; apply GlobalTheory.InvDerBridge.isInvDer_of_isInv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZero

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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSZeroDer

theorem isInvDer_of_isInv {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    {v : TanM (𝟙 (Sp K)) A} {u : epsR K ⟶ A} (hu : u.left = (tv v).left) (ht : IsTangent u)
    {dd : Fld A.left} (hd : IsInv A v dd) : GlobalTheory.KS.IsInvDer u dd :=
  GlobalTheory.T.isInvariantField_dualNumber_of_isInvariant_tangentVector K A v u dd hu ht hd

theorem pbT_id_le {X : Scheme.{0}} {O₀ O : X.Opens} (h : O ≤ O₀) (s : Γ(X, O₀)) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT, rsT, dite_eq_left (show O ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ O₀ from h), dite_eq_left h]
  rfl

theorem constFn_zero_fn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (O : X.Opens) :
    constFn q O 0 = 0 := by
  rw [constFn, map_zero, map_zero]

theorem id_app_apply {X : Scheme.{0}} (O : X.Opens) (s : Γ(X, O)) : ((𝟙 X : X ⟶ X).app O).hom s = s := by
  simp only [Scheme.Hom.id_app]
  rfl

theorem rsT_mul_le {X : Scheme.{0}} {O₀ O : X.Opens} (h : O ≤ O₀) (s t : Γ(X, O₀)) : rsT (s * t) O = rsT s O * rsT t O := by
  rw [rsT, rsT, rsT, dite_eq_left h, dite_eq_left h, dite_eq_left h, map_mul]

theorem dlg_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (L : LB A.left)
    (δ : Fld A.left) (hf : IsField ⊤ δ) (i i' : L.ι) (ψ : Γ(A.left, L.U i ⊓ L.U i'))
    (hψ : (L.g i i').val * ψ = δ (L.U i ⊓ L.U i') (L.g i i').val) (O : A.left.Opens) (hO : O ≤ L.U i ⊓ L.U i') :
    dlg A (𝟙 _) L δ i i' O = rsT ψ O := by
  rw [dlg, pbT_id_le hO, pbT_id_le hO]
  have e2 := congrArg (fun s => rsT s O) hψ
  have e3 : rsT (δ (L.U i ⊓ L.U i') (L.g i i').val) O = δ O (rsT (L.g i i').val O) := by
    rw [rsT, rsT, dite_eq_left hO, dite_eq_left hO]
    exact (hf.2.2 _ O hO le_top _).symm
  rw [rsT_mul_le hO, e3] at e2
  rw [← e2, mul_comm (rsT (L.g i i').val O), _root_.mul_assoc, ← rsT_mul_le hO, Units.mul_inv]
  have e4 : rsT (1 : Γ(A.left, L.U i ⊓ L.U i')) O = 1 := by rw [rsT, dite_eq_left hO, map_one]
  rw [e4, _root_.mul_one]

theorem main : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ M : Matrix (Fin n) (Fin n) K, KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) M → M = 0 := by
  intro K _ _ P₀ n v dd hdd M hM
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  obtain ⟨u, hu, hul⟩ := GlobalTheory.Heat.DlogIndep.exists_isLieBasis v
  have hinv : ∀ a, GlobalTheory.KS.IsInvDer (u a) (dd a) := fun a => isInvDer_of_isInv (hul a) (hu.1 a) (hdd a)
  have hiso := GlobalTheory.SiegLower.lbIso_pull_id P₀.isLB
  obtain ⟨⟨φ, hφ⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hinv _ (𝟙 _) P₀.L P₀.isLB hiso
  obtain ⟨J, W, j, d, hcov, hWj, hl, hdiff⟩ := hM
  have hcv : ∀ z : P₀.A.left, ∃ i, (𝟙 P₀.A.left : P₀.A.left ⟶ P₀.A.left) z ∈ W i := fun z => by
    have h2 : z ∈ ⨆ i, W i := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  have hpb : IsPullback (𝟙 P₀.A.left) P₀.A.hom P₀.A.hom (𝟙 (Sp K)) := IsPullback.of_horiz_isIso ⟨by simp⟩
  refine GlobalTheory.KSUniq.theta_eq_fibre P₀ u hu dd hinv P₀.A.hom (𝟙 _) (𝟙 _) hpb (U := ⊤) (isAffineOpen_top _) P₀.L
    P₀.isLB hiso (fun _ => 0) M 0 W W j j d (fun _ _ _ => 0) (fun _ => le_top) (fun _ => le_top) hWj hWj hcv hcv
    (fun i => (hl i).1) (fun _ => isField_zero _) ?_ ?_ φ hφ ?_ ?_
  · intro i h r
    have e : r = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r) := by
      simp
    have := (hl i).2 (W i) le_rfl ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r)
    show _ = (P₀.A.hom.appLE ⊤ (W i) h).hom 0
    rw [map_zero]
    conv_lhs => rw [e]
    exact this.trans (by simp [constFn])
  · intro k h r
    show (0 : Γ(P₀.A.left, W k)) = (P₀.A.hom.appLE ⊤ (W k) h).hom 0
    rw [map_zero]
  · intro i i' O hO f
    rw [id_app_apply, id_app_apply, hdiff i i' O hO f]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have p : pbT (𝟙 P₀.A.left) (P₀.L.g (j i) (j i')).val
        ((𝟙 P₀.A.left) ⁻¹ᵁ P₀.L.U (j i) ⊓ (𝟙 P₀.A.left) ⁻¹ᵁ P₀.L.U (j i')) = (P₀.L.g (j i) (j i')).val :=
      GlobalTheory.Heat.DlogIndep.pbT_id (X := P₀.A.left) (P₀.L.U (j i) ⊓ P₀.L.U (j i')) _
    have hψ := hφ b (j i) (j i')
    rw [p] at hψ
    rw [dlg_eq P₀.L (dd b) (hdd b).1 (j i) (j i') (φ b (j i) (j i')) hψ O
      (fun z hz => ⟨hWj i (hO hz).1, hWj i' (hO hz).2⟩)]
    rfl
  · intro k k' O hO f
    rw [id_app_apply]
    simp only [Matrix.zero_apply, constFn_zero_fn, zero_mul, Finset.sum_const_zero, sub_self]
    rfl

end GlobalTheory.KSZeroDer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZeroStatement

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

theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_zero_derivation_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ M : Matrix (Fin n) (Fin n) K, KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) M → M = 0 := by
  first | exact @GlobalTheory.KSZeroDer.main | exact GlobalTheory.KSZeroDer.main | (intros; apply GlobalTheory.KSZeroDer.main <;> assumption)
end
end
