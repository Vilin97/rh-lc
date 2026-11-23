module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalNeZeroOfIsIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorEigenDiagonalThetaOrderTwoStatement
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroupStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.abelian_sections_irreducible_theta_group : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.ThetaIrred.main | exact GlobalTheory.ThetaIrred.main | (intros; apply GlobalTheory.ThetaIrred.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaTensorNeZero

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AdditionTensor

section
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} {K : Type} [Fintype K]

noncomputable def svalHom (p : Y ⟶ Spec (CommRingCat.of F)) (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (r : T ⟶ Y) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) : SecMod p (LB.LinComb L φ ε) →+ T.presheaf.stalk z :=
  AddMonoidHom.mk' (fun s => sval s.sec r z J) (fun _ _ => gs_add r z _ (hJ.mem φ r) _ _)

theorem svalHom_smul (p : Y ⟶ Spec (CommRingCat.of F)) (φ : K → (Y ⟶ Z)) (ε : K → ℤ) (r : T ⟶ Y) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    svalHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) (scal p c)).trans (gs_pull r p z ⊤ trivial _)))

end

theorem sum_sval_mul_eq_zero {F : Type} [CommRing F] {Z Y₁ Y₂ T : Scheme.{0}} {L : LB Z}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂))
    (h : ∑ i, TensorProduct.tmul F (a i) (b i) = 0) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂) (e : r₁ ≫ p₁ = r₂ ≫ p₂) (z : T)
    {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  let f : SecMod p₁ (LB.LinComb L φ₁ ε₁) →+ SecMod p₂ (LB.LinComb L φ₂ ε₂) →+ T.presheaf.stalk z :=
    (((AddMonoidHom.mul (R := T.presheaf.stalk z)).comp (svalHom p₁ φ₁ ε₁ r₁ z hJ)).flip.comp
      (svalHom p₂ φ₂ ε₂ r₂ z hJ)).flip
  have hf : ∀ s t, f s t = svalHom p₁ φ₁ ε₁ r₁ z hJ s * svalHom p₂ φ₂ ε₂ r₂ z hJ t := fun _ _ => rfl
  have hb : ∀ (c : F) s t, f (c • s) t = f s (c • t) := fun c s t => by
    rw [hf, hf, svalHom_smul, svalHom_smul, e]; ring
  have := congrArg (TensorProduct.liftAddHom f hb) h

  rw [map_sum, map_zero] at this
  simp only [TensorProduct.liftAddHom_tmul] at this
  exact this

end GlobalTheory.AdditionTensor

namespace GlobalTheory

theorem addition_tensor_ne_zero : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by
  intro S P F _ p th n t t' hadd hth h0
  obtain ⟨κ, -, hκ⟩ := hadd
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hI : IsIntegral (Over.mk p ⊗ P.A).left := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  obtain ⟨z⟩ : Nonempty (Over.mk p ⊗ P.A).left := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB z (K := PEmpty) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim) (fun k => k.elim)
  have hne : ∃ j, th.sec.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hth (DVR.SecOps.sec_ext hc)
  have hv := sval_ne_zero_of_isIso P.A.left (Over.mk p ⊗ P.A).left P.L P.isLB (Fin 1)
    (fun _ => (snd (Over.mk p) P.A).left) (fun _ => ((1 : ℕ) : ℤ)) th.sec hne _ (𝟙 _) z J hJ
  have h1 := hκ (Over.mk p ⊗ P.A) (fst _ _) (snd _ _) 1 z J hJ
  have h2 := AdditionTensor.sum_sval_mul_eq_zero (fst (Over.mk p) P.A).left (fst (Over.mk p) P.A).left
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ))
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ)) t t' h0
    (lift (fst (Over.mk p) P.A) (snd (Over.mk p) P.A)).left (lift (fst (Over.mk p) P.A) (1 : Over.mk p ⊗ P.A ⟶ P.A)).left
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z hJ
  have h3 := h1.symm.trans h2
  rw [inv_one, _root_.mul_one, lift_fst_snd, Units.mul_right_eq_zero, mul_self_eq_zero] at h3
  exact hv h3

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaTensorNeZeroStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.additionFormula_tensor_ne_zero : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by
  first | exact @GlobalTheory.addition_tensor_ne_zero | exact GlobalTheory.addition_tensor_ne_zero | (intros; apply GlobalTheory.addition_tensor_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EigenTensorFullLeftSupport

section

@[expose] public section

namespace GlobalTheory

open TensorProduct

noncomputable def rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) : TensorProduct F E E' →ₗ[F] E :=
  (TensorProduct.rid F E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l

theorem rightContract_tmul {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (x : E) (y : E') :
    rightContract l (x ⊗ₜ[F] y) = l y • x := by
  simp [rightContract]

theorem rightContract_map {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (f : E →ₗ[F] E) (g : E' →ₗ[F] E')
    (w : TensorProduct F E E') :
    rightContract l (TensorProduct.map f g w) = f (rightContract (l ∘ₗ g) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [rightContract_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem eq_zero_of_rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (w : TensorProduct F E E')
    (h : ∀ l : E' →ₗ[F] F, rightContract l w = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F E'
  have key : ∀ (i) (v : TensorProduct F E E'),
      TensorProduct.equivFinsuppOfBasisRight b v i = rightContract (b.coord i) v := by
    intro i v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [rightContract_tmul]
    | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, h]
  simp

theorem eigenTensor_full_left_support :
    ∀ (F : Type) [Field F] (E E' Ix : Type) [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (Φ : Ix → (E →ₗ[F] E)) (Φ' : Ix → (E' ≃ₗ[F] E')), (∀ U : Submodule F E, (∀ i, ∀ v ∈ U, Φ i v ∈ U) → U = ⊥ ∨ U = ⊤) → ∀ w : TensorProduct F E E', w ≠ 0 → (∀ i, ∃ r : F, TensorProduct.map (Φ i) (Φ' i : E' →ₗ[F] E') w = r • w) → ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E' →ₗ[F] E') w = 0 → π = 0 := by
  intro F _ E E' Ix _ _ _ _ Φ Φ' hirr w hw heig π hπ
  let U : Submodule F E := Submodule.span F (Set.range fun l : E' →ₗ[F] F => rightContract l w)
  have hmem : ∀ l : E' →ₗ[F] F, rightContract l w ∈ U := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hstab : ∀ i, ∀ v ∈ U, Φ i v ∈ U := by
    intro i v hv
    have hle : U ≤ U.comap (Φ i) := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      obtain ⟨r, hr⟩ := heig i
      have h1 := rightContract_map (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) (Φ i) (Φ' i : E' →ₗ[F] E') w
      have h2 : (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) ∘ₗ (Φ' i : E' →ₗ[F] E') = l := by
        ext y; simp
      rw [h2, hr, map_smul] at h1
      show Φ i (rightContract l w) ∈ U
      rw [← h1]
      exact U.smul_mem _ (hmem _)
    exact hle hv
  rcases hirr U hstab with hU | hU
  · exfalso
    apply hw
    apply eq_zero_of_rightContract
    intro l
    have := hmem l
    rwa [hU, Submodule.mem_bot] at this
  · have hle : U ≤ LinearMap.ker π := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      have h1 := rightContract_map l π LinearMap.id w
      rw [hπ, map_zero, LinearMap.comp_id] at h1
      exact h1.symm
    rw [hU, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorFullLeftSupport

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddTensor

theorem full_left_support : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S), (2 : F) ≠ 0 → ∀ (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∀ π : EA P p 2 →ₗ[F] EA P p 2, TensorProduct.map π (LinearMap.id : EA P p 2 →ₗ[F] EA P p 2) (∑ i, TensorProduct.tmul F (t i) (t' i)) = 0 → π = 0 := by
  intro h1 h2 S _ P F _ _ p h2F th n t t' hadd hth
  choose Φ hΦ hΦu _ using GlobalTheory.ThetaLin.main S P F p 2
  refine GlobalTheory.eigenTensor_full_left_support F (EA P p 2) (EA P p 2)
    {θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p) // θ.pt ^ 2 = 1}
    (fun θ => (Φ θ.1 : EA P p 2 →ₗ[F] EA P p 2)) (fun θ => Φ θ.1) ?_ _
    (GlobalTheory.T.additionFormula_tensor_ne_zero S P F p th n t t' hadd hth) ?_
  · intro U hU
    refine (GlobalTheory.T.abelian_sections_irreducible_theta_group h1 h2 S P F p 2 (by exact_mod_cast h2F)).2 U ?_
    intro θ hθ v v' hvv' hv
    have e : v' = Φ θ v := hΦu θ v.sec v'.sec hvv'
    rw [e]
    exact hU ⟨θ, hθ⟩ v hv
  · intro θ
    obtain ⟨r, hr⟩ := GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two h1.globalFns S P F p th n t t' (fun i => Φ θ.1 (t i)) (fun i => Φ θ.1 (t' i))
      hadd θ.1 θ.2 (fun i => ⟨hΦ θ.1 (t i), hΦ θ.1 (t' i)⟩)
    refine ⟨r, Eq.trans ?_ hr⟩

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.map_tmul _ _ _ _

end GlobalTheory.AddTensor
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorFullLeftSupportStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.additionTensor_full_left_support : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S), (2 : F) ≠ 0 → ∀ (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∀ π : EA P p 2 →ₗ[F] EA P p 2, TensorProduct.map π (LinearMap.id : EA P p 2 →ₗ[F] EA P p 2) (∑ i, TensorProduct.tmul F (t i) (t' i)) = 0 → π = 0 := by
  first | exact @GlobalTheory.AddTensor.full_left_support | exact GlobalTheory.AddTensor.full_left_support | (intros; apply GlobalTheory.AddTensor.full_left_support <;> assumption)
end
end
