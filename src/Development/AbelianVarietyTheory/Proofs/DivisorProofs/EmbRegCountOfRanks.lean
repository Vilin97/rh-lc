module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDetermStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbRegOfIsBaseChange

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem embReg_of_isBaseChange : ∀ (K L Γ V W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ : Representation K Γ V) (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K L Γ V W _ _ _ _ _ _ _ _ _ _ _ f hf ρ ρ' hρ H n hE
  obtain ⟨j, hj, hje⟩ := hE
  let eK : MonoidAlgebra K H ≃ₗ[K] (H →₀ K) := MonoidAlgebra.coeffLinearEquiv K
  let eL : MonoidAlgebra L H ≃ₗ[L] (H →₀ L) := MonoidAlgebra.coeffLinearEquiv L
  let m0 : (H →₀ K) →ₗ[K] (H →₀ L) := Finsupp.mapRange.linearMap (Algebra.linearMap K L)
  let φ0 : MonoidAlgebra K H →ₗ[K] MonoidAlgebra L H :=
    (eL.restrictScalars K).symm.toLinearMap ∘ₗ m0 ∘ₗ eK.toLinearMap
  have h0 : IsBaseChange L φ0 := by
    refine (IsBaseChange.iff_of_equiv_comm eK eL (f' := m0) ?_).mpr
      (IsBaseChange.finsuppPow H (IsBaseChange.linearMap K L))
    exact LinearMap.ext fun x => (eL.apply_symm_apply (m0 (eK x))).symm
  have hφ0 : ∀ x, φ0 x = MonoidAlgebra.mapRingHom H (algebraMap K L) x := by
    intro x
    ext g
    simp [φ0, eK, eL, m0]
  let φ : (Fin n → MonoidAlgebra K H) →ₗ[K] (Fin n → MonoidAlgebra L H) := φ0.compLeft (Fin n)
  have hφ : IsBaseChange L φ := IsBaseChange.finitePow (Fin n) h0
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  let j' : W →ₗ[L] (Fin n → MonoidAlgebra L H) := hf.lift (φ ∘ₗ j)
  have hj'f : ∀ v, j' (f v) = φ (j v) := fun v => hf.lift_eq _ v
  let P : (Fin n → MonoidAlgebra L H) →ₗ[L] W := hφ.lift (f ∘ₗ p)
  have hPj : ∀ w, P (j' w) = w := by
    intro w
    have : P ∘ₗ j' = LinearMap.id := hf.algHom_ext _ _ (fun v => by
      rw [LinearMap.comp_apply, hj'f]
      change hφ.lift (f ∘ₗ p) (φ (j v)) = f v
      rw [hφ.lift_eq, LinearMap.comp_apply, ← LinearMap.comp_apply p j, hp, LinearMap.id_apply])
    exact LinearMap.congr_fun this w
  refine ⟨j', fun a b hab => by rw [← hPj a, ← hPj b, hab], ?_⟩
  intro h w i
  have key : (LinearMap.proj i ∘ₗ j' ∘ₗ (ρ' h)) =
      (LinearMap.mulLeft L (MonoidAlgebra.single h (1 : L)) ∘ₗ LinearMap.proj i ∘ₗ j') := by
    refine hf.algHom_ext _ _ (fun v => ?_)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply, hρ, hj'f]
    change φ0 (j (ρ h v) i) = MonoidAlgebra.single h 1 * φ0 (j v i)
    rw [hje, hφ0, hφ0, map_mul, MonoidAlgebra.mapRingHom_single, map_one]
  exact LinearMap.congr_fun key w

end GlobalTheory.BadCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfCharacterTw

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

noncomputable def twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    MonoidAlgebra K H →ₐ[K] MonoidAlgebra K H :=
  MonoidAlgebra.lift K (MonoidAlgebra K H) H
    { toFun := fun h => MonoidAlgebra.single h (((χ (h : Γ))⁻¹ : Kˣ) : K)
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := by
        intro a b
        simp [MonoidAlgebra.single_mul_single, mul_comm] }

theorem twistAlg_single {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) (h : H) (c : K) :
    twistAlg H χ (MonoidAlgebra.single h c) = MonoidAlgebra.single h (c * (((χ (h : Γ))⁻¹ : Kˣ) : K)) := by
  simp [twistAlg, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single]

theorem twistAlg_inv_twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ)
    (x : MonoidAlgebra K H) : twistAlg H χ⁻¹ (twistAlg H χ x) = x := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    simp only [MonoidAlgebra.of_apply, twistAlg_single]
    congr 1
    simp
  | add x y hx hy => simp [map_add (f := _), hx, hy]
  | smul r x hx => simp [map_smul, hx]

theorem twistAlg_injective {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    Function.Injective (twistAlg H χ) := fun x y hxy => by
  rw [← twistAlg_inv_twistAlg H χ x, ← twistAlg_inv_twistAlg H χ y, hxy]

theorem embReg_twist : ∀ (K Γ V : Type) [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ ρ' : Representation K Γ V)
    (χ : Γ →* Kˣ), (∀ g v, ρ' g v = ((χ g : Kˣ) : K) • ρ g v) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K Γ V _ _ _ _ ρ ρ' χ hρ H n ⟨j, hj, hjeq⟩
  refine ⟨LinearMap.pi fun i => (twistAlg H χ).toLinearMap.comp ((LinearMap.proj i).comp j), ?_, ?_⟩
  · intro v w hvw
    apply hj
    funext i
    have := congrFun hvw i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply] at this
    exact twistAlg_injective H χ this
  · intro h v i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply]
    rw [hρ, map_smul, Pi.smul_apply, hjeq, map_smul, map_mul, twistAlg_single, ← smul_mul_assoc,
      MonoidAlgebra.smul_single]
    congr 2
    simp

end GlobalTheory.BadCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfCharacterTwStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_of_characterTwist : ∀ (K Γ V : Type) [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ ρ' : Representation K Γ V) (χ : Γ →* Kˣ), (∀ g v, ρ' g v = ((χ g : Kˣ) : K) • ρ g v) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  first | exact @GlobalTheory.BadCount.embReg_twist | exact GlobalTheory.BadCount.embReg_twist | (intros; apply GlobalTheory.BadCount.embReg_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankCharacterSpaceBaseChange

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
open scoped TensorProduct

namespace GlobalTheory.BadCount

theorem tmul_one_mem_nonZeroDivisors_of_field {K L R : Type} [Field K] [Field L] [Algebra K L]
    [CommRing R] [Algebra K R] (d : R) (hd : d ∈ nonZeroDivisors R) :
    ((1 : L) ⊗ₜ[K] d) ∈ nonZeroDivisors (L ⊗[K] R) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have hinj : Function.Injective ((LinearMap.mulRight K d).lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b hab => by
      have : (a - b) * d = 0 := by simpa [sub_mul, sub_eq_zero] using hab
      exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hd) _ this))
  have heq : ∀ y : L ⊗[K] R, (LinearMap.mulRight K d).lTensor L y = y * ((1 : L) ⊗ₜ[K] d) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb => simp [map_add (f := _), add_mul, ha, hb]
  apply hinj
  rw [heq, hx, map_zero]

theorem finrank_le_card_mul_finrank_eig_baseChange : ∀ (K L Γ R W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V : Submodule K R) [FiniteDimensional K V] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ Vm, x * act h u ∈ V) → ∀ [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ lam : H →* Lˣ, finrank K Vm ≤ Nat.card H * finrank L (eig ρ' H lam) := by
  intro K L Γ R W _ _ _ _ _ _ _ act H _ _ u hdet Vm V _ ρ hρ hVm _ _ _ _ f hf ρ' hρ' lam
  classical
  let actL : Γ → (L ⊗[K] R →ₐ[L] L ⊗[K] R) := fun g => Algebra.TensorProduct.map (AlgHom.id L L) (act g)
  have actL_tmul : ∀ g (l : L) (r : R), actL g (l ⊗ₜ r) = l ⊗ₜ act g r := fun g l r => by
    simp [actL, Algebra.TensorProduct.map_tmul]
  have actL_mul : ∀ g g' x, actL (g * g') x = actL g (actL g' x) := by
    intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp only [actL_tmul, map_mul, AlgHom.mul_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have actL_one : ∀ x, actL 1 x = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp only [actL_tmul, map_one, AlgHom.one_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have inj_of : ∀ {M : Type} [AddCommGroup M] [Module K M] (g : M →ₗ[K] R), Function.Injective g →
      Function.Injective (g.baseChange L) := by
    intro M _ _ g hg
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap g hg
  let ιV : L ⊗[K] V →ₗ[L] L ⊗[K] R := V.subtype.baseChange L
  let ιm : L ⊗[K] Vm →ₗ[L] L ⊗[K] R := Vm.subtype.baseChange L
  let A : H → (Vm →ₗ[K] V) := fun h =>
    { toFun := fun x => ⟨(x : R) * act h u, hVm h x x.2⟩
      map_add' := by intro x y; ext; simp [add_mul]
      map_smul' := by intro c x; ext; simp [smul_mul_assoc] }
  have hA : ∀ h y, ιV ((A h).baseChange L y) = ιm y * ((1 : L) ⊗ₜ act h u) := by
    intro h y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l x => simp [ιV, ιm, A, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  let e := hf.equiv
  let j : W →ₗ[L] L ⊗[K] R := ιV ∘ₗ e.symm.toLinearMap
  have hj : ∀ (g : Γ) w, j (ρ' g w) = actL g (j w) := by
    intro g w
    obtain ⟨z, rfl⟩ := e.surjective w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l v =>
      have h1 : e (l ⊗ₜ v) = l • f v := hf.equiv_tmul l v
      have h2 : e (l ⊗ₜ ρ g v) = l • f (ρ g v) := hf.equiv_tmul l _
      simp only [j, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h1, map_smul, hρ', ← h2, ← h1, e.symm_apply_apply, e.symm_apply_apply]
      simp [ιV, actL_tmul, hρ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hje : ∀ z, j (e z) = ιV z := fun z => by simp [j]
  let T : W →ₗ[L] W := ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • ρ' g
  have hT : ∀ w, T w ∈ eig ρ' H lam := by
    intro w
    rw [mem_eig]
    intro k

    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ (fun g => ?_)
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul ρ', Module.End.mul_apply, smul_smul, map_mul lam]
    congr 1
    rw [← Units.val_mul, mul_inv, mul_inv_cancel_left]
  have hjT : ∀ w, j (T w) = ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (j w) := by
    intro w

    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hj]
  let Ψ : L ⊗[K] Vm →ₗ[L] (H → eig ρ' H lam) :=
    LinearMap.pi fun h => LinearMap.codRestrict (eig ρ' H lam) (T ∘ₗ e.toLinearMap ∘ₗ (A h).baseChange L)
      (fun y => hT _)
  have hΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have P : ∀ h : H, ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (ιm y * ((1 : L) ⊗ₜ act h u)) = 0 := by
      intro h
      have h0 := congrArg Subtype.val (congrFun hy h)
      simp only [Ψ, LinearMap.pi_apply, LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Pi.zero_apply, ZeroMemClass.coe_zero] at h0
      have h1 := congrArg j h0
      rw [hjT, hje, hA, map_zero] at h1
      exact h1
    have key := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H L (L ⊗[K] R)
      (fun h => actL ((h : Γ)⁻¹)) (fun x => by simp [actL_one])
      (fun h h' x => by simp [mul_inv_rev, actL_mul]) lam⁻¹ ((1 : L) ⊗ₜ u) ?_
    · have hy0 : ιm y = 0 := by
        refine key.2.1 (ιm y) (fun h' => ?_)
        rw [← P h'⁻¹]
        refine Fintype.sum_equiv (Equiv.inv H) _ _ (fun g => ?_)
        simp [actL_tmul]
      exact inj_of _ Vm.injective_subtype (by rw [hy0, map_zero])
    · have hM : (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)) =
          (Algebra.TensorProduct.includeRight : R →ₐ[K] L ⊗[K] R).mapMatrix
            ((Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u)).submatrix (Equiv.inv H) (Equiv.inv H)) := by
        ext h g
        simp [actL_tmul, mul_inv_rev, Function.swap]
      show (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)).det ∈ _
      rw [hM, ← AlgHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose,
        Algebra.TensorProduct.includeRight_apply]
      exact tmul_one_mem_nonZeroDivisors_of_field _ hdet
  have hfinW : Module.Finite L W := Module.Finite.equiv e
  have h1 : finrank K Vm = finrank L (L ⊗[K] Vm) := (Module.finrank_baseChange).symm
  rw [h1]
  refine (LinearMap.finrank_le_finrank_of_injective hΨ).trans (le_of_eq ?_)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end GlobalTheory.BadCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankCharacterSpaceBaseChangeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.finrank_le_card_mul_finrank_characterSpace_baseChange : ∀ (K L Γ R W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V : Submodule K R) [FiniteDimensional K V] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ Vm, x * act h u ∈ V) → ∀ [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ lam : H →* Lˣ, finrank K Vm ≤ Nat.card H * finrank L (eig ρ' H lam) := by
  first | exact @GlobalTheory.BadCount.finrank_le_card_mul_finrank_eig_baseChange | exact GlobalTheory.BadCount.finrank_le_card_mul_finrank_eig_baseChange | (intros; apply GlobalTheory.BadCount.finrank_le_card_mul_finrank_eig_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbRegCountOfRanks

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

def untwist {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ Γ W) (χ : Γ →* ℂˣ) :
    Representation ℂ Γ W where
  toFun g := (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ' g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, mul_inv_rev, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply,
      LinearMap.map_smul, smul_smul]
    ring_nf

theorem untwist_apply {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ Γ W)
    (χ : Γ →* ℂˣ) (g : Γ) (w : W) : untwist ρ' χ g w = (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ' g w := rfl

theorem embReg_count_of_ranks : ∀ (K Γ R W : Type) [Field K] [Algebra K ℂ] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (Hb H : Subgroup Γ) [Fintype Hb] [DecidableEq Hb] [Fintype H] [DecidableEq H] (u0 u : R), (Matrix.of fun h g : Hb => act ((h : Γ) * g) u0).det ∈ nonZeroDivisors R → (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V V1 V2 : Submodule K R) [FiniteDimensional K V] [FiniteDimensional K V2] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : Hb, ∀ x ∈ Vm, x * act h u0 ∈ V) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V1) → (∀ h : H, ∀ x ∈ V1, act h x ∈ V1) → (∀ h : H, ∀ x ∈ V1, x * act h u ∈ V2) → ∀ c : ℝ, 0 ≤ c → (finrank K V2 : ℝ) ≤ c * finrank K Vm → ∀ [AddCommGroup W] [Module K W] [Module ℂ W] [IsScalarTower K ℂ W] (f : V →ₗ[K] W), IsBaseChange ℂ f → ∀ (ρ' : Representation ℂ Γ W) (χ : Γ →* ℂˣ), (∀ g v, ρ' g (f v) = ((χ g : ℂˣ) : ℂ) • f (ρ g v)) → ∀ lam : Hb →* ℂˣ, ∃ n : ℕ, EmbReg ρ' H n ∧ (n : ℝ) * Nat.card H ≤ c * Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by
  intro K Γ R W _ _ _ _ _ _ act Hb H _ _ _ _ u0 u hu0 hu Vm V V1 V2 _ _ ρ hρ hVm hV hV1 hV2 c hc hcr _ _ _ _ f hf ρ' χ hρ' lam
  obtain ⟨n, hn, hnle⟩ := GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant K Γ R act H u hu V V1 V2 ρ hρ hV hV1 hV2
  have hf'' : ∀ g v, untwist ρ' χ g (f v) = f (ρ g v) := by
    intro g v
    rw [untwist_apply, hρ', smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hn'' : EmbReg (untwist ρ' χ) H n :=
    embReg_of_isBaseChange K ℂ Γ V W f hf ρ (untwist ρ' χ) hf'' H n hn
  have hn' : EmbReg ρ' H n := by
    refine GlobalTheory.T.embedsInRegularRepresentationCopies_of_characterTwist ℂ Γ W (untwist ρ' χ) ρ' χ ?_ H n hn''
    intro g v
    rw [untwist_apply, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let lam' : Hb →* ℂˣ := lam * (χ.comp Hb.subtype)⁻¹
  have heig : eig ρ' Hb lam = eig (untwist ρ' χ) Hb lam' := by
    ext v
    rw [mem_eig, mem_eig]
    refine forall_congr' fun h => ?_
    rw [untwist_apply]
    simp only [lam', MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Units.val_mul]
    constructor
    · intro e; rw [e, smul_smul, mul_comm]
    · intro e
      have := congrArg (fun w => ((χ (h : Γ) : ℂˣ) : ℂ) • w) e
      simp only [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] at this
      rw [this]; congr 1
      rw [mul_left_comm, mul_inv_cancel, mul_one]
  have hlow := GlobalTheory.T.finrank_le_card_mul_finrank_characterSpace_baseChange K ℂ Γ R W act Hb u0 hu0 Vm V ρ hρ hVm f hf (untwist ρ' χ) hf'' lam'
  rw [← heig] at hlow
  refine ⟨n, hn', ?_⟩
  have h1 : ((n * Nat.card H : ℕ) : ℝ) ≤ finrank K V2 := by exact_mod_cast hnle
  have h2 : (finrank K Vm : ℝ) ≤ Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by exact_mod_cast hlow
  push_cast at h1
  calc (n : ℝ) * Nat.card H ≤ finrank K V2 := h1
    _ ≤ c * finrank K Vm := hcr
    _ ≤ c * (Nat.card Hb * finrank ℂ (eig ρ' Hb lam)) := mul_le_mul_of_nonneg_left h2 hc
    _ = c * Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by ring

end GlobalTheory.BadCount
end
end
