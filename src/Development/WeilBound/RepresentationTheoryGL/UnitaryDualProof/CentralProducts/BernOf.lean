module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.LeviScalars.EmbScalarMemLevi
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.PositiveProducts.PosProdOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.SubquotientBounds.LeOfSubsingletonSubQuot
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.UnitarisableHypotheses.NormEqOneOfUnitarisable

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.CentralGenerators.CentralSubGen

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.CS

variable {k : Type} [Field k]

theorem sc_one (n : ℕ) : sc n (1 : kˣ) = 1 := map_one _

theorem sc_mul (n : ℕ) (y z : kˣ) : sc n (y * z) = sc n y * sc n z := map_mul _ _ _

theorem sc_comm (n : ℕ) (y : kˣ) (g : GL (Fin n) k) : sc n y * g = g * sc n y := by
  apply Units.ext
  have h : ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.scalar (Fin n) (y : k) := rfl
  show ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) =
    (g : Matrix (Fin n) (Fin n) k) * ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  rw [h]
  exact (Matrix.scalar_commute (y : k) (fun r => Commute.all _ _) _).eq

theorem rho_sc_comm {n : ℕ} (A : GRep k n) (y : kˣ) (g : GL (Fin n) k) (v : A.V) :
    A.ρ (sc n y) (A.ρ g v) = A.ρ g (A.ρ (sc n y) v) := by
  rw [← Module.End.mul_apply, ← map_mul, sc_comm, map_mul, Module.End.mul_apply]

theorem centralSub_gen [TopologicalSpace k] : CentralSub k := by
  classical
  intro n A _hs hLF x c a ha hxa
  obtain ⟨U, hUf, haU, hUinv⟩ := hLF a
  have := hUf
  let Good : Submodule ℂ A.V → Prop := fun S => S ≤ U ∧ S ≠ ⊥ ∧
    (∀ y : kˣ, ∀ s ∈ S, A.ρ (sc n y) s ∈ S) ∧ ∀ s ∈ S, A.ρ (sc n x) s = c • s
  have hex : ∃ d : ℕ, ∃ S : Submodule ℂ A.V, Good S ∧ Module.finrank ℂ S = d := by
    refine ⟨_, U ⊓ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id), ⟨inf_le_left, ?_, ?_, ?_⟩, rfl⟩
    · intro h
      apply ha
      have hm : a ∈ U ⊓ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id) :=
        ⟨haU, by simp [LinearMap.mem_ker, hxa]⟩
      rw [h] at hm
      exact (Submodule.mem_bot ℂ).1 hm
    · rintro y s ⟨hsU, hsk⟩
      refine ⟨hUinv y s hsU, ?_⟩
      have hsk' : A.ρ (sc n x) s = c • s := by
        simpa [LinearMap.mem_ker, sub_eq_zero] using hsk
      show A.ρ (sc n y) s ∈ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, rho_sc_comm A x (sc n y) s, hsk', map_smul]
      simp
    · rintro s ⟨_, hsk⟩
      simpa [LinearMap.mem_ker, sub_eq_zero] using hsk
  obtain ⟨S, ⟨hSU, hS0, hSinv, hSx⟩, hSd⟩ := Nat.find_spec hex
  have hmin : ∀ S' : Submodule ℂ A.V, Good S' → Module.finrank ℂ S ≤ Module.finrank ℂ S' := by
    intro S' hS'
    rw [hSd]
    exact Nat.find_min' hex ⟨S', hS', rfl⟩
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  have hscal : ∀ y : kˣ, ∃ μ : ℂ, ∀ s ∈ S, A.ρ (sc n y) s = μ • s := by
    intro y
    let f : Module.End ℂ S := (A.ρ (sc n y)).restrict (hSinv y)
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    refine ⟨μ, ?_⟩
    have hfw : A.ρ (sc n y) (w : A.V) = μ • (w : A.V) := congrArg Subtype.val hw.apply_eq_smul
    let S' : Submodule ℂ A.V := S ⊓ LinearMap.ker (A.ρ (sc n y) - μ • LinearMap.id)
    have hmem : ∀ s, s ∈ S' ↔ s ∈ S ∧ A.ρ (sc n y) s = μ • s := by
      intro s
      simp [S', Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hgood : Good S' := by
      refine ⟨inf_le_left.trans hSU, ?_, ?_, ?_⟩
      · intro h
        have hw' : (w : A.V) ∈ S' := (hmem _).2 ⟨w.2, hfw⟩
        rw [h] at hw'
        exact hw.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hw'))
      · intro y' s hs
        obtain ⟨hsS, hsy⟩ := (hmem s).1 hs
        refine (hmem _).2 ⟨hSinv y' s hsS, ?_⟩
        rw [rho_sc_comm A y (sc n y') s, hsy, map_smul]
      · intro s hs
        exact hSx s ((hmem s).1 hs).1
    have hEq : S' = S := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin S' hgood)
    intro s hs
    rw [← hEq] at hs
    exact ((hmem s).1 hs).2
  choose lam hlam using hscal
  obtain ⟨a', ha'S, ha'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have key : ∀ μ ν : ℂ, μ • a' = ν • a' → μ = ν := fun μ ν h => smul_left_injective ℂ ha'0 h
  have hlam1 : lam 1 = 1 := by
    apply key
    rw [← hlam 1 a' ha'S, sc_one, map_one, Module.End.one_apply, one_smul]
  have hlammul : ∀ y z : kˣ, lam (y * z) = lam y * lam z := by
    intro y z
    apply key
    rw [← hlam (y * z) a' ha'S, sc_mul, map_mul, Module.End.mul_apply, hlam z a' ha'S, map_smul,
      hlam y a' ha'S, smul_smul, mul_comm]
  let f : kˣ →* ℂ := { toFun := lam, map_one' := hlam1, map_mul' := hlammul }
  let Wm : Submodule ℂ A.V :=
    { carrier := {v | ∀ y : kˣ, A.ρ (sc n y) v = lam y • v}
      add_mem' := by
        intro u v hu hv y
        have hu' : ∀ y : kˣ, A.ρ (sc n y) u = lam y • u := hu
        have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
        show A.ρ (sc n y) (u + v) = lam y • (u + v)
        rw [map_add (f := _), hu' y, hv' y, smul_add]
      zero_mem' := by
        intro y
        show A.ρ (sc n y) 0 = lam y • (0 : A.V)
        rw [map_zero, smul_zero]
      smul_mem' := by
        intro r v hv y
        have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
        show A.ρ (sc n y) (r • v) = lam y • (r • v)
        rw [map_smul, hv' y, smul_comm] }
  let W : Subrepresentation A.ρ := ⟨Wm, fun g v hv y => by
    have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
    show A.ρ (sc n y) (A.ρ g v) = lam y • A.ρ g v
    rw [rho_sc_comm, hv' y, map_smul]⟩
  have ha'W : a' ∈ W.toSubmodule := fun y => hlam y a' ha'S
  refine ⟨W, f.toHomUnits, ?_, ?_, ?_⟩
  · intro h
    apply ha'0
    have h2 : W.toSubmodule = (⊥ : Subrepresentation A.ρ).toSubmodule := congrArg _ h
    have h3 : a' ∈ (⊥ : Subrepresentation A.ρ).toSubmodule := h2 ▸ ha'W
    exact (Submodule.mem_bot ℂ).1 h3
  · intro z v
    apply Subtype.ext
    show A.ρ (sc n z) v.1 = ((f.toHomUnits z : ℂˣ) : ℂ) • v.1
    rw [MonoidHom.coe_toHomUnits]
    exact v.2 z
  · show ((f.toHomUnits x : ℂˣ) : ℂ) = c
    rw [MonoidHom.coe_toHomUnits]
    exact (key _ _ ((hlam x a' ha'S).symm.trans (hSx a' ha'S))).trans rfl

theorem centralSub (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CentralSub k :=
  centralSub_gen

end PositivityTheory.RgUd.Prod.CS
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.CentralSub

section

@[expose] public section

namespace PositivityTheory.RgUd.Prod.CSel

theorem centralSub (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CentralSub k := PositivityTheory.RgUd.Prod.CS.centralSub k

end PositivityTheory.RgUd.Prod.CSel
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.EigenInjectivity.SubInjective

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace PositivityTheory.RgUd.Prod.Eig

section Lin

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem sub_injective (f : Module.End ℂ V) (α : ℂ) (h : ∀ a : V, f a = α • a → a = 0) :
    Function.Injective (f - α • (LinearMap.id : V →ₗ[ℂ] V)) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => h a ?_
  simpa [sub_eq_zero] using ha

theorem exists_fin (S : Module.End ℂ V) (T : Module.End ℂ W)
    (hA : ∀ a : V, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ a ∈ U ∧ ∀ u ∈ U, S u ∈ U)
    (hB : ∀ b : W, ∃ U : Submodule ℂ W, FiniteDimensional ℂ U ∧ b ∈ U ∧ ∀ u ∈ U, T u ∈ U)
    (y : V ⊗[ℂ] W) : ∃ (U₁ : Submodule ℂ V) (U₂ : Submodule ℂ W), FiniteDimensional ℂ U₁ ∧
      FiniteDimensional ℂ U₂ ∧ (∀ u ∈ U₁, S u ∈ U₁) ∧ (∀ u ∈ U₂, T u ∈ U₂) ∧
      y ∈ LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨⊥, ⊥, inferInstance, inferInstance, by simp, by simp, zero_mem _⟩
  | tmul a b =>
    obtain ⟨U₁, h₁, ha, s₁⟩ := hA a
    obtain ⟨U₂, h₂, hb, s₂⟩ := hB b
    exact ⟨U₁, U₂, h₁, h₂, s₁, s₂, ⟨⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩, by simp⟩⟩
  | add y z hy hz =>
    obtain ⟨U₁, U₂, h₁, h₂, s₁, s₂, my⟩ := hy
    obtain ⟨U₁', U₂', h₁', h₂', s₁', s₂', mz⟩ := hz
    have st : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (F : Module.End ℂ M) (P Q : Submodule ℂ M),
        (∀ u ∈ P, F u ∈ P) → (∀ u ∈ Q, F u ∈ Q) → ∀ u ∈ P ⊔ Q, F u ∈ P ⊔ Q := by
      intro M _ _ F P Q hP hQ u hu
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hu
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hP p hp) (hQ q hq)
    have mono : ∀ (P P' : Submodule ℂ V) (Q Q' : Submodule ℂ W), P ≤ P' → Q ≤ Q' →
        LinearMap.range (TensorProduct.map P.subtype Q.subtype) ≤
          LinearMap.range (TensorProduct.map P'.subtype Q'.subtype) := by
      intro P P' Q Q' hP hQ
      have : TensorProduct.map P.subtype Q.subtype =
          TensorProduct.map P'.subtype Q'.subtype ∘ₗ
            TensorProduct.map (Submodule.inclusion hP) (Submodule.inclusion hQ) := by
        rw [← TensorProduct.map_comp]; rfl
      rw [this]
      exact LinearMap.range_comp_le_range _ _
    exact ⟨U₁ ⊔ U₁', U₂ ⊔ U₂', inferInstance, inferInstance, st S _ _ s₁ s₁', st T _ _ s₂ s₂',
      add_mem (mono _ _ _ _ le_sup_left le_sup_left my) (mono _ _ _ _ le_sup_right le_sup_right mz)⟩

theorem tensor_eig (S : Module.End ℂ V) (T : Module.End ℂ W) (hS : Function.Injective S)
    (U₁ : Submodule ℂ V) (U₂ : Submodule ℂ W) [FiniteDimensional ℂ U₁] [FiniteDimensional ℂ U₂]
    (h₁ : ∀ u ∈ U₁, S u ∈ U₁)
    (y : V ⊗[ℂ] W) (hy : y ∈ LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype))
    (hy0 : y ≠ 0) (c : ℂ) (hc : TensorProduct.map S T y = c • y) :
    ∃ α β : ℂ, c = α * β ∧ (∃ a : V, a ≠ 0 ∧ S a = α • a) ∧ ∃ b : W, b ≠ 0 ∧ T b = β • b := by
  set R := LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype) with hR
  set S' := LinearMap.rTensor W S with hS'
  set T' := LinearMap.lTensor V T with hT'
  set P := TensorProduct.map S T with hP
  have hPST : ∀ z, P z = S' (T' z) := fun z => by
    rw [hP, hS', hT', ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
  have hPS : ∀ z, P (S' z) = S' (P z) := fun z => by
    have : P ∘ₗ S' = S' ∘ₗ P := TensorProduct.ext' fun a b => by simp [hP, hS']
    exact LinearMap.congr_fun this z
  have hRS : ∀ z ∈ R, S' z ∈ R := by
    rintro _ ⟨z, rfl⟩
    refine ⟨TensorProduct.map (S.restrict h₁) LinearMap.id z, ?_⟩
    have : TensorProduct.map U₁.subtype U₂.subtype ∘ₗ TensorProduct.map (S.restrict h₁) LinearMap.id =
        S' ∘ₗ TensorProduct.map U₁.subtype U₂.subtype :=
      TensorProduct.ext' fun a b => by simp [hS', LinearMap.restrict_apply]
    exact LinearMap.congr_fun this z
  let E : Submodule ℂ (V ⊗[ℂ] W) := R ⊓ LinearMap.ker (P - c • LinearMap.id)
  have memE : ∀ z, z ∈ E ↔ z ∈ R ∧ P z = c • z := fun z => by
    simp [E, sub_eq_zero]
  have hES : ∀ z ∈ E, S' z ∈ E := fun z hz => by
    rw [memE] at hz ⊢
    exact ⟨hRS z hz.1, by rw [hPS, hz.2, map_smul]⟩
  have : FiniteDimensional ℂ R := LinearMap.finiteDimensional_range _
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  have hyE : y ∈ E := (memE y).2 ⟨hy, hc⟩
  have : Nontrivial E := ⟨⟨⟨y, hyE⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (S'.restrict hES)
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hv1 : S' v.1 = α • v.1 := by
    have := Module.End.mem_eigenspace_iff.1 hv.1
    exact congrArg Subtype.val this
  have hv0 : v.1 ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hv2 : P v.1 = c • v.1 := ((memE _).1 v.2).2
  have hS'inj : Function.Injective S' := Module.Flat.rTensor_preserves_injective_linearMap S hS
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hv0 (hS'inj (by rw [hv1, zero_smul, map_zero]))
  have hT1 : T' v.1 = (c / α) • v.1 := by
    apply hS'inj
    rw [← hPST, hv2, map_smul, hv1, smul_smul, div_mul_cancel₀ _ hα0]
  refine ⟨α, c / α, (mul_div_cancel₀ _ hα0).symm, ?_, ?_⟩
  · by_contra hno
    push Not at hno
    have hinj := sub_injective S α fun a ha => by
      by_contra h0; exact hno a h0 ha
    have h3 := Module.Flat.rTensor_preserves_injective_linearMap (M := W) _ hinj
    have h4 : LinearMap.rTensor W (S - α • LinearMap.id) v.1 = 0 := by
      rw [LinearMap.rTensor_sub, LinearMap.rTensor_smul, LinearMap.rTensor_id, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, ← hS', hv1, sub_self]
    exact hv0 (h3 (by rw [h4, map_zero]))
  · by_contra hno
    push Not at hno
    have hinj := sub_injective T (c / α) fun b hb => by
      by_contra h0; exact hno b h0 hb
    have h3 := Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ hinj
    have h4 : LinearMap.lTensor V (T - (c / α) • LinearMap.id) v.1 = 0 := by
      rw [LinearMap.lTensor_sub, LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, ← hT', hT1, sub_self]
    exact hv0 (h3 (by rw [h4, map_zero]))

end Lin

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eigProd : EigProd k := by
  intro r t A B _ _ hA hB x c f hf hfc
  have hinj : ∀ {n : ℕ} (C : GRep k n), Function.Injective (C.ρ (sc n x)) := fun {n} C => by
    refine Function.LeftInverse.injective (g := C.ρ (sc n x⁻¹)) fun a => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]
  have h1 : leviEmb k (two (stdSum (rfl : r + t = r + t)))
      (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) = sc (r + t) x := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := (two (stdSum (rfl : r + t = r + t))).surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := (two (stdSum (rfl : r + t = r + t))).surjective j
    by_cases hb : b = b'
    · subst hb
      simp only [leviEmb, blockDiagonal'_apply_eq, Equiv.symm_apply_apply, Matrix.reindex_apply, Matrix.submatrix_apply, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · simp only [leviEmb, blockDiagonal'_apply, Equiv.symm_apply_apply, Matrix.reindex_apply, Matrix.submatrix_apply, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk, hb, ↓reduceDIte]
      simp [hb]
  obtain ⟨g, hg⟩ : ∃ g, f.1.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (Subtype.ext (funext h)))
  have hc : f.1.1 (g * sc (r + t) x) = c • f.1.1 g := congrArg (fun F : (A.prod B).V => F.1.1 g) hfc
  have hcomm : g * sc (r + t) x = sc (r + t) x * g := by
    ext i j
    simp [mul_comm]
  let e := two (stdSum (rfl : r + t = r + t))
  let d : Levi k (Two (Fin r) (Fin t)) := fun a => GeneralLinearGroup.scalar _ x
  have hp : leviEmb k e d ∈ parab k e := by
    apply mem_parab_iff.2
    intro a b i j hab
    simp [leviEmb, blockDiagonal'_apply, hab.ne']
  have hproj : leviProj k e ⟨leviEmb k e d, hp⟩ = d := by
    funext a
    ext i j
    simp [leviProj_apply, leviEmb, blockDiagonal'_apply_eq]
  have h5 := parInd_law e (piTensor (twoRep A.ρ B.ρ)) f ⟨leviEmb k e d, hp⟩ g
  rw [hproj, GlobalTheory.CentralSupport.deltaHalf_scalar] at h5
  have h6 : piTensor (twoRep A.ρ B.ρ) (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) (f.1.1 g) =
      c • f.1.1 g := by
    have h7 : f.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t)))
        (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) * g) = c • f.1.1 g := by
      rw [h1, ← hcomm]; exact hc
    rw [h5] at h7
    simpa using h7
  have htr : ∀ z, Exponents.boolTensorEquiv (X := TwoT A.V B.V)
      (piTensor (twoRep A.ρ B.ρ) (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) z) =
      TensorProduct.map (A.ρ (sc r x)) (B.ρ (sc t x)) (Exponents.boolTensorEquiv (X := TwoT A.V B.V) z) := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | add z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw, map_add (f := _), map_add (f := _)]
    | smul_tprod s z =>
      rw [map_smul, map_smul, map_smul, map_smul, piTensor_tprod, Exponents.boolTensorEquiv_tprod,
        Exponents.boolTensorEquiv_tprod, TensorProduct.map_tmul]
      rfl
  set y := Exponents.boolTensorEquiv (X := TwoT A.V B.V) (f.1.1 g) with hy
  have hy0 : y ≠ 0 := by
    rw [hy]; exact (LinearEquiv.map_ne_zero_iff _).2 hg
  have hyc : TensorProduct.map (A.ρ (sc r x)) (B.ρ (sc t x)) y = c • y := by
    rw [hy, ← htr, h6, map_smul]
  obtain ⟨U₁, U₂, fd₁, fd₂, s₁, -, hmem⟩ := exists_fin (A.ρ (sc r x)) (B.ρ (sc t x))
    (fun a => by obtain ⟨U, h, ha, hs⟩ := hA a; exact ⟨U, h, ha, fun u hu => hs x u hu⟩)
    (fun b => by obtain ⟨U, h, hb, hs⟩ := hB b; exact ⟨U, h, hb, fun u hu => hs x u hu⟩) y
  exact tensor_eig _ _ (hinj A) U₁ U₂ s₁ y hmem hy0 c hyc


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem eigFilt : EigFilt k := by
  intro n V _ _ ρ ℓ F hF h0 hℓ x c v hv hvc
  classical
  have hex : ∃ j, v ∉ (F (j + 1)).toSubmodule := ⟨ℓ, by
    rw [hℓ]
    intro h
    exact hv ((Submodule.mem_bot ℂ).1 h)⟩
  set j := Nat.find hex with hjdef
  have hj : v ∉ (F (j + 1)).toSubmodule := Nat.find_spec hex
  have hvj : v ∈ (F j).toSubmodule := by
    rcases hjj : j with _ | j'
    · rw [h0]; exact Submodule.mem_top
    · have := Nat.find_min hex (show j' < Nat.find hex by omega)
      push Not at this
      exact this
  refine ⟨j, Nat.find_min' hex (show v ∉ (F (ℓ + 1)).toSubmodule from ?_), ?_⟩
  · rw [hℓ]; intro h; exact hv ((Submodule.mem_bot ℂ).1 h)
  refine ⟨Submodule.Quotient.mk ⟨v, hvj⟩, fun h => hj (Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h)), ?_⟩
  rw [← Submodule.Quotient.mk_smul]
  show Submodule.Quotient.mk (⟨ρ (sc n x) v, _⟩ : (F j).toSubmodule) = _
  congr 1
  exact Subtype.ext hvc

end PositivityTheory.RgUd.Prod.Eig
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.BernOf

section

@[expose] public section

noncomputable section

namespace PositivityTheory.RgUd.Prod.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bern_of (hT : DerivTop k) (hP : DerivPos k) (hL : GlobalTheory.RgGu.Leib.LeibnizOrd k) : BernAt k :=
  Asm.bern_of_parts k hT
    (Pos.posProd_of k hT hP hL (LF.lfDeriv k) (CSel.centralSub k) (Eig.eigProd k) (Eig.eigFilt k))
    (Pos2.topProd_of k hT hP hL (LF.lfDeriv k) (CSel.centralSub k) (Eig.eigProd k) (Eig.eigFilt k))

end PositivityTheory.RgUd.Prod.Final
end
end
end
