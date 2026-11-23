module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuum
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTestStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTransformingCharacterEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuumStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  first | exact @GlobalTheory.InertVacLagP.exists_lagr_inv_vac | exact GlobalTheory.InertVacLagP.exists_lagr_inv_vac | (intros; apply GlobalTheory.InertVacLagP.exists_lagr_inv_vac <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperator

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacEquiv

theorem acts_schr_of_ref {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    (w : (κ → AF F) × (κ → AF F)) (h₁ : At (evFin F v) w.1) (h₂ : At (evFin F v) w.2)
    (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0) (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x)
    (φ φ₁ : (κ → Fv F v) → ℂ) (h : schr ψ w (tens (evFin F v) φ R) = tens (evFin F v) φ₁ R) :
    Acts (evFin F v) (schr ψ w) φ φ₁ := by
  intro r hr
  funext x
  set y : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (x i)) with hyD
  have hev : ∀ i, evFin F v (y i) = evFin F v (x i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have hy : At (evFin F v) y := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hRy : R y = R 0 := by simpa using hR 0 y hy
  have hRyw : R (y + w.1) = R y := hR y w.1 h₁
  have hrx : r (x + w.1) = r x := hr.1 x w.1 h₁
  have hdot : x ⬝ᵥ w.2 = y ⬝ᵥ w.2 := by
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    have hz : evFin F v (x i - y i) = 0 := by rw [map_sub, hev, sub_self]
    have h0 := congrFun (h₂ (x i - y i) hz) i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    rw [← sub_eq_zero, ← sub_mul, h0]
  have hφ : (fun i => evFin F v ((x + w.1) i)) = (fun i => evFin F v ((y + w.1) i)) := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), hev]
  have hφ₁ : (fun i => evFin F v (x i)) = (fun i => evFin F v (y i)) := by
    funext i
    exact (hev i).symm
  have key := congrFun h y
  simp only [schr, tens] at key ⊢
  rw [hRyw, hRy] at key
  rw [hdot, hrx, hφ₁]
  have hcanc : ψ (y ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * φ (fun i => evFin F v ((x + w.1) i)) =
      φ₁ (fun i => evFin F v (y i)) := by
    apply mul_right_cancel₀ hR0
    rw [hφ, ← key, mul_assoc]
  rw [← mul_assoc, hcanc]

theorem heisInv_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v m C l hl g _ S hS u hu φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hRest⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hsp := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  set u' := GlobalTheory.WeilM.actAB (cA σ) ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u with hu'D
  have hu'eq : u' = mat g * u := by
    simp [hu'D, GlobalTheory.WeilM.actAB, mat]
  obtain ⟨huAt, z, hz⟩ := hu
  have hAt' : At (evFin F v) u' := by
    intro c hc
    rw [hu'eq, ← Matrix.mul_smul, huAt c hc, Matrix.mul_zero]
  have hlag : u' ∈ GlobalTheory.InertVacLag.lagAt v C := ⟨hAt', mat g * z, by rw [hu'eq, hz, Matrix.mul_assoc]⟩
  have hco1 : At (evFin F v) (G.M'.co.e u').1 := by
    intro c hc
    rw [← Prod.smul_fst, ← map_smul, hAt' c hc, map_zero, Prod.fst_zero]
  have hco2 : At (evFin F v) (G.M'.co.e u').2 := by
    intro c hc
    rw [← Prod.smul_snd, ← map_smul, hAt' c hc, map_zero, Prod.snd_zero]
  have hRinv := (hRest 0 (Submodule.zero_mem _)).1
  have hact : Acts (evFin F v) (G.M'.co.rho B.ψ u') (S φ) (S φ₁) := by
    apply acts_schr_of_ref v B.ψ (G.M'.co.e u') hco1 hco2 R hR0 hRinv
    have e1 := (hS φ hφ).2 R (hRest φ hφ)
    have e2 := (hS φ₁ hφ₁).2 R (hRest φ₁ hφ₁)
    have e3 := hA R (hRest φ hφ)
    have e4 := hsp.impl ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u (tens (evFin F v) φ R) (hRest φ hφ).2
    show G.M'.co.rho B.ψ u' (tens (evFin F v) (S φ) R) = tens (evFin F v) (S φ₁) R
    rw [← e1, ← e2, ← e3, hu'D]
    exact e4.symm
  exact hl u' hlag (S φ) (hS φ hφ).1 (S φ₁) (hS φ₁ hφ₁).1 hact

end GlobalTheory.InertVacEquiv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperatorStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  first | exact @GlobalTheory.InertVacEquiv.heisInv_comp | exact GlobalTheory.InertVacEquiv.heisInv_comp | (intros; apply GlobalTheory.InertVacEquiv.heisInv_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOfHeisInv

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

theorem inv_of_heisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = l φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hv m C hC l hl g hg φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin a' × Fin (a + a')) v
  have htadd : ∀ f f' : (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      tens (evFin F v) (f + f') R = tens (evFin F v) f R + tens (evFin F v) f' R := fun f f' => by
    funext x; simp [tens, add_mul]
  have htsmul : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) R = c • tens (evFin F v) f R := fun c f => by
    funext x; simp [tens, mul_assoc]
  let Sop : UA σ G.V'.J → (((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) :=
    fun g =>
    { toFun := fun f t => (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i))
      map_add' := fun f f' => by
        funext t; simp only [htadd, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        funext t; simp only [htsmul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hSop : ∀ g f t, Sop g f t = (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) :=
    fun _ _ _ => rfl
  have huniq : ∀ (T : ((Fin a' × Fin (a + a') → AF F) → ℂ) → (Fin a' × Fin (a + a') → AF F) → ℂ)
      (f f₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ SB _ → Acts (evFin F v) T f f₁ →
      ∀ t, f₁ t = (R 0)⁻¹ * T (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro T f f₁ hf hA t
    rw [hA R (hR f hf)]
    have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
    have h1 : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR f hf).1 0 _ hat
    simp only [tens, h1, GlobalTheory.LatVac.evFin_liftV]
    field_simp
  have hS : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Sop g f ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, 1)) f (Sop g f) := by
    intro g hg f hf
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v g hg
    have e : S₀ f = Sop g f := funext fun t => (huniq _ f _ hf (hS₀ f hf).2 t).trans (hSop g f t).symm
    rw [← e]; exact hS₀ f hf
  obtain ⟨φ₀, hφ₀, hline⟩ := GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test F E σ a' (a + a') G.V' G.W G.M' B.ψ v (hT.base.inert v w hin).2.2 m C hC
  by_cases hz : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), l f = 0
  · rw [hz φ₁ hφ₁, hz φ hφ]
  push_neg at hz
  have hl0 : l φ₀ ≠ 0 := fun h => by
    obtain ⟨f, hf, hne⟩ := hz; exact hne (hline l hl h f hf)
  let c : UA σ G.V'.J → ℂ := fun g => l (Sop g φ₀) / l φ₀
  have hlaw : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ f₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) f f₁ → l f₁ = c g * l f := by
    intro g hg f hf f₁ hf₁ hA
    have hf₁eq : f₁ = Sop g f := funext fun t => (huniq _ f f₁ hf hA t).trans (hSop g f t).symm
    have hE := GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator F E σ B a a' G X om om' hT v m C l hl g hg (Sop g) (hS g hg)
    have hl' : GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ Sop g - c g • l) := by
      intro u hu f hf f₁ hf₁ hA'
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hE u hu f hf f₁ hf₁ hA', hl u hu f hf f₁ hf₁ hA']
    have h0 : (l ∘ₗ Sop g - c g • l) φ₀ = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, c]
      field_simp
      ring
    have h1 := hline _ hl' h0 f hf
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at h1
    rw [hf₁eq]
    linear_combination h1
  have hc := GlobalTheory.T.inert_place_transforming_character_eq_one F E σ B a a' G X om om' hT v w hin hv m C hC l hl hz c hlaw g hg
  rw [hlaw g hg φ hφ φ₁ hφ₁ hA, hc, one_mul]

end GlobalTheory.InertVacLag
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumNotMemAugmentationInertPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertVacLag

theorem vac_not_mem_augAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw hvT hmem
  obtain ⟨C, l, hC, hl, hne⟩ := GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum F E σ B a a' G X om om' hT v w hvw hvT
  have hle : augAt om' v ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, ha, rfl⟩
    show φ₁ - φ ∈ LinearMap.ker l
    rw [LinearMap.mem_ker, map_sub,
      GlobalTheory.InertVacLag.inv_of_heisInv F E σ B a a' G X om om' hT v w hvw hvT _ C hC l hl g hg φ hφ φ₁ hφ₁ ha, sub_self]
  exact hne (hle hmem)

end GlobalTheory.InertVacLag
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumNotMemAugmentationInertPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  first | exact @GlobalTheory.InertVacLag.vac_not_mem_augAt | exact GlobalTheory.InertVacLag.vac_not_mem_augAt | (intros; apply GlobalTheory.InertVacLag.vac_not_mem_augAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOne

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertScalarLeft

theorem scalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT k hk c hc
  by_contra hne
  have hSB := (hTr.geo.hM'.vac v).1
  apply GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place F E σ B a a' G X om om' hTr v w hin hT
  have hmem : c • G.M'.vac v - G.M'.vac v ∈ augAt om' v :=
    Submodule.subset_span ⟨k, hk.1, _, hSB, _, Submodule.smul_mem _ c hSB, hc, rfl⟩
  have h1 : c - 1 ≠ 0 := sub_ne_zero.mpr hne
  have h2 : G.M'.vac v = (c - 1)⁻¹ • (c • G.M'.vac v - G.M'.vac v) := by
    rw [show c • G.M'.vac v - G.M'.vac v = (c - 1) • G.M'.vac v by rw [sub_smul, one_smul],
      smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ hmem

end GlobalTheory.InertScalarLeft
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_vacuumScalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.InertScalarLeft.scalar_eq_one | exact GlobalTheory.InertScalarLeft.scalar_eq_one | (intros; apply GlobalTheory.InertScalarLeft.scalar_eq_one <;> assumption)
end
end
