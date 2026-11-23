module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariant
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEvaluationBijectiveSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRightStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorHaarNormProportionalStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblESymmToLinearMap

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem elim_dot' {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

section Coord

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) w w' = hTens c JA JB w.toCols₁ w'.toCols₁ - hTens c JA JB w.toCols₂ w'.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.toCols₁_apply, Matrix.toCols₂_apply, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [← sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (w w' : Matrix α (β ⊕ β) E) :
    symp c ξ JA (dbl JB) w w' = symp c ξ JA JB w.toCols₁ w'.toCols₁ - symp c ξ JA JB w.toCols₂ w'.toCols₂ := by
  unfold symp
  rw [hTens_dbl, mul_sub, map_sub]

variable [Invertible (2 : R)] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

def dblCo (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun w => (Sum.elim (d.e w.toCols₁).1 (d.e w.toCols₂).1, Sum.elim (d.e w.toCols₁).2 (-(d.e w.toCols₂).2))
      map_add' := fun w w' => by
        have h1 : (w + w').toCols₁ = w.toCols₁ + w'.toCols₁ := by ext; simp
        have h2 : (w + w').toCols₂ = w.toCols₂ + w'.toCols₂ := by ext; simp
        rw [h1, h2, map_add (f := _), map_add (f := _)]
        ext k <;> cases k <;> simp [add_comm]
      map_smul' := fun a w => by
        have h1 : (a • w).toCols₁ = a • w.toCols₁ := by ext; simp
        have h2 : (a • w).toCols₂ = a • w.toCols₂ := by ext; simp
        rw [h1, h2, map_smul, map_smul]
        ext k <;> cases k <;> simp
      invFun := fun p => Matrix.fromCols (d.e.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
        (d.e.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
      left_inv := fun w => by
        simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, neg_neg, Prod.mk.eta, LinearEquiv.symm_apply_apply]
        exact Matrix.fromCols_toCols w
      right_inv := fun p => by
        simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, LinearEquiv.apply_symm_apply, neg_neg,
          Sum.elim_comp_inl_inr] }
  form w w' := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [symp_dbl, d.form, d.form, elim_dot', elim_dot', dotProduct_neg, dotProduct_neg]
    ring

theorem dblCo_isDblCoord (d : Darboux (symp c ξ JA JB) κ) : IsDblCoord c ξ JA JB d (dblCo c d) := fun w₁ w₂ => by
  simp [dblCo]

end Coord

section Equivs

variable {R : Type}

def conjE {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (X → ℂ) :=
  LinearEquiv.ofLinear (conjMap T.toLinearMap) (conjMap T.symm.toLinearMap)
    (LinearMap.ext fun φ => by simp [conjMap_apply]) (LinearMap.ext fun φ => by simp [conjMap_apply])

theorem conjE_apply {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) (φ : X → ℂ) : conjE T φ = star (T (star φ)) := rfl

def partLE {κ κ' : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partL T.toLinearMap) (partL T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])

def partRE {κ κ' : Type} (T : ((κ' → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ)) : ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partR T.toLinearMap) (partR T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])

def dblE {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ) :=
  (partRE (conjE T)).trans (partLE T)

end Equivs

end GlobalTheory.DblInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwine

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.EvTame

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def HasTameExp {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ))
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    pureA F f (0 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
  funext x; simp [pureA]

theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g₁ g₂ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f (g₁ + g₂) = pureA F f g₁ + pureA F f g₂ := by
  funext x; simp [pureA, mul_add]

theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pureA F f (c • g) = c • pureA F f g := by
  funext x; simp only [pureA, Pi.smul_apply, smul_eq_mul]; ring

theorem hasTameExp_zero {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) :
    HasTameExp T 0 :=
  ⟨Empty, inferInstance, fun j => j.elim, fun j => j.elim, fun j => j.elim, fun f => by
    letI : IsEmpty Empty := Empty.instIsEmpty
    rw [pureA_zero, map_zero]; simp⟩

theorem HasTameExp.add {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g₁ g₂ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (h₁ : HasTameExp T g₁) (h₂ : HasTameExp T g₂) :
    HasTameExp T (g₁ + g₂) := by
  obtain ⟨ι₁, _, P₁, k₁, hk₁, e₁⟩ := h₁
  obtain ⟨ι₂, _, P₂, k₂, hk₂, e₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim P₁ P₂, Sum.elim k₁ k₂, ?_, fun f => ?_⟩
  · rintro (j | j)
    · exact hk₁ j
    · exact hk₂ j
  · rw [pureA_add, map_add (f := _), e₁, e₂, Fintype.sum_sum_type]
    rfl

theorem HasTameExp.smul {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (c : ℂ) (h : HasTameExp T g) : HasTameExp T (c • g) := by
  obtain ⟨ι, _, P, k, hk, e⟩ := h
  refine ⟨ι, inferInstance, P, fun j => c • k j, fun j => Submodule.smul_mem _ c (hk j), fun f => ?_⟩
  rw [pureA_smul, map_smul, e, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (pureA_smul _ c _).symm

theorem pure_eq_pureA {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = pureA F f (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := rfl

end GlobalTheory.EvTame

namespace GlobalTheory.EvTame

open scoped Classical

theorem isTame_of_isEv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁),
    M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → IsTame F e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hs := GlobalTheory.SBSpan.mem_span_restrictedProd F (Fin n × Fin d) g hg
  clear hg
  change HasTameExp e g
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, hcof, rfl⟩ := hx
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := by
      filter_upwards [hcof, hM.std] with v h1 h2
      rw [h1, h2]
    have hSB : ∀ v, ev v (φ v) ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := fun v =>
      (hev v).2 ▸ Submodule.mem_map_of_mem (hφ v)
    have hcof' : ∀ᶠ v in cofinite,
        ev v (φ v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hvac, hM₁.std] with v h1 h2
      rw [h1, (hev v).1, h2]
    refine ⟨Unit, inferInstance, fun _ => ei,
      fun _ y => ∏ᶠ v, ev v (φ v) fun i => evalV F v (y i),
      fun _ => GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ (fun v => ev v (φ v)) hSB hcof', fun f => ?_⟩
    rw [← pure_eq_pureA, hloc f φ hφ hvac, pure_eq_pureA, Fintype.sum_unique]
  | zero => exact hasTameExp_zero e
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.EvTame
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMap

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

open scoped Classical

namespace GlobalTheory.DoublingEv.ConjTame

def conjSch {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    SchwartzMap D ℂ →SL[starRingEnd ℂ] SchwartzMap D ℂ :=
  SchwartzMap.mkCLM (𝕜 := ℂ) (𝕜' := ℂ) (σ := starRingEnd ℂ) (fun f x => star (f x))
    (fun f g x => by simp [star_add])
    (fun a f x => by simp [smul_eq_mul, mul_comm])
    (fun f => Complex.conjCLE.contDiff.comp (f.smooth ⊤))
    (fun n => ⟨{n}, 1, zero_le_one, fun f x => by
      have h : (fun x => star (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := rfl
      rw [h, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Finset.sup_singleton, one_mul]
      exact SchwartzMap.le_seminorm ℂ n.1 n.2 f x⟩)

theorem conjSch_apply {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] (f : SchwartzMap D ℂ) (x : D) :
    conjSch f x = star (f x) := rfl

theorem star_mem_SB {X : Type} [TopologicalSpace X] {g : X → ℂ} (hg : g ∈ SB X) : star g ∈ SB X :=
  ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩

variable {F : Type} [Field F] [NumberField F]

theorem star_pureA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    star (pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
  funext x
  simp [pureA, conjSch_apply, star_mul', Pi.star_apply]

end GlobalTheory.DoublingEv.ConjTame


open GlobalTheory.DoublingEv.ConjTame in
theorem GlobalTheory.DoublingEv.isTame_conjMap : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsTame F T → IsTame F (conjMap T) := by
  intro F _ _ κ κ' _ _ T hT g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT (star g) (star_mem_SB hg)
  let Q : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ :=
    fun j => (conjSch.comp (P j)).comp conjSch
  refine ⟨ι, inferInstance, Q, fun j => star (g' j), fun j => star_mem_SB (hg' j), fun f => ?_⟩
  have hs : star (pureA F (f : _ → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
    rw [star_pureA]
  rw [conjMap_apply, hs, hP, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_pureA]
  rfl

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesSchwartz

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem evDbl_schr {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
    (A₁ B₁ A₂ B₂ : κ → AF F) (a₁ b₁ a₂ b₂ : κ₁ → AF F)
    (h1 : ∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a₁, b₁) (T Φ))
    (h2 : ∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a₂, b₂) (T Φ))
    (h3 : ∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) :
    ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
      schr ψ (Sum.elim a₁ a₂, Sum.elim b₁ (-b₂)) (evDbl T φ) := by
  intro φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a₂, -b₂) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (a₂, -b₂) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := GlobalTheory.DoublingEvLaw.sliceL hΨ (s ∘ Sum.inr + a₂)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b₂) - ⅟(2 : AF F) * (a₂ ⬝ᵥ b₂)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a₂))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, GlobalTheory.DoublingEvLaw.elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (GlobalTheory.DoublingEvLaw.sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, GlobalTheory.DoublingEvLaw.elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b₁ (-b₂) = (s ∘ Sum.inl) ⬝ᵥ b₁ - (s ∘ Sum.inr) ⬝ᵥ b₂ := by
    rw [← Sum.elim_comp_inl_inr s, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sub_eq_add_neg]
  rw [hs]
  ring

theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

theorem hasDbl_of_tame {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra (AF F) E]
    (c : E →ₐ[AF F] E) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (hT : IsGoodInt (adeleClass F) ψ d d₁ T) (ht : IsTame F T.toLinearMap) (hti : IsTame F T.symm.toLinearMap) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hS : IsTame F (conjMap T.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ ht
  have hSi : IsTame F (conjMap T.symm.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ hti
  have hR : IsTame F (partR (κ := κ) (conjMap T.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hS
  have hL : IsTame F (partL (κ' := κ) T.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ ht
  have hRi : IsTame F (partR (κ := κ) (conjMap T.symm.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hSi
  have hLi : IsTame F (partL (κ' := κ) T.symm.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hti
  have hD : IsTame F (dblE T).toLinearMap := hR.comp hL
  have hDi : IsTame F (dblE T).symm.toLinearMap := hLi.comp hRi
  have hstar : ∀ φ : (κ → AF F) → ℂ, φ ∈ schA F κ → star φ ∈ schA F κ := fun φ hφ =>
    GlobalTheory.SchAConj.star_mem_schA F κ φ hφ
  have hSsp : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    rw [conjE_apply]
    constructor
    · intro h
      exact hstar _ ((hsp _).1 (hstar _ h))
    · intro h
      have h1 : T (star φ) ∈ schA F κ := by simpa using hstar _ h
      simpa using hstar _ ((hsp _).2 h1)
  have hTL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := hunit
  have hSL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖conjMap T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨c₀, hc₀⟩ := hunit μ hμ
    refine ⟨c₀, fun φ hφ => ?_⟩
    have h := hc₀ (star φ) (hstar φ hφ)
    simp only [conjMap_apply, Pi.star_apply, enorm_eq_nnnorm, nnnorm_star, LinearEquiv.coe_coe] at h ⊢
    exact h
  refine ⟨dblCo c d₁, dblE T, conjE T, dblCo_isDblCoord c d₁,
    ⟨fun φ => ⟨fun h => hD.mapsTo φ h, fun h => ?_⟩, fun w φ hφ => ?_, fun l => ⟨fun hl => hD.comp_adm hl, fun hl => ?_⟩,
      fun μ hμ => ?_⟩, hSsp, fun φ₁ _ φ₂ _ => evDbl_boxFun T.toLinearMap φ₁ φ₂⟩
  · have := hDi.mapsTo _ h
    rw [show (dblE T).symm.toLinearMap ((dblE T) φ) = φ from (dblE T).symm_apply_apply φ] at this
    exact this
  · obtain ⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, w = Matrix.fromCols w₁ w₂ := ⟨w.toCols₁, w.toCols₂, (Matrix.fromCols_toCols w).symm⟩
    have e1 : dd.rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d.e w₁).1 (d.e w₂).1, Sum.elim (d.e w₁).2 (-(d.e w₂).2)) := by
      unfold Darboux.rho; rw [hdd]
    have e2 : (dblCo c d₁).rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d₁.e w₁).1 (d₁.e w₂).1, Sum.elim (d₁.e w₁).2 (-(d₁.e w₂).2)) := by
      unfold Darboux.rho; rw [dblCo_isDblCoord]
    rw [e1, e2]
    exact evDbl_schr ψ hψ T.toLinearMap _ _ _ _ _ _ _ _ (fun Φ hΦ => hheis w₁ Φ hΦ) (fun Φ hΦ => hheis w₂ Φ hΦ)
      hR.mapsTo φ hφ
  · have := hDi.comp_adm hl
    convert this using 1
    ext φ
    simp
  · obtain ⟨c₁, hc₁⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ T.toLinearMap ht hTL).1 μ hμ
    obtain ⟨c₂, hc₂⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ (conjMap T.toLinearMap) hS hSL).2 μ hμ
    refine ⟨c₁ * c₂, fun Φ hΦ => ?_⟩
    show ∫⁻ x, ‖partL (κ' := κ) T.toLinearMap (partR (κ := κ) (conjMap T.toLinearMap) Φ) x‖ₑ ^ 2 ∂μ = _
    rw [hc₁ _ (hR.mapsTo Φ hΦ), hc₂ Φ hΦ, mul_assoc]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co M₁.co T := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hTs : ∀ x, x ∈ schA F (Fin n × Fin d) ↔ T x ∈ schA F (Fin n × Fin d) := fun x => by
    constructor
    · intro hx
      rw [hTe x hx]
      exact hbij.mapsTo hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
      have : T y = T x := by rw [hTe y hy, hyx]
      rw [← T.injective this]
      exact hy
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (GlobalTheory.T.model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans
        (adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := GlobalTheory.T.model_evaluation_preserves_admissible hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  have ht : IsTame F T.toLinearMap := by
    intro g hg
    obtain ⟨ι, inst, P, g', hg', hPe⟩ := GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hpair.good hM₁ hev g hg
    refine ⟨ι, inst, P, g', hg', fun f => ?_⟩
    rw [← hPe f]
    exact hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)
  have hti : IsTame F T.symm.toLinearMap :=
    GlobalTheory.T.good_model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T.symm.toLinearMap
      (fun Φ hΦ => by rw [← hTe Φ hΦ]; simp)
  exact hasDbl_of_tame (cA σ) B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) (-1) _ _ M.co M₁.co T hgood ht hti

end GlobalTheory.DblInt
end
end
end
