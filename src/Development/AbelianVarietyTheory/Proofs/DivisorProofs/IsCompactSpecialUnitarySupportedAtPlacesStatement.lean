module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceExtensionByZeroTensorOfPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdeleOfPlacesMulEqSumComponentsStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSpecialUnitarySupportedAtPlaces

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

namespace GlobalTheory.SUSuppClosed

theorem isClosed_SUSupp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) : IsClosed (SUSupp σ J ε) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have hv : Continuous fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (GlobalTheory.AdelicU.isEmbedding_matHom (AF F) σ J).continuous
  have h1 : IsClosed {g : HA (AF F) σ J | g ∈ SUAdelic σ J} := by
    simp only [StrongApprox.mem_SUAdelic]
    exact isClosed_eq hv.matrix_det continuous_const
  have h2 : IsClosed {g : HA (AF F) σ J | ∀ i j,
      algebraMap (AF F) (AF F ⊗[F] E) ε * (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j =
        (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous fun g : HA (AF F) σ J =>
        (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j :=
      (hv.sub continuous_const).matrix_elem i j
    exact isClosed_eq (continuous_const.mul hc) hc
  exact h1.inter h2

end GlobalTheory.SUSuppClosed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSpecialUnitarySupportedAtPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.isClosed_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F), IsClosed (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppClosed.isClosed_SUSupp | exact GlobalTheory.SUSuppClosed.isClosed_SUSupp | (intros; apply GlobalTheory.SUSuppClosed.isClosed_SUSupp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesBis

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.SUSuppCompact

theorem isCompact_SUSupp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (X : Set (AF F ⊗[F] E)) (hX : IsCompact X) (hcl : IsClosed (SUSupp σ J ε)) (hent : ∀ g ∈ SUSupp σ J ε, ∀ i j, ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ X) : IsCompact (SUSupp σ J ε) := by
  have hinv : ∀ g ∈ SUSupp σ J ε, g⁻¹ ∈ SUSupp σ J ε := by
    intro g hg
    rw [GlobalTheory.SUSuppSub.mem_SUSupp_iff] at hg ⊢
    exact ⟨(SUAdelic σ J).inv_mem hg.1, GlobalTheory.SUSuppSub.fix_inv _ (GlobalTheory.SUSuppSub.mv_inv_mul σ J g) hg.2⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  let S : Set (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => X
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hX
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  have hL := (GlobalTheory.AdelicU.isClosedEmbedding_matHom_GAd σ J).isCompact_preimage hK
  refine hL.of_isClosed_subset hcl fun g hg => ?_
  refine ⟨fun i _ j _ => hent g hg i j, ((HA.mat (AF F) σ J g⁻¹).1), fun i _ j _ => hent g⁻¹ (hinv g hg) i j, ?_⟩
  rfl
end GlobalTheory.SUSuppCompact

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesTer

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (X : Set (AF F ⊗[F] E)), IsCompact X → IsClosed (SUSupp σ J ε) → (∀ g ∈ SUSupp σ J ε, ∀ i j, ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ X) → IsCompact (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppCompact.isCompact_SUSupp | exact GlobalTheory.SUSuppCompact.isCompact_SUSupp | (intros; apply GlobalTheory.SUSuppCompact.isCompact_SUSupp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEquationBaseChangeAlgHom

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

namespace GlobalTheory

theorem unitaryEq_baseChange {F E R K : Type} [Field F] [Field E] [Algebra F E] [CommRing R]
    [Algebra F R] [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] K) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :
    Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J →
    Formalism.UG.cT (sigR K σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) * JR K J *
      g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = JR K J := by
  intro h
  set φ' : R ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
    with hφ'
  have hsig : ∀ x, φ' (sigR R σ x) = sigR K σ (φ' x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [hφ', sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hJ : (JR R J).map φ' = JR K J := by
    ext i j
    simp [JR, inclR, hφ']
  have hcT : (Formalism.UG.cT (sigR R σ) g).map φ' = Formalism.UG.cT (sigR K σ) (g.map φ') := by
    ext i j
    simp [Formalism.UG.cT, hsig]
  have h2 := congrArg (fun A => A.map φ') h
  simp only [Matrix.map_mul] at h2
  rw [hcT, hJ] at h2
  exact h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEquationBaseChangeAlgHomStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.unitaryEquation_baseChange_algHom : ∀ {F E R K : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] K) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J → Formalism.UG.cT (sigR K σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) * JR K J * g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = JR K J := by
  first | exact @GlobalTheory.unitaryEq_baseChange | exact GlobalTheory.unitaryEq_baseChange | (intros; apply GlobalTheory.unitaryEq_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlaces

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SUSuppCompact

theorem isCompact_SUSupp_of_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (∀ w ∈ S₁, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g = JR w.Completion J → ∀ i j, g i j ∈ C) → (∀ v ∈ S₂, ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g = JR (Fv F v) J → ∀ i j, g i j ∈ C) → IsCompact (SUSupp σ J ε) := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε h₁ h₂
  classical
  haveI : FiniteDimensional F E := inferInstance
  have h₁' : ∀ w : InfinitePlace F, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ (w ∈ S₁ →
      ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g =
        JR w.Completion J → ∀ i j, g i j ∈ C) := by
    intro w
    by_cases hw : w ∈ S₁
    · obtain ⟨C, hC, hC'⟩ := h₁ w hw
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hw⟩
  have h₂' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ (v ∈ S₂ →
      ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g =
        JR (Fv F v) J → ∀ i j, g i j ∈ C) := by
    intro v
    by_cases hv : v ∈ S₂
    · obtain ⟨C, hC, hC'⟩ := h₂ v hv
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hv⟩
  choose C₁ hC₁ hC₁' using h₁'
  choose C₂ hC₂ hC₂' using h₂'
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Set (AF F ⊗[F] E)), (∀ i ∈ s, IsCompact (f i)) →
      IsCompact (∑ i ∈ s, f i) := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, ← Set.singleton_zero]; exact isCompact_singleton
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  set e := algebraMap (AF F) (AF F ⊗[F] E) ε with he
  let X : Set (AF F ⊗[F] E) := (fun δ => δ * (1 - e)) '' ({0, 1} : Set (AF F ⊗[F] E)) +
    (∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w) '' C₁ w) +
    ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v) '' C₂ v
  have hX : IsCompact X :=
    ((((Set.toFinite _).isCompact).image (continuous_id.mul continuous_const)).add
      (hsum _ _ fun w _ => (hC₁ w).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))).add (hsum _ _ fun v _ => (hC₂ v).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))
  refine GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces σ J ε X hX (GlobalTheory.T.isClosed_specialUnitarySupportedAtPlaces σ J ε) fun g hg i j => ?_
  have hu : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      JR (AF F) J * ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J := by
    let g' : HR (AF F) σ J := g
    exact g'.2
  set a := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with ha
  set δ := (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with hδ
  have hfix : e * (a - δ) = a - δ := by
    have := hg.2 i j
    simpa only [Matrix.sub_apply] using this
  have hdec : a = δ * (1 - e) + e * a := by linear_combination (-1 : AF F ⊗[F] E) * hfix
  rw [hdec, GlobalTheory.T.idempotentAdeleOfPlaces_mul_eq_sum_components S₁ S₂ ε hε a, ← add_assoc]
  refine Set.add_mem_add (Set.add_mem_add ⟨δ, ?_, rfl⟩ (Set.finsetSum_mem_finsetSum _ _ _ fun w hw => ⟨_, ?_, rfl⟩))
    (Set.finsetSum_mem_finsetSum _ _ _ fun v hv => ⟨_, ?_, rfl⟩)
  · rw [hδ, Matrix.one_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact hC₁' w hw _ (GlobalTheory.T.unitaryEquation_baseChange_algHom σ J _ _ hu) i j
  · exact hC₂' v hv _ (GlobalTheory.T.unitaryEquation_baseChange_algHom σ J _ _ hu) i j

end GlobalTheory.SUSuppCompact

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isCompact_specialUnitary_supportedAtPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (∀ w ∈ S₁, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g = JR w.Completion J → ∀ i j, g i j ∈ C) → (∀ v ∈ S₂, ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g = JR (Fv F v) J → ∀ i j, g i j ∈ C) → IsCompact (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppCompact.isCompact_SUSupp_of_bounded | exact GlobalTheory.SUSuppCompact.isCompact_SUSupp_of_bounded | (intros; apply GlobalTheory.SUSuppCompact.isCompact_SUSupp_of_bounded <;> assumption)
end
end
