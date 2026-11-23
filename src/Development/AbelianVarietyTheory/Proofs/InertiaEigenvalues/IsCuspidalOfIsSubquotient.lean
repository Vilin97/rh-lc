module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRep
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleQuotientFinitelyGeneratedRepStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroIntertwiningMapFromUnitarySupercusp
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVector
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorLiftEquivariantMapsOfIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalJacquetModuleSecondBlockOfVanishingStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedJacquetTwoBlocksFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRepStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.exists_equiv_exteriorTensor_of_irreducible_prod_rep : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  first | exact @GlobalTheory.TensorFactor.exists_equiv_extTensor | exact GlobalTheory.TensorFactor.exists_equiv_extTensor | (intros; apply GlobalTheory.TensorFactor.exists_equiv_extTensor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroIntertwiningMapFromUnitarySupercuspStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.exists_nonzero_intertwiningMap_from_unitary_supercuspidal : ∀ (G W V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) (ρ : Representation ℂ G V) (p : π.IntertwiningMap ρ), IsSmooth π → IsSupercuspidal ρ → IsUnitarisable ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ∀ w, π z w = c • w) → p ≠ 0 → ∃ ι : ρ.IntertwiningMap π, ι ≠ 0 := by
  first | exact @GlobalTheory.CuspBack.exists_back | exact GlobalTheory.CuspBack.exists_back | (intros; apply GlobalTheory.CuspBack.exists_back <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVectorStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.exists_smoothDual_ne_zero_at_vector : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsSmooth ρ → ∀ v : V, v ≠ 0 → ∃ l : Module.Dual ℂ V, l ∈ smoothPart ρ.dual ∧ l v ≠ 0 := by
  first | exact @GlobalTheory.SmoothForm.exists_smooth_form_ne_zero | exact GlobalTheory.SmoothForm.exists_smooth_form_ne_zero | (intros; apply GlobalTheory.SmoothForm.exists_smooth_form_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorLiftEquivariantMapsOfIrreducibleStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.injective_tensor_lift_equivariant_maps_of_irreducible : ∀ (H X Y : Type) [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H X) (ρ : Representation ℂ H Y), ρ.IsIrreducible → (∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) → ∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ g (φ v)) → Function.Injective (TensorProduct.lift M.subtype) := by
  first | exact @GlobalTheory.SmGL.EvalInj.lift_subtype_injective | exact GlobalTheory.SmGL.EvalInj.lift_subtype_injective | (intros; apply GlobalTheory.SmGL.EvalInj.lift_subtype_injective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableComplexRepOfSupercuspidalUnitaryCeStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.isUnitarisableComplexRep_of_supercuspidal_unitary_center : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual → l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  first | exact @GlobalTheory.isUnitarisable_of_isSupercuspidal | exact GlobalTheory.isUnitarisable_of_isSupercuspidal | (intros; apply GlobalTheory.isUnitarisable_of_isSupercuspidal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetNontrivial

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.JacquetEmptyFirstBlock

theorem jacquet_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    π.IsIrreducible → ∀ (h : 0 + n = n), Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) := by
  intro k _ _ _ _ n V _ _ π hπ h
  have key : ∀ x, GlobalTheory.SmGL.blk (two (stdSum h)) x = true := by
    intro x
    unfold GlobalTheory.SmGL.blk
    obtain ⟨⟨b, y⟩, hy⟩ : ∃ p, (two (stdSum h)).symm x = p := ⟨_, rfl⟩
    rw [hy]
    cases b
    · exact Fin.elim0 y
    · rfl
  have hbot : unipRad k (two (stdSum h)) = ⊥ := by
    by_contra hne
    obtain ⟨i, j, hij⟩ := (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff).1 hne
    rw [key i, key j] at hij
    exact lt_irrefl _ hij
  have hker : twKer π (⊥ : Subgroup (GL (Fin n) k)) 1 = ⊥ := by
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨⟨g, hg⟩, v, rfl⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : IsSimpleOrder (Subrepresentation π) := hπ
    exact (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _))
  rw [hbot]
  show Nontrivial (V ⧸ twKer π ⊥ 1)
  rw [hker]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℂ V) rfl).toEquiv.nontrivial

end GlobalTheory.SmGL.JacquetEmptyFirstBlock
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSubquotient

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCuspidal_of_isSubquotient {n V W : Type} [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W}
    (hτ : IsCuspidal τ) (h : IsSubquotient π τ) : IsCuspidal π := by
  refine ⟨h.isSmooth hτ.1, fun s d e he => ?_⟩
  obtain ⟨S, f, hf⟩ := GlobalTheory.JacquetExact.isSubquotient_jac e hτ.1 h
  haveI := hτ.2 s d e he
  exact hf.subsingleton

theorem exists_root_norm {ω : kˣ →* ℂˣ} (hω : IsSmoothChar ω) {b : ℕ} (hb : 0 < b) :
    ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ ∀ z, ‖((ω * ψ ^ b) z : ℂ)‖ = 1 := by
  apply _root_.GlobalTheory.LocGL.SupportUnique.exists_root_norm <;> assumption

theorem exists_irreducible_sub {b : ℕ} (hb : 0 < b) {X : Type} [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    (τ : Representation ℂ (GL (Fin b) k) X) (hτ : IsCuspidal τ)
    (hz : ∀ z ∈ Subgroup.center (GL (Fin b) k), ∃ c : ℂ, ∀ w, τ z w = c • w) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (ρ : Representation ℂ (GL (Fin b) k) Y),
      ρ.IsIrreducible ∧ IsCuspidal ρ ∧ ∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ g (ι v) := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  let S : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
    have hle : Submodule.span ℂ (Set.range fun g => τ g x) ≤
        (Submodule.span ℂ (Set.range fun g => τ g x)).comap (τ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', rfl⟩
      exact Submodule.subset_span ⟨g * g', by simp⟩
    exact hle hv⟩
  have hxS : x ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have hnt : Nontrivial S.toSubmodule := ⟨⟨⟨x, hxS⟩, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨Y, _, _, ρ, hρi, p, hp⟩ := GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep _ _ S.toRepresentation {⟨x, hxS⟩} hnt (by
    refine Submodule.map_injective_of_injective S.toSubmodule.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show _ = Submodule.span ℂ (Set.range fun g => τ g x)
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨g, v, hv, rfl⟩, rfl⟩
      rw [Finset.mem_singleton.1 hv]
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨_, ⟨g, _, Finset.mem_singleton_self _, rfl⟩, rfl⟩)
  have hρc : IsCuspidal ρ := isCuspidal_of_isSubquotient hτ ⟨S, p, hp⟩
  have hSs : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, Representation.IntertwiningMap.id _, Function.surjective_id⟩ hτ.1
  obtain ⟨ω, hω, hωc⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar hρc.1 hρi
  obtain ⟨ψ, hψ, hψ1⟩ := exists_root_norm hω hb
  have hc' : IsCuspidal (twist ρ (detChar (Fin b) ψ)) := GlobalTheory.LocGL.isCuspidal_twist hρc hψ
  have hsc := GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k b Y _ hc'
  haveI : Nontrivial Y := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρi
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨l, hl, hly⟩ := GlobalTheory.T.exists_smoothDual_ne_zero_at_vector _ _ (twist ρ (detChar (Fin b) ψ)) (fun U hU => by
    obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset (n := Fin b) hU
    exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, h⟩) hc'.1 y hy
  have hu := GlobalTheory.T.isUnitarisableComplexRep_of_supercuspidal_unitary_center _ _ _ l hl (fun h => hly (by rw [h]; rfl)) (GlobalTheory.LocGL.isIrreducible_twist hρi _) hsc
    (fun z hz => by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨z, rfl⟩ := hz
      have h := GlobalTheory.LocGL.hasCentralChar_twist hωc ψ z
      rw [Fintype.card_fin] at h
      exact ⟨_, hψ1 z, h⟩)
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_nonzero_intertwiningMap_from_unitary_supercuspidal _ _ _ (twist S.toRepresentation (detChar (Fin b) ψ)) _ (twistMap p _)
    (isSmooth_twist hSs hψ.detChar) hsc hu
    (fun z hz' => by
      obtain ⟨c, hc⟩ := hz z hz'
      refine ⟨(detChar (Fin b) ψ z : ℂ) * c, fun w => ?_⟩
      rw [twist_apply, mul_smul]
      exact congrArg _ (Subtype.ext (hc w)))
    (fun h => by
      obtain ⟨w, hw⟩ := hp y
      have h1 : twistMap p (detChar (Fin b) ψ) w = y := hw
      rw [h] at h1
      exact hy h1.symm)
  refine ⟨Y, _, _, ρ, hρi, hρc, S.toSubmodule.subtype ∘ₗ ι.toLinearMap, fun h => hι ?_, fun g v => ?_⟩
  · ext v
    exact LinearMap.congr_fun h v
  · have h1 := Representation.IntertwiningMap.isIntertwining _ _ ι g v
    rw [twist_apply, twist_apply, map_smul] at h1
    exact congrArg Subtype.val (smul_right_injective _ (Units.ne_zero _) h1)

theorem exists_map_jac₂ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hn : 0 < n) :
    ∃ (a b : ℕ) (h : a + b = n) (W W' : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : AddCommGroup W') (_ : Module ℂ W')
      (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W'),
      0 < b ∧ IsSmooth σ ∧ σ.IsIrreducible ∧ IsSmooth ρ ∧ ρ.IsIrreducible ∧ IsCuspidal ρ ∧
      ∃ φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 := by
  classical
  have hex : ∃ b : ℕ, 0 < b ∧ ∃ (a : ℕ) (h : a + b = n), Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) :=
    ⟨n, hn, 0, zero_add n, GlobalTheory.SmGL.JacquetEmptyFirstBlock.jacquet_nontrivial k n V π hi _⟩
  obtain ⟨hb, a, h, hnt⟩ := Nat.find_spec hex
  have hmin := fun t (ht : t < Nat.find hex) => Nat.find_min hex ht
  generalize Nat.find hex = b at hb h hnt hmin
  have hJc := GlobalTheory.T.isCuspidal_jacquetModule_second_block_of_vanishing k a b n h V π hs fun r t h' h0 ht =>
    not_nontrivial_iff_subsingleton.1 fun h1 => hmin t ht ⟨h0, r, h', h1⟩
  obtain ⟨s, hspan⟩ := GlobalTheory.T.normalizedJacquetTwoBlocks_finitelyGenerated k a b n h V π hs hi
  obtain ⟨X, _, _, τ, hτi, f, hf⟩ := GlobalTheory.T.exists_irreducible_quotient_finitelyGenerated_rep _ _ _ s hnt hspan
  have hτs : IsSmooth τ := (IsSubquotient.of_surjective f hf).isSmooth (isSmooth_jac₂ _ hs)
  have hτc : IsCuspidal (k := k) (n := Fin b) (τ.comp (MonoidHom.inr _ _)) :=
    isCuspidal_of_isSubquotient hJc (IsSubquotient.of_surjective (compMap f _) hf)
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτi
  haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin a)
  haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin b)
  obtain ⟨Y, _, _, ρ, hρi, hρc, hι⟩ := exists_irreducible_sub hb (τ.comp (MonoidHom.inr _ _)) hτc fun z hz =>
    GlobalTheory.LocGL.exists_eq_smul_of_isSmooth hτs hτi ⟨τ (1, z), fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (Subgroup.mem_center_iff.1 hz g.2).symm⟩
  obtain ⟨W, _, _, σ, hσs, hσi, ⟨φ⟩⟩ := GlobalTheory.T.exists_equiv_exteriorTensor_of_irreducible_prod_rep _ _ X Y τ ρ hτs hτi hρi
    (GlobalTheory.T.injective_tensor_lift_equivariant_maps_of_irreducible _ X Y (τ.comp (MonoidHom.inr _ _)) ρ hρi (GlobalTheory.LocGL.schur_GL hρc.1 hρi)) hι
  refine ⟨a, b, h, W, Y, _, _, _, _, σ, ρ, hb, hσs, hσi, hρc.1, hρi, hρc, φ.toIntertwiningMap.comp f, fun h0 => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  obtain ⟨w, rfl⟩ := hf x
  have h1 : φ (f w) = 0 := congrArg (fun F => F w) h0
  exact hx ((map_eq_zero_iff φ φ.injective).1 h1)

end GlobalTheory.JacFactor
end
end
