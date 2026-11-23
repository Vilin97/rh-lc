module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSubquotientIffWhittakerQuotientStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoGenericSubquotientsImpossible

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientRealisedBySubreps

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SubquotPres

theorem exists_equiv_subQuot : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (π : Representation ℂ G W),
    IsSubquotient π ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ Nonempty (π.Equiv (subQuot A B)) := by
  intro G V W _ _ _ _ _ ρ π h
  obtain ⟨S, f, hf⟩ := h
  have hint : ∀ (g : G) (x : S.toSubmodule),
      f.toLinearMap (S.toRepresentation g x) = π g (f.toLinearMap x) := fun g x => by
    simpa only [Representation.IntertwiningMap.toLinearMap_apply] using
      Representation.IntertwiningMap.isIntertwining _ _ f g x
  let K : Submodule ℂ S.toSubmodule := LinearMap.ker f.toLinearMap
  let B : Subrepresentation ρ := ⟨K.map S.toSubmodule.subtype, by
    intro g v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨S.toRepresentation g x, ?_, rfl⟩
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hint, hx, map_zero]⟩
  have hBS : B ≤ S := by
    show K.map S.toSubmodule.subtype ≤ S.toSubmodule
    exact Submodule.map_subtype_le _ _
  have hQ : Submodule.comap S.toSubmodule.subtype B.toSubmodule = K :=
    Submodule.comap_map_eq_of_injective Subtype.val_injective K
  let φ := Submodule.liftQ (Submodule.comap S.toSubmodule.subtype B.toSubmodule) f.toLinearMap hQ.le
  have hφ : ∀ x : S.toSubmodule, φ (Submodule.Quotient.mk x) = f.toLinearMap x := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hQ.ge
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk x, by rw [hφ, Representation.IntertwiningMap.toLinearMap_apply]⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hφint : ∀ (g : G) q, φ (GlobalTheory.SmGL.subQuot S B g q) = π g (φ q) := by
    intro g q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact hint g x
  have hT : ∀ g : G, e.symm.toLinearMap ∘ₗ π g =
      GlobalTheory.SmGL.subQuot S B g ∘ₗ e.symm.toLinearMap := by
    intro g
    ext w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    obtain ⟨q, rfl⟩ := e.surjective w
    rw [LinearEquiv.symm_apply_apply]
    exact (hφint g q).symm
  let T : Representation.IntertwiningMap π (GlobalTheory.SmGL.subQuot S B) :=
    ⟨e.symm.toLinearMap, hT⟩
  exact ⟨S, B, hBS, ⟨Representation.Equiv.mk' T e (fun w => e.apply_symm_apply w)
    (fun q => e.symm_apply_apply q)⟩⟩

end GlobalTheory.CompanionTheory.SubquotPres
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientRealisedBySubrepsStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.subquotient_realised_by_subreps : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (π : Representation ℂ G W), IsSubquotient π ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ Nonempty (π.Equiv (subQuot A B)) := by
  first | exact @GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot | exact GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot | (intros; apply GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelSupDistributesSubreps

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.WhitSup

theorem mem_sup_of_mem_twKer_sup {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (X Y : Subrepresentation ρ) (H : Subgroup G) (χ : H →* ℂˣ)
    {w : (X ⊔ Y).toSubmodule} (hw : w ∈ twKer (X ⊔ Y).toRepresentation H χ) :
    (w : V) ∈ X.toSubmodule ⊓ twKer ρ H χ ⊔ Y.toSubmodule ⊓ twKer ρ H χ := by
  unfold GlobalTheory.PRep.twKer at hw ⊢
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨h, u, rfl⟩ := hz
    have hu : (u : V) ∈ X.toSubmodule ⊔ Y.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup]
      exact u.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hu
    have hρu : ((X ⊔ Y).toRepresentation h u : V) = ρ h u := rfl
    have hcoe : (((X ⊔ Y).toRepresentation h u - (χ h : ℂ) • u : (X ⊔ Y).toSubmodule) : V) =
        (ρ h x - (χ h : ℂ) • x) + (ρ h y - (χ h : ℂ) • y) := by
      rw [Submodule.coe_sub, Submodule.coe_smul, hρu, ← hxy, map_add (f := _), smul_add]
      abel
    rw [hcoe]
    apply Submodule.add_mem_sup
    · exact Submodule.mem_inf.2
        ⟨X.toSubmodule.sub_mem (X.apply_mem_toSubmodule h hx) (X.toSubmodule.smul_mem _ hx),
          Submodule.subset_span ⟨h, x, rfl⟩⟩
    · exact Submodule.mem_inf.2
        ⟨Y.toSubmodule.sub_mem (Y.apply_mem_toSubmodule h hy) (Y.toSubmodule.smul_mem _ hy),
          Submodule.subset_span ⟨h, y, rfl⟩⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Submodule.coe_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ c ha

theorem sup_inf_twKer_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ≤ X.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ⊔ Y.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ X Y w hw
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
  have hW : GlobalTheory.PRep.IsSmooth (X ⊔ Y).toRepresentation := by
    unfold GlobalTheory.PRep.IsSmooth at hρ ⊢
    intro v
    have hset : {g | (X ⊔ Y).toRepresentation g v = v} = {g | ρ g v = v} := by
      ext g
      exact Subtype.ext_iff
    rw [hset]
    exact hρ v
  have hw' : (⟨w, hw1⟩ : (X ⊔ Y).toSubmodule) ∈ GlobalTheory.PRep.twKer
      (X ⊔ Y).toRepresentation (GlobalTheory.SmGL.unipB k (Fin N))
      (GlobalTheory.LocGL.whitChar ψ N) :=
    GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N (X ⊔ Y).toRepresentation ρ
      hW hρ (X ⊔ Y).toSubmodule.subtype Subtype.val_injective (fun _ _ => rfl) _ hw2
  exact GlobalTheory.CompanionTheory.PRep.WhitSup.mem_sup_of_mem_twKer_sup X Y _ _ hw'

end GlobalTheory.CompanionTheory.PRep.WhitSup

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelSupDistributesSubrepsStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.twisted_kernel_sup_distributes_subreps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ≤ X.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ⊔ Y.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le | exact GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le | (intros; apply GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoGenericSubquotientsImpossibleStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nonempty_equiv_subQuot_of_not_le_sup : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (T : Submodule ℂ V), Module.rank ℂ (V ⧸ T) ≤ 1 → (∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ T ≤ X.toSubmodule ⊓ T ⊔ Y.toSubmodule ⊓ T) → ∀ A B C D : Subrepresentation ρ, B ≤ A → D ≤ C → (subQuot A B).IsIrreducible → (subQuot C D).IsIrreducible → ¬ A.toSubmodule ≤ B.toSubmodule ⊔ T → ¬ C.toSubmodule ≤ D.toSubmodule ⊔ T → Nonempty ((subQuot A B).Equiv (subQuot C D)) := by
  first | exact @GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic | exact GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic | (intros; apply GlobalTheory.CompanionTheory.GenCoreMain.nonempty_equiv_of_generic <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBound

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenUniq

theorem nonempty_equiv_of_generic_subquotients (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (N : ℕ) {V W₁ W₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ (GL (Fin N) k) V)
    (π : Representation ℂ (GL (Fin N) k) W₁) (σ : Representation ℂ (GL (Fin N) k) W₂)
    (hρ : IsSmooth ρ)
    (hrank : Module.rank ℂ (TwJacquet ρ (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπρ : IsSubquotient π ρ) (hσρ : IsSubquotient σ ρ)
    (hgπ : IsGenericFor ψ π) (hgσ : IsGenericFor ψ σ) : Nonempty (π.Equiv σ) := by
  obtain ⟨A, B, hBA, ⟨e₁⟩⟩ := GlobalTheory.T.subquotient_realised_by_subreps ρ π hπρ
  obtain ⟨C, D, hDC, ⟨e₂⟩⟩ := GlobalTheory.T.subquotient_realised_by_subreps ρ σ hσρ
  have hiAB : (subQuot A B).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₁ hπ
  have hiCD : (subQuot C D).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₂ hσ
  have hAB := (GlobalTheory.T.generic_subquotient_iff_whittaker_quotient k ψ hψ N ρ hρ A B hBA).1 (IsGenericFor.of_equiv hgπ e₁)
  have hCD := (GlobalTheory.T.generic_subquotient_iff_whittaker_quotient k ψ hψ N ρ hρ C D hDC).1 (IsGenericFor.of_equiv hgσ e₂)
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_equiv_subQuot_of_not_le_sup ρ (twKer ρ (unipB k (Fin N)) (whitChar ψ N)) hrank
    (GlobalTheory.T.twisted_kernel_sup_distributes_subreps k ψ hψ N ρ hρ) A B C D hBA hDC hiAB hiCD hAB hCD
  exact ⟨(e₁.trans e).trans e₂.symm⟩

end GlobalTheory.CompanionTheory.GenUniq
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBoundStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.whittaker_rank_extension_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V W₁ W₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ (GL (Fin N) k) V) (π : Representation ℂ (GL (Fin N) k) W₁) (σ : Representation ℂ (GL (Fin N) k) W₂), IsSmooth ρ → Module.rank ℂ (TwJacquet ρ (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 → π.IsIrreducible → σ.IsIrreducible → IsSubquotient π ρ → IsSubquotient σ ρ → IsGenericFor ψ π → IsGenericFor ψ σ → Nonempty (π.Equiv σ) := by
  first | exact @GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients | exact GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients | (intros; apply GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients <;> assumption)
end
end
