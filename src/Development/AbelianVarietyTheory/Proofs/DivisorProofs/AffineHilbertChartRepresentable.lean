module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertTensorToSubschemeSectionsSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisQuotientTensorBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOfQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealsEqOfSpanIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertRepresentingUniversalSubscheme
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorPullbackEqMapStatement
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingMapFromAffineOpens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorBasisCriterion
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHom

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem secAlg_toSpecΓ_top (Z : Scheme.{0}) :
    secAlg Γ(Z, ⊤) Z.toSpecΓ ⊤ = RingHom.id _ := by
  ext a
  have e : Z.toSpecΓ.appLE ⊤ ⊤ (by simp) = Z.toSpecΓ.appTop := (Scheme.Hom.app_eq_appLE _).symm
  simp only [secAlg, RingHom.comp_apply, e, Scheme.toSpecΓ_appTop]
  simp

theorem exists_hom_secAlg_top (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)) :
    ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom Φ), ?_⟩
  rw [secAlg_comp, secAlg_toSpecΓ_top]
  rfl

end GlobalTheory.HilbAff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHomStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom : ∀ (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)), ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  first | (exact @GlobalTheory.HilbAff.exists_hom_secAlg_top) | (exact GlobalTheory.HilbAff.exists_hom_secAlg_top) | (intros; apply GlobalTheory.HilbAff.exists_hom_secAlg_top  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSectionsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (I₁ I₂ : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData), (∀ U : T.affineOpens, RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₁ U) = RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₂ U)) → I₁ = I₂ := by
  first | (exact @GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq) | (exact GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq) | (intros; apply GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasis

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem good_xI : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) {r : ℕ} (v : Fin r → B), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → GlobalTheory.HilbAff.Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (GlobalTheory.HilbAff.xI A B C J) := by
  intro A B C _ _ _ _ _ J r v hli hsp
  let bas : Module.Basis (Fin r) C ((C ⊗[A] B) ⧸ J) := Module.Basis.mk hli hsp.ge
  haveI : Module.Free C ((C ⊗[A] B) ⧸ J) := Module.Free.of_basis bas
  haveI : Module.Finite C ((C ⊗[A] B) ⧸ J) := Module.Finite.of_basis bas
  have hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom) :=
    (Ideal.Quotient.mk_surjective).comp (Algebra.TensorProduct.comm A B C).surjective
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have hsnd : (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv) ≫
      pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap C ((C ⊗[A] B) ⧸ J))) := by
    rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  refine good_ker A B r _ _ ?_ ?_ ?_
  · rw [hsnd]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · rw [hsnd]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · intro y
    rw [hsnd]
    refine (Scheme.Hom.finrank_SpecMap_algebraMap C ((C ⊗[A] B) ⧸ J) y).trans ?_
    haveI : Nontrivial C := by
      let p : PrimeSpectrum C := y
      refine ⟨⟨0, 1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩⟩
      rw [← h]; exact p.asIdeal.zero_mem
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis bas, Fintype.card_fin]
    rfl

end GlobalTheory.HilbAff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasisStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) {r : ℕ} (v : Fin r → B), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → GlobalTheory.HilbAff.Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (GlobalTheory.HilbAff.xI A B C J) := by
  first | (exact @GlobalTheory.HilbAff.good_xI) | (exact GlobalTheory.HilbAff.good_xI) | (intros; apply GlobalTheory.HilbAff.good_xI  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorToSubschemeSectionsRestricStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct


theorem _root_.GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
      (g : T ⟶ Spec (CommRingCat.of A))
      (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
      (U V : T.affineOpens) (h : (U : T.Opens) ≤ V),
      letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
      letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
      ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
        (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
          (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤
        RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  intro A B _ _ _ T g I U V h
  let := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
  let := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
          (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op) }
  refine ⟨ρ, rfl, ?_⟩
  have kappa_tmul (W : T.Opens) (c : Γ(T, W)) (b : B) :
      letI := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
      GlobalTheory.HilbAff.kappa A B g I W (c ⊗ₜ[A] b) =
        ((I.subschemeι ≫ pullback.snd _ g).app W).hom c *
          ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤
            ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) (by simp)).hom
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
    let := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
    let : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) :=
      (((I.subschemeι ≫ pullback.snd _ g).app W).hom.comp
        (GlobalTheory.HilbAff.secAlg A g W)).toAlgebra
    exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hκ (t : Γ(T, V) ⊗[A] B) :
      GlobalTheory.HilbAff.kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (GlobalTheory.HilbAff.kappa A B g I V t) := by
    induction t using TensorProduct.inductionOn with
    | tmul c b =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
      have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := rfl
      rw [hc]
      congr 1
      · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
        rfl
      · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
            (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
            (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
        exact (congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [hκ t, ht, map_zero]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertChartRepresentable

section

@[expose] public section

namespace GlobalTheory.HilbAff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem exists_unique_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (C : Type) [CommRing C] [Algebra A C]
    (J : Ideal (C ⊗[A] B))
    (hli : LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k))))
    (hsp : Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k)))) = ⊤)
    (huniv : ∀ (A' : Type) [CommRing A'] [Algebra A A'] (J' : Ideal (A' ⊗[A] B)),
      LinearIndependent A' (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k))) →
      Submodule.span A' (Set.range (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k)))) = ⊤ →
      ∃! φ : C →ₐ[A] A', J' = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)))
    (hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J))
    (Z : Scheme.{0}) (g : Z ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    (hI : Good A B r g I)
    (hy : ∀ U : Z.affineOpens, letI := (secAlg A g U).toAlgebra
      Function.Bijective fun c : Fin r → Γ(Z, U) => kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k))) :
    ∃! h : Z ⟶ Spec (CommRingCat.of C), (functor A B r).map h.op
      (⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩ :
        (functor A B r).obj (op (Spec (CommRingCat.of C)))) = ⟨g, ⟨I, hI⟩⟩ := by
  have hch : ∀ U : Z.affineOpens, ∃ φ : C →+* Γ(Z, U), ∃ hφ : ∀ a : A,
      φ (algebraMap A C a) = secAlg A g U a,
      letI := (secAlg A g U).toAlgebra
      RingHom.ker (kappa A B g I U) = J.map (Algebra.TensorProduct.map
        ({ toRingHom := φ, commutes' := hφ } : C →ₐ[A] Γ(Z, U)) (AlgHom.id A B)) ∧
      ∀ ψ : C →ₐ[A] Γ(Z, U), RingHom.ker (kappa A B g I U) =
        J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B)) → ψ.toRingHom = φ := by
    intro U
    letI := (secAlg A g U).toAlgebra
    obtain ⟨-, hli', hsp'⟩ := (GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)
    obtain ⟨φ, hφ, hφu⟩ := huniv Γ(Z, U) _ hli' hsp'
    exact ⟨φ.toRingHom, φ.commutes, hφ, fun ψ hψ => congrArg AlgHom.toRingHom (hφu ψ hψ)⟩
  choose φ hφA hφ hφu using hch
  have compat : ∀ (U V : Z.affineOpens) (hUV : (U : Z.Opens) ≤ V),
      (Z.presheaf.map (homOfLE hUV).op).hom.comp (φ V) = φ U := by
    intro U V hUV
    letI iU := (secAlg A g U).toAlgebra
    letI iV := (secAlg A g V).toAlgebra
    obtain ⟨ρ, hρ, hle⟩ := GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict A B g I U V hUV
    let φV : C →ₐ[A] Γ(Z, V) := { toRingHom := φ V, commutes' := hφA V }
    have hmap : J.map (Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B)) =
        (RingHom.ker (kappa A B g I V)).map (Algebra.TensorProduct.map ρ (AlgHom.id A B)) := by
      rw [hφ V, show Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B) =
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)).comp
          (Algebra.TensorProduct.map φV (AlgHom.id A B)) by
        rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id]]
      exact (Ideal.map_map (Algebra.TensorProduct.map φV (AlgHom.id A B)).toRingHom
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)).toRingHom).symm
    have hsp2 := (GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J (ρ.comp φV) hli hsp).2
    have hliU := ((GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)).2.1
    have heq := GlobalTheory.T.ideals_eq_of_span_independent A B Γ(Z, U) (fun k => e (σ k)) _ _ (hmap ▸ hle) hsp2 hliU
    rw [← hφu U (ρ.comp φV) heq.symm, ← hρ]
    rfl
  obtain ⟨Φ, hΦ, hΦu⟩ := GlobalTheory.T.ring_map_from_affine_opens Z C φ compat
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom Z C Φ
  have hhU : ∀ U : Z.affineOpens, secAlg C h U = φ U := fun U => by
    rw [← secAlg_res C h (le_top : (U : Z.Opens) ≤ ⊤), hh, hΦ U]
  have hgA : h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = g := by
    apply eq_of_secAlg_top
    rw [secAlg_comp, hh]
    obtain ⟨Ψ, -, hΨu⟩ := GlobalTheory.T.ring_map_from_affine_opens Z A (fun U => secAlg A g U) (fun U V hUV => secAlg_res A g hUV)
    have h1 := hΨu (Φ.comp (algebraMap A C)) (fun U => by
      rw [← RingHom.comp_assoc, hΦ U]; ext a; exact hφA U a)
    have h2 := hΨu (secAlg A g ⊤) (fun U => secAlg_res A g le_top)
    rw [h1, h2]
  refine ⟨h, ?_, ?_⟩
  · subst hgA
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    apply GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections
    intro U
    obtain ⟨φ', hφ', hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U
    letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
    refine (hker.trans ?_).trans (hφ U).symm
    congr 2
    exact AlgHom.ext fun c => congrArg (fun F => F c) (hφ'.trans (hhU U))
  · intro h' hh'
    have hU : ∀ U : Z.affineOpens, secAlg C h' U = φ U := by
      intro U
      obtain ⟨φ', hφ', hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h' U
      cases hh'
      rw [← hφ']
      exact hφu U φ' hker
    have hΦ' : secAlg C h' ⊤ = Φ := hΦu _ (fun U => by rw [secAlg_res, hU U])
    exact eq_of_secAlg_top C (hΦ'.trans hh.symm)

theorem chart_represents (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) :
    ∃ (X : Scheme.{0}) (x : (functor A B r).obj (op X)), IsAffine X ∧ LocallyOfFiniteType x.1 ∧
      Basic A B e σ x ∧ ∀ (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)), Basic A B e σ y →
        ∃! g : Z ⟶ X, (functor A B r).map g.op x = y := by
  obtain ⟨C, _, _, J, hfp, hli, hsp, huniv⟩ := GlobalTheory.hilbChart_representable A B N r e σ
  have hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J) :=
    GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis A B C J (fun k => e (σ k)) hli hsp
  let x : (functor A B r).obj (op (Spec (CommRingCat.of C))) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩
  have hBx : ∀ (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)),
      Basic A B e σ ((functor A B r).map h.op x) := by
    intro Z h
    rw [functor_map, basic_iff_kappa]
    intro U
    obtain ⟨φ, -, hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U
    letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
    obtain ⟨hli', hsp'⟩ := GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J φ hli hsp
    refine (GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mpr ⟨GlobalTheory.T.affineHilbertTensorToSubschemeSections_surjective A B _ _ U, ?_, ?_⟩
    · rw [hker]; exact hli'
    · rw [hker]; exact hsp'
  have hBasic : Basic A B e σ x := by
    simpa using hBx _ (𝟙 _)
  refine ⟨Spec (CommRingCat.of C), x, inferInstance, ?_, hBasic, ?_⟩
  · show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A C)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    haveI := hfp
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  intro Z y hy
  obtain ⟨g, I, hI⟩ := y
  rw [basic_iff_kappa] at hy
  exact exists_unique_lift A B e σ C J hli hsp huniv hgood Z g I hI hy
end GlobalTheory.HilbAff
end
end
