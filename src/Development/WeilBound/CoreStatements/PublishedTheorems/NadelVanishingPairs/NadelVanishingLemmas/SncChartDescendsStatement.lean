module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpenStatement
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFibreEquivPushoutFormallyEtale
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
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerAffineChartStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFibreEquivPushoutFormallyEtaleStatement

section

@[expose] public section

open scoped TensorProduct Polynomial

theorem _root_.GlobalTheory.T.exists_kaehler_fibre_equiv_D_compat : ∀ (R R' B C B' K : Type) [CommRing R] [CommRing R'] [CommRing B] [CommRing C] [CommRing B'] [Field K] [Algebra R R'] [Algebra R B] [Algebra R C] [Algebra R' C] [Algebra B C] [IsScalarTower R R' C] [IsScalarTower R B C] [Algebra.IsPushout R R' B C] [Algebra C B'] [Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [Algebra B' K] [Algebra B K], (∀ x : B, algebraMap B K x = algebraMap B' K (algebraMap C B' (algebraMap B C x))) → ∃ e : (K ⊗[B] Ω[B⁄R]) ≃ₗ[K] (K ⊗[B'] Ω[B'⁄R']), ∀ x : B, e ((1 : K) ⊗ₜ[B] KaehlerDifferential.D R B x) = (1 : K) ⊗ₜ[B'] KaehlerDifferential.D R' B' (algebraMap C B' (algebraMap B C x)) := by
  first | exact @GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale | exact GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale | (intros; apply GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDifferentials

section

@[expose] public section

open scoped TensorProduct Polynomial

namespace GlobalTheory.EtaleCoordRank

open KaehlerDifferential TensorProduct

theorem finrank_and_linearIndependent_D_unit_mul : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  intro R B K _ _ _ _ _ d t h
  have key : ∃ b : Module.Basis (Fin d) B Ω[B⁄R], ∀ i, b i = D R B (t i) := by
    letI : Algebra (MvPolynomial (Fin d) R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin d) R) B :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R B r = MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.C r)
        simp
    haveI : Algebra.Etale (MvPolynomial (Fin d) R) B := h
    obtain ⟨⟨b, hb⟩, _⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B (Fin d)
    refine ⟨b, fun i => ?_⟩
    rw [hb]
    congr 1
    change MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.X i) = t i
    simp
  obtain ⟨b, hb⟩ := key
  let b' : Module.Basis (Fin d) K (K ⊗[B] Ω[B⁄R]) := b.baseChange K
  refine ⟨by rw [Module.finrank_eq_card_basis b', Fintype.card_fin], ?_⟩
  intro ι e u ht
  have hli : LinearIndependent K (fun i => b' (e i)) := b'.linearIndependent.comp e e.injective
  have hfun : (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) =
      (fun i => Units.map (algebraMap B K : B →* K) (u i)) • (fun i => b' (e i)) := by
    funext i
    simp only [Pi.smul_apply', Units.smul_def, Units.coe_map, MonoidHom.coe_coe, b',
      Module.Basis.baseChange_apply, hb]
    rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, ← algebraMap_smul K (u i : B),
      ← algebraMap_smul K (t (e i)), ht, zero_smul, add_zero]
  rw [hfun]
  exact hli.units_smul _

end GlobalTheory.EtaleCoordRank
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesDifferentials

section

@[expose] public section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.etale_coordinates_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  first | exact @_root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | exact _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | (intros; apply _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescends

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.ChartDesc

theorem resG_etale (X : Scheme.{0}) (U W : X.Opens) (h : W ≤ U) (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : (resG X h).Etale := by
  have := HasRingHomProperty.appLE (P := @Etale) (𝟙 X) (inferInstanceAs (Etale (𝟙 X))) ⟨U, hU⟩
    ⟨W, hW⟩ (by simpa using h)
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] at this
  exact this

theorem chart_desc : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π)) (y : X'), IsPullback π f' f (spMap φ) → y ∈ C'.U → ∃ C : SncChart f d L σ, π y ∈ C.U := by
  intro R R' _ _ φ X X' f f' π _ d s L σ C' y H hy
  let c : ∀ i, (L i).ι := fun i => C'.c i ⟨⟩
  have hyc : ∀ i, π y ∈ (L i).U (c i) := fun i => by
    exact (Cartier.pull_U (L i) π (C'.c i)).le (C'.le i hy)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_iInter.2 hyc) (isOpen_iInter_of_finite fun i => ((L i).U (c i)).isOpen)
  have hc : ∀ i, (U : X.Opens) ≤ (L i).U (c i) := fun i _ hz => Set.mem_iInter.1 (hUle hz) i
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((C'.U ⊓ π ⁻¹ᵁ U : X'.Opens) : Set X') from ⟨hy, hxU⟩) (C'.U ⊓ π ⁻¹ᵁ U).isOpen
  have hWC : (W : X'.Opens) ≤ C'.U := fun _ hz => (hWle hz).1
  have hWU : (W : X'.Opens) ≤ π ⁻¹ᵁ U := fun _ hz => (hWle hz).2

  have hA : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (Qcqs.baseRingHom f U) (CommRingCat.ofHom φ) (π.app U)
      (Qcqs.baseRingHom f' (π ⁻¹ᵁ U)) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Qcqs.baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [Qcqs.baseRingHom]
  let K := X'.residueField y
  letI : Algebra R R' := φ.toAlgebra
  letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra
  letI : Algebra R' Γ(X', π ⁻¹ᵁ U) := (cstOn f' (π ⁻¹ᵁ U)).toAlgebra
  letI : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  letI : Algebra R Γ(X', π ⁻¹ᵁ U) := ((cstOn f' (π ⁻¹ᵁ U)).comp φ).toAlgebra
  letI : Algebra Γ(X', π ⁻¹ᵁ U) Γ(X', W) := (resG X' hWU).toAlgebra
  letI : Algebra R' Γ(X', W) := (cstOn f' W).toAlgebra
  letI : Algebra Γ(X', W) K := (X'.evaluation W y hyW).hom.toAlgebra
  letI : Algebra Γ(X, U) K :=
    ((X'.evaluation W y hyW).hom.comp ((resG X' hWU).comp (π.app U).hom)).toAlgebra
  haveI : IsScalarTower R R' Γ(X', π ⁻¹ᵁ U) := .of_algebraMap_eq fun r ↦ rfl
  have e2 : ∀ r : R, (π.app U).hom (cstOn f U r) = cstOn f' (π ⁻¹ᵁ U) (φ r) := fun r => by
    have h1 := Qcqs.app_baseRingHom π f U r
    have h2 : Qcqs.baseRingHom (π ≫ f) (π ⁻¹ᵁ U) r = Qcqs.baseRingHom f' (π ⁻¹ᵁ U) (φ r) := by
      rw [H.w, Qcqs.baseRingHom_comp_SpecMap]; rfl
    exact h1.trans h2
  haveI : IsScalarTower R Γ(X, U) Γ(X', π ⁻¹ᵁ U) := .of_algebraMap_eq fun r ↦ (e2 r).symm
  haveI : Algebra.IsPushout R R' Γ(X, U) Γ(X', π ⁻¹ᵁ U) := by
    have po'' : IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, U))) (CommRingCat.ofHom (algebraMap R R'))
        (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U)))
        (CommRingCat.ofHom (algebraMap R' Γ(X', π ⁻¹ᵁ U))) := po'
    exact (CommRingCat.isPushout_iff_isPushout.mp po'').symm
  haveI : IsScalarTower R' Γ(X', π ⁻¹ᵁ U) Γ(X', W) := .of_algebraMap_eq fun r ↦
    (Qcqs.baseRingHom_res f' hWU r).symm
  haveI : Algebra.FormallyEtale Γ(X', π ⁻¹ᵁ U) Γ(X', W) := by
    haveI : Algebra.Etale Γ(X', π ⁻¹ᵁ U) Γ(X', W) := resG_etale X' _ _ hWU hU' hW
    infer_instance

  let t : Fin d → Γ(X', W) := fun a => resG X' hWC (C'.t a)
  have ht : IsEtCoord f' W t := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R' X' f' C'.U W hWC d C'.t C'.affine hW C'.etale
  have hbasis := GlobalTheory.T.etale_coordinates_differentials R' Γ(X', W) K d t ht
  obtain ⟨ebc, hebc⟩ := GlobalTheory.T.exists_kaehler_fibre_equiv_D_compat R R' Γ(X, U) Γ(X', π ⁻¹ᵁ U) Γ(X', W) K (fun _ => rfl)
  have key : ∀ i, algebraMap Γ(X', π ⁻¹ᵁ U) Γ(X', W)
      (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U) (resG X (hc i) ((σ i).f (c i)))) =
      ((Units.map (resG X' hWC).toMonoidHom (C'.u i) : Γ(X', W)ˣ) : Γ(X', W)) *
        resG X' hWC ((C'.e i).elim 1 C'.t) := by
    intro i
    have e := congrArg (resG X' hWC) (C'.eq i)
    rw [map_mul] at e
    refine Eq.trans ?_ e
    show resG X' hWU ((π.app U).hom (resG X (hc i) ((σ i).f (c i)))) =
      resG X' hWC (resG X' (C'.le i) (resG X' _ ((π.app _).hom ((σ i).f (C'.c i ⟨⟩)))))
    rw [Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG, Cartier.resG_resG]
  have hunit : ∀ v : Γ(X', W)ˣ, algebraMap Γ(X', W) K v ≠ 0 := fun v =>
    (v.isUnit.map (algebraMap Γ(X', W) K)).ne_zero
  have hres : ∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ π y ∈ X.basicOpen a := by
    intro a
    change (X'.evaluation W y hyW).hom (resG X' hWU ((π.app U).hom a)) ≠ 0 ↔ _
    rw [Ne, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]
    change y ∈ X'.basicOpen ((X'.presheaf.map (homOfLE hWU).op).hom _) ↔ _
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact ⟨fun h => h.2, fun h => ⟨hyW, h⟩⟩
  have hrank : Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d :=
    ebc.finrank_eq.trans hbasis.1
  have hvan : ∀ i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0},
      ∃ a, C'.e i.1 = some a ∧ algebraMap Γ(X', W) K (t a) = 0 := by
    rintro ⟨i, hi⟩
    have h0 : algebraMap Γ(X', W) K (algebraMap Γ(X', π ⁻¹ᵁ U) Γ(X', W)
        (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U) (resG X (hc i) ((σ i).f (c i))))) = 0 := hi
    rw [key i, map_mul] at h0
    rcases hE : C'.e i with _ | a
    · rw [hE] at h0
      simp only [Option.elim, map_one, mul_one] at h0
      exact absurd h0 (hunit _)
    · refine ⟨a, rfl, ?_⟩
      rw [hE] at h0
      exact (mul_eq_zero.1 h0).resolve_left (hunit _)
  choose g hg hg0 using hvan
  let emb : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} ↪ Fin d :=
    ⟨g, fun i j hij => Subtype.ext (C'.inj i.1 j.1 (g i) (hg i) (by rw [hij]; exact hg j))⟩
  let u : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} → Γ(X', W)ˣ :=
    fun i => Units.map (resG X' hWC).toMonoidHom (C'.u i.1)
  have hli := hbasis.2 _ emb u hg0
  have hfam : ∀ i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0},
      ebc ((1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i.1) ((σ i.1).f (c i.1)))) =
      (1 : K) ⊗ₜ[Γ(X', W)] KaehlerDifferential.D R' Γ(X', W) ((u i : Γ(X', W)) * t (emb i)) := by
    intro i
    rw [hebc, key i.1, hg i]
    rfl
  have hlin : LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K
      (resG X (hc i) ((σ i).f (c i))) = 0} =>
      (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i.1) ((σ i.1).f (c i.1)))) := by
    refine LinearIndependent.of_comp ebc.toLinearMap ?_
    convert hli using 1
    funext i
    exact hfam i
  exact GlobalTheory.T.finrank_kaehler_affine_chart R X f d s L σ U c hc (π y) K hU hxU hres ⟨hrank, hlin⟩

end GlobalTheory.ChartDesc
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescendsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.snc_chart_descends : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π)) (y : X'), IsPullback π f' f (spMap φ) → y ∈ C'.U → ∃ C : SncChart f d L σ, π y ∈ C.U := by
  first | exact @_root_.GlobalTheory.ChartDesc.chart_desc | exact _root_.GlobalTheory.ChartDesc.chart_desc | (intros; apply _root_.GlobalTheory.ChartDesc.chart_desc <;> assumption)
end
end
