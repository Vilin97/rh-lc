module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTotallyRealEvenNegPlacesLocalNorm
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OmStable
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwoMulFinrank
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GeneratesDiffMap
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsFractionRingOfIntegers
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.FinrankWAddConj

section

@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem eigQuot_lattice {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
    {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
    (ρ : 𝓞 E →+* Module.End C Ω) (σ : E →+* C) (X : Submodule O Ω) (hX : X.IsLattice C) :
    (latIn (eigQuot ρ σ X) (eigSp ρ σ)).IsLattice C := by
  let f : Ω →ₗ[O] eigSp ρ σ :=
    ((eigProj ρ σ).codRestrict (eigSp ρ σ) (LatBasic.eigProj_mem ρ σ)).restrictScalars O
  have hmap : latIn (eigQuot ρ σ X) (eigSp ρ σ) = X.map f := by
    ext x
    change (∃ y ∈ X, eigProj ρ σ y = (x : Ω)) ↔ ∃ y ∈ X, f y = x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, Subtype.ext h⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, congrArg Subtype.val h⟩
  haveI : IsFractionRing O C := hv.isFractionRing
  rw [hmap]
  exact Submodule.IsLattice.of_fg C (hX.fg.map f)

theorem pt_om_block : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω) (σ : E →+* C), P.omHT σ ≤ P.omRec σ ∧ (∀ x ∈ P.omRec σ, κ • x ∈ P.omHT σ) ∧ (latIn (P.omHT σ) (P.Ωsp σ)).IsLattice C ∧ (latIn (P.omRec σ) (P.Ωsp σ)).IsLattice C := by
  intro C _ v O _ _ hv _ _ E _ _ c hc κ N V _ _ _ _ Ω _ _ _ _ P σ
  refine ⟨Submodule.map_mono ?_, ?_, eigQuot_lattice hv _ _ _ (PtBasic.om'_lattice P),
    eigQuot_lattice hv _ _ _ P.om_lat.toIsLattice⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact P.ht_mem x hx
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, e⟩ := P.κ_mem y hy
    exact ⟨κ • y, ⟨x, hx, e⟩, map_smul _ _ _⟩

section

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem e_eigProj (hc : ∀ x, c (c x) = x) (σ : E →+* C) {x : V} (hx : x ∈ eigSp P.ρ σ) (y : V) :
    P.e x (eigProj P.ρ (σ.comp c.toRingHom) y) = P.e x y := by
  have h : ∀ a : 𝓞 E, P.e x (P.ρ a y) = σ (c (a : E)) * P.e x y := by
    intro a
    have h1 := P.adj (RingOfIntegers.mapRingEquiv c a) x y
    have h2 : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      ext; exact hc _
    rw [h2, LatBasic.mem_eigSp.1 hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    exact h1.symm

  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_eq_mul,
  ← mul_assoc]
  rw [← Finset.sum_mul]
  have : ∑ k, (σ.comp c.toRingHom) (dualInt E k) * σ (c ((RingOfIntegers.basis E k : 𝓞 E) : E)) = 1 := by

    rw [← map_one (σ.comp c.toRingHom), ← LatBasic.sum_dualInt_mul, map_sum]
    simp
  rw [this, one_mul]

theorem finrank_eigSp [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O) (σ : E →+* C) :
    finrank C (eigSp P.ρ σ) = N := by
  obtain ⟨h1, d, -, -, h2⟩ := exists_diff_generator C v O hv E σ
  obtain ⟨-, -, h3, h4⟩ := SubDiffQuot.eigSub_eq_different_smul_eigQuot O C V E P.ρ P.T N P.t σ d
    hv.hom_inj h1 h2 P.free
  rw [← h4, finrank_span_eq_card h3, Fintype.card_fin]

theorem finrank_W_add_Ω [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O) (σ : E →+* C) :
    finrank C (P.Wsp σ) + finrank C (P.Ωsp σ) = N := by
  haveI := PtBasic.finite_V P
  let f := P.ht ∘ₗ (eigSp P.ρ σ).subtype
  have h := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range f = P.Ωsp σ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change P.ht x ∈ eigSp _ _
      rw [← LatBasic.eigProj_of_mem x.2, PtBasic.ht_eigProj]
      exact LatBasic.eigProj_mem _ _ _
    · intro y hy
      obtain ⟨x, rfl⟩ := PtBasic.ht_surjective P y
      refine ⟨⟨_, LatBasic.eigProj_mem P.ρ σ x⟩, ?_⟩
      change P.ht (eigProj P.ρ σ x) = _
      rw [PtBasic.ht_eigProj, LatBasic.eigProj_of_mem hy]
  have hk : finrank C (LinearMap.ker f) = finrank C (P.Wsp σ) := by
    rw [← Submodule.finrank_map_subtype_eq, LinearMap.ker_comp, Submodule.map_comap_subtype,
      inf_comm]
    rfl
  rw [hr, hk, finrank_eigSp P hv] at h
  omega

theorem finrank_W_add_conj [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O)
    (hc : ∀ x, c (c x) = x) (σ : E →+* C) :
    finrank C (P.Wsp σ) + finrank C (P.Wsp (σ.comp c.toRingHom)) = N := by
  haveI := PtBasic.finite_V P
  set τ := σ.comp c.toRingHom
  let B : eigSp P.ρ σ →ₗ[C] Module.Dual C (eigSp P.ρ τ) :=
    (P.e.domRestrict₁₂ (eigSp P.ρ σ) (eigSp P.ρ τ))
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have : (x : V) = 0 := P.nondeg _ fun y => by
      rw [PtBasic.e_skew, ← e_eigProj P hc σ x.2, neg_eq_zero]
      exact congrArg (fun φ => φ ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩) (LinearMap.mem_ker.1 hx)
    exact Subtype.ext this
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, finrank_eigSp P hv, finrank_eigSp P hv])).1 hinj
  let W₁ : Submodule C (eigSp P.ρ σ) := P.W.comap (eigSp P.ρ σ).subtype
  let W₂ : Submodule C (eigSp P.ρ τ) := P.W.comap (eigSp P.ρ τ).subtype
  have hW : W₁ = W₂.dualAnnihilator.comap B := by
    ext x
    rw [Submodule.mem_comap (f := B), Submodule.mem_dualAnnihilator]
    change P.ht x = 0 ↔ _
    rw [P.lagr]
    refine ⟨fun h w hw => h w hw, fun h y hy => ?_⟩
    rw [← e_eigProj P hc σ x.2]
    refine h ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩ ?_
    change P.ht (eigProj P.ρ τ y) = 0
    rw [PtBasic.ht_eigProj, hy, map_zero]
  have e1 : finrank C W₁ = finrank C W₂.dualAnnihilator := by
    rw [← (LinearEquiv.ofBijective B ⟨hinj, hsurj⟩).finrank_map_eq W₁, hW]
    exact congrArg (fun U : Submodule C (Module.Dual C (eigSp P.ρ τ)) => finrank C U)
      (Submodule.map_comap_eq_of_surjective hsurj _)
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W₂
  have e3 : ∀ s : E →+* C, finrank C (P.W.comap (eigSp P.ρ s).subtype) = finrank C (P.Wsp s) := by
    intro s
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]
    rfl
  rw [← e1, finrank_eigSp P hv, e3, e3] at e2
  omega

theorem finrank_Ω_add_Ω [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O)
    (hc : ∀ x, c (c x) = x) (σ : E →+* C) :
    finrank C (P.Ωsp σ) + finrank C (P.Ωsp (σ.comp c.toRingHom)) = N := by
  have h1 := finrank_W_add_Ω P hv σ
  have h2 := finrank_W_add_Ω P hv (σ.comp c.toRingHom)
  have h3 := finrank_W_add_conj P hv hc σ
  omega

end

end PositivityTheory.HtPt.Gb
end
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.RedOmHTBc

section

@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

theorem red_omHT_bc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[algebraMap A O] Ω') (hred : D.ReducesTo (algebraMap A O) P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (algebraMap A O a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → Module.Projective A (D.omHT σ) → ∃ j : O ⊗[A] (D.omHT σ) →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = P.omHT σ' ∧ (∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → algebraMap A O d • j (1 ⊗ₜ z) = ι y) ∧ Module.finrank A (D.omHT σ) = Module.finrank C (P.Ωsp σ') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D C _ _ _ v O _ _ hv _ κ' V _ _ _ _
    Ω' _ _ _ _ P ι hred σ σ' d hφ hd hκ hproj
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have := isFractionRing_of_integers hv
  have hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range := fun a =>
    IsIntegrallyClosed.isIntegral_iff.1
      ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)
  obtain ⟨hd', h1, h2, h3, -⟩ := red_proj A K hAK E c hc p R N Ω D C v O hv κ' V Ω'
    (algebraMap A O) P ι hred σ σ' d hσ hφ hd hκ
  have hδ : algebraMap O C (algebraMap A O d) ≠ 0 :=
    (different_generator_dualInt O C E σ' _ hv.hom_inj
      (exists_diff_generator C v O hv E σ').1 hd').1
  obtain ⟨j₀, hj₀, -, hj₀'⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  have hfg : (D.omHT σ).FG := by
    have : IsNoetherian A D.om := isNoetherian_of_fg_of_noetherian _ D.om_lat.fg
    have h := (IsNoetherian.noetherian (D.om'.comap D.om.subtype)).map D.om.subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (om'_le_om D)] at h
    exact h.map _
  have : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.2 hfg
  let α : D.omHT σ →ₗ[A] D.om := LinearMap.codRestrict D.om (d • (D.omHT σ).subtype) (by
    rintro ⟨_, x, hx, rfl⟩
    exact h1 x (om'_le_om D hx))
  let β : D.om →ₗ[A] D.omHT σ := LinearMap.codRestrict (D.omHT σ)
    ((eigProj D.ρΩ σ).restrictScalars A ∘ₗ ((p : A) ^ R • D.om.subtype))
    (fun x => ⟨_, pow_smul_mem_om' D x.2, rfl⟩)
  have hβα : β ∘ₗ α = ((p : A) ^ R * d) • LinearMap.id := by
    ext z
    change eigProj D.ρΩ σ ((p : A) ^ R • d • (z : Ω)) = ((p : A) ^ R * d) • (z : Ω)
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LatBasic.eigProj_of_mem (LatBasic.eigQuot_le_eigSp _ _ D.om' z.2), mul_smul]
  have hne : algebraMap A O ((p : A) ^ R * d) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap O C) h
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_zero] at h'
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) hδ h'
  have hα : Function.Injective (α.baseChange O) := by
    have h : Function.Injective ((β.baseChange O) ∘ₗ (α.baseChange O)) := by
      rw [← LinearMap.baseChange_comp, hβα, LinearMap.baseChange_smul, LinearMap.baseChange_id]
      intro x y e
      change ((p : A) ^ R * d) • x = ((p : A) ^ R * d) • y at e
      rw [← algebraMap_smul O, ← algebraMap_smul O ((p : A) ^ R * d) y] at e
      exact smul_right_injective _ hne e
    exact Function.Injective.of_comp h
  obtain ⟨j₁, hj₁, hr₁⟩ := exists_lift (ι.comp α)
  have hj₁' : j₁ = j₀ ∘ₗ α.baseChange O := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul o z =>
      have : o ⊗ₜ[A] z = o • ((1 : O) ⊗ₜ[A] z) := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, hj₁, LinearMap.comp_apply j₀, LinearMap.baseChange_tmul, hj₀']
      rfl
  let s : Ω' →ₗ[O] Ω' :=
    ((algebraMap O C (algebraMap A O d))⁻¹ • (LinearMap.id : Ω' →ₗ[C] Ω')).restrictScalars O
  have hs : ∀ w, algebraMap A O d • s w = w := fun w => by
    change algebraMap A O d • (algebraMap O C (algebraMap A O d))⁻¹ • w = w
    rw [← algebraMap_smul C, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  have hinj : Function.Injective (s ∘ₗ j₁) := by
    have hs' : Function.Injective s := fun x y e => by rw [← hs x, e, hs]
    rw [hj₁']
    exact hs'.comp (hj₀.comp hα)
  have hrange : LinearMap.range (s ∘ₗ j₁) = P.omHT σ' := by
    have e : Set.range (ι.comp α) = ι '' {y : D.om | ∃ z ∈ D.omHT σ, (y : Ω) = d • z} := by
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨α z, ⟨z, z.2, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, e⟩, rfl⟩
        exact ⟨⟨z, hz⟩, congrArg ι (Subtype.ext e.symm)⟩
    rw [LinearMap.range_comp, hr₁, e, h3, ← Submodule.map_comp]
    have : s ∘ₗ (algebraMap A O d • LinearMap.id) = LinearMap.id := by
      ext w
      change s (algebraMap A O d • w) = w
      rw [map_smul, hs]
    rw [this, Submodule.map_id]
  refine ⟨s ∘ₗ j₁, hinj, hrange, fun z y e => ?_, ?_⟩
  · rw [LinearMap.comp_apply, hs, hj₁]
    exact congrArg ι (Subtype.ext e.symm)
  · have hl := (pt_om_block C v O hv E c hc κ' N V Ω' P σ').2.2.1
    have hfull : (latIn (P.omHT σ') (P.Ωsp σ')).IsFullLattice C := by
      refine { toIsLattice := hl, span_eq_top := ?_ }
      apply eq_top_iff.mpr
      intro x _
      have hx : (x : Ω') ∈ Submodule.span C (P.om : Set Ω') := by
        rw [P.om_lat.span_eq_top]
        trivial
      obtain ⟨a, ha, hay⟩ := exists_smul_mem_of_mem_span_val hv P.om hx
      obtain ⟨z, hz, hze⟩ := P.κ_mem (a • (x : Ω')) hay
      have hm : (algebraMap O C κ' * a) • x ∈ latIn (P.omHT σ') (P.Ωsp σ') := by
        change (algebraMap O C κ' * a) • (x : Ω') ∈ P.omHT σ'
        refine ⟨P.ht z, ⟨z, hz, rfl⟩, ?_⟩
        rw [hze, ← algebraMap_smul C, smul_smul]
        change eigProj P.ρΩ σ' ((algebraMap O C κ' * a) • (x : Ω')) = _
        rw [map_smul, LatBasic.eigProj_of_mem x.2]
      have hm' := Submodule.subset_span hm (R := C)
      have hn : algebraMap O C κ' * a ≠ 0 := mul_ne_zero P.κ_ne ha
      have := (Submodule.span C (latIn (P.omHT σ') (P.Ωsp σ') : Set (P.Ωsp σ'))).smul_mem
        (algebraMap O C κ' * a)⁻¹ hm'
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul] at this
      exact this
    rw [← finrank_baseChange_flat (O := O), ← LinearMap.finrank_range_of_inj hinj, hrange,
      ← finrank_lattice _ hfull]
    have e : (latIn (P.omHT σ') (P.Ωsp σ')).map ((P.Ωsp σ').subtype.restrictScalars O) =
        P.omHT σ' := by
      rw [LatBasic.map_latIn]
      exact inf_eq_left.2 (LatBasic.eigQuot_le_eigSp _ _ _)
    conv_lhs => rw [← e]
    exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq.symm

theorem chart_rank : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ σ d d' hp hκ hd hd' hP hP' htest
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hp0 : (p : A) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap A K) h
    rw [map_natCast, map_zero] at h'
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero h'
  obtain ⟨𝔮, h𝔮⟩ := Ideal.nonempty_minimalPrimes (I := Ideal.span {(p : A)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hprime : 𝔮.IsPrime := h𝔮.1.1
  have hmem : (p : A) ∈ 𝔮 := h𝔮.1.2 (Ideal.mem_span_singleton_self _)
  have hht : 𝔮.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h𝔮) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    rintro rfl
    exact hp0 hmem
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, -, hred⟩ :=
    htest 𝔮 hprime hht hmem
  let _ : Algebra A O := φ.toAlgebra
  have hg : Function.Injective ((algebraMap O C).comp φ) := hv.hom_inj.comp hφ
  let ψ : K →+* C := IsFractionRing.lift hg
  have hψ : ∀ (τ : E →+* K) (a : 𝓞 E) (a' : A), algebraMap A K a' = τ (a : E) →
      algebraMap O C (algebraMap A O a') = (ψ.comp τ) (a : E) := fun τ a a' h => by
    rw [RingHom.comp_apply, ← h]
    exact (IsFractionRing.lift_algebraMap hg a').symm
  have hκ' : φ κ ∣ (p : O) ^ R := by
    have := map_dvd φ hκ
    rwa [map_pow, map_natCast] at this
  obtain ⟨_, -, -, -, e1⟩ := red_omHT_bc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred σ
    (ψ.comp σ) d (hψ σ) hd hκ' hP
  obtain ⟨_, -, -, -, e2⟩ := red_omHT_bc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred
    (σ.comp c.toRingHom) (ψ.comp (σ.comp c.toRingHom)) d' (hψ _) hd' hκ' hP'
  rw [e1, e2]
  exact finrank_Ω_add_Ω P hv hc (ψ.comp σ)

end PositivityTheory.HtPt.Gb
end
end
end
