module

public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AdmissibleLatticesCommensurable
public import Formalism.WeaklyAdmissibleFiltrations.Statement
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsLatticeEqAddSmulOfStableFgSubmodule

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule :
    ∀ {G O LL V : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (ρ : Representation LL G V)
      (Λ : Lattice (O := O) ρ) (A : Submodule O V), A.FG → (∀ g, ∀ a ∈ A, ρ g a ∈ A) → ∀ μ : O, μ ≠ 0 →
      ∃ L : Lattice (O := O) ρ, ∀ v, v ∈ L.T ↔ ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u := by
  intro G O LL V _ _ _ _ _ _ _ _ _ _ _ ρ Λ A hA hst μ hμ
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hmem : ∀ v, v ∈ A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)) ↔
      ∃ a ∈ A, ∃ u ∈ Λ.T, v = a + μ • u := by
    intro v
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, z, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨a, ha, u, hu, by simp⟩
    · rintro ⟨a, ha, u, hu, rfl⟩
      exact ⟨a, ha, μ • u, ⟨u, hu, by simp⟩, rfl⟩
  have hfg : (A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))).FG := hA.sup (Λ.fg.map _)
  have htf : Module.IsTorsionFree O V := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r m h
    rw [← algebraMap_smul LL r m, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  refine ⟨⟨A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V)), ?_, hfg, ?_, ?_⟩, hmem⟩
  · intro g x hx
    obtain ⟨a, ha, u, hu, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨ρ g a, hst g a ha, ρ g u, Λ.stable g u hu, ?_⟩
    rw [map_add (f := _), ← algebraMap_smul LL μ u, map_smul, algebraMap_smul]
  · haveI : Module.Finite O ↥(A ⊔ Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))) :=
      Module.Finite.iff_fg.2 hfg
    infer_instance
  · rw [eq_top_iff, ← Λ.span, Submodule.span_le]
    intro u hu
    have hne : algebraMap O LL μ ≠ 0 := fun h => hμ (hinj (by rw [h, map_zero]))
    have : u = (algebraMap O LL μ)⁻¹ • (μ • u) := by
      rw [← algebraMap_smul LL μ u, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hmem _).2 ⟨0, A.zero_mem, u, hu, by simp⟩))
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsLinearEquivQuotientOfLatticeSum

section

@[expose] public section

theorem _root_.UpperTheory.KN.exists_linearEquiv_quotient_of_lattice_sum :
    ∀ {O V A M : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup A] [Module O A] [AddCommGroup M] [Module O M]
      (j : A →ₗ[O] V) (q : A →ₗ[O] M) (B T₁ T₂ : Submodule O V), Function.Injective j → Function.Surjective q →
      (∀ a, j a ∈ B → q a = 0) → (∀ v, v ∈ T₁ ↔ ∃ a, ∃ b ∈ B, v = j a + b) → (∀ v, v ∈ T₂ ↔ ∃ a, q a = 0 ∧ ∃ b ∈ B, v = j a + b) →
      ∃ e : M ≃ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype), ∀ (a : A) (y : ↥T₁), e (q a) = Submodule.Quotient.mk y ↔ ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b := by
  intro O V A M _ _ _ _ _ _ _ j q B T₁ T₂ _ hq hB h1 h2
  have hj : ∀ a, j a ∈ T₁ := fun a => (h1 _).2 ⟨a, 0, B.zero_mem, by simp⟩
  let p : A →ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype) :=
    (T₂.comap T₁.subtype).mkQ ∘ₗ j.codRestrict T₁ hj
  have key : ∀ (a : A) (y : ↥T₁), p a = Submodule.Quotient.mk y ↔
      ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b := by
    intro a y
    have h : p a = Submodule.Quotient.mk y ↔ (y : V) - j a ∈ T₂ := by
      rw [eq_comm]
      exact Submodule.Quotient.eq (T₂.comap T₁.subtype)
    rw [h, h2]
    constructor
    · rintro ⟨a', ha', b, hb, hy⟩
      refine ⟨a' + a, by simp [ha'], b, hb, ?_⟩
      rw [map_add (f := _), add_right_comm, ← hy, sub_add_cancel]
    · rintro ⟨a', ha', b, hb, hy⟩
      refine ⟨a' - a, by simp [ha'], b, hb, ?_⟩
      rw [map_sub, hy]
      abel
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨a, b, hb, hy⟩ := (h1 _).1 y.2
    exact ⟨a, (key a y).2 ⟨a, rfl, b, hb, hy⟩⟩
  have hker : LinearMap.ker q = LinearMap.ker p := by
    ext a
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.Quotient.mk_zero, key]
    constructor
    · intro ha
      exact ⟨0, by simp [ha], 0, B.zero_mem, by simp⟩
    · rintro ⟨a', ha', b, hb, hy⟩
      rw [← ha']
      apply hB
      have : j a' = -b := eq_neg_of_add_eq_zero_left hy.symm
      rw [this]
      exact B.neg_mem hb
  refine ⟨(q.quotKerEquivOfSurjective hq).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (p.quotKerEquivOfSurjective hp)), fun a y => ?_⟩
  rw [← key]
  have h3 : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, h3]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsGaloisStableLatticeOfPeriodData

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

private theorem admissible_lattice_inclusion {G O LL V : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (ρ : Representation LL G V)
    (Λ : Lattice (O := O) ρ)
    {A : Type} [AddCommGroup A] [Module O A] [Module.Finite O A] (j : A →ₗ[O] V) (actA : G → A → A)
    {E : Type} [AddCommGroup E] [Module O E] (act : G → E → E) (S : Submodule O E)
    (q : A →ₗ[O] (E ⧸ S)) (c : O)
    (hj : Function.Injective j) (hact : ∀ g a, j (actA g a) = ρ g (j a)) (hq : Function.Surjective q)
    (hqa : ∀ g a x, q a = Submodule.Quotient.mk x → q (actA g a) = Submodule.Quotient.mk (act g x))
    (hc : c ≠ 0) (hcy : ∀ y : E ⧸ S, c • y = 0) :
    ∃ (L₁ L₂ : Lattice (O := O) ρ),
      L₂.T ≤ L₁.T ∧ ∃ e : (E ⧸ S) ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype),
        ∀ (g : G) (x : E) (y : ↥L₁.T), e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
          e (Submodule.Quotient.mk (act g x)) = Submodule.Quotient.mk ⟨ρ g y, L₁.stable g y y.2⟩ := by
  have h0 : ∀ g, actA g 0 = 0 := fun g => hj (by rw [hact, map_zero, map_zero])
  have hker : ∀ g a, q a = 0 → q (actA g a) = 0 := by
    intro g a ha
    have h1 := hqa g a 0 (by rw [ha]; rfl)
    have h2 := hqa g 0 0 (by rw [map_zero]; rfl)
    rw [h1, ← h2, h0, map_zero]
  obtain ⟨μ, hμ, hcom⟩ := UpperTheory.KN.admissible_lattices_commensurable (LL := LL) Λ.T (LinearMap.range j) Λ.fg c hc
  have fg1 : (LinearMap.range j).FG := by
    rw [← Submodule.map_top]
    exact Submodule.FG.map j Module.Finite.fg_top
  have fg2 : ((LinearMap.ker q).map j).FG :=
    Submodule.FG.map j (IsNoetherian.noetherian _)
  obtain ⟨L₁, hL₁⟩ := UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule ρ Λ (LinearMap.range j) fg1
    (by rintro g _ ⟨a, rfl⟩; exact ⟨actA g a, hact g a⟩) μ hμ
  obtain ⟨L₂, hL₂⟩ := UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule ρ Λ ((LinearMap.ker q).map j) fg2
    (by rintro g _ ⟨a, ha, rfl⟩; exact ⟨actA g a, hker g a ha, hact g a⟩) μ hμ
  let B : Submodule O V := Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))
  have hB : ∀ b, b ∈ B ↔ ∃ u ∈ Λ.T, μ • u = b := fun b => Iff.rfl
  obtain ⟨e, he⟩ := UpperTheory.KN.exists_linearEquiv_quotient_of_lattice_sum j q B L₁.T L₂.T hj hq
    (by
      intro a ha
      obtain ⟨u, hu, hua⟩ := (hB _).1 ha
      obtain ⟨_, ⟨a', rfl⟩, h⟩ := hcom u hu ⟨a, hua.symm⟩
      have : a = c • a' := hj (by rw [map_smul, ← h, hua])
      rw [this, map_smul, hcy])
    (by
      intro v
      rw [hL₁]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
        exact ⟨a, _, (hB _).2 ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨a, b, hb, rfl⟩
        obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
        exact ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩)
    (by
      intro v
      rw [hL₂]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩
        exact ⟨a, ha, _, (hB _).2 ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
        exact ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩)
  refine ⟨L₁, L₂, ?_, e, ?_⟩
  · intro v hv
    obtain ⟨_, ⟨a, _, rfl⟩, u, hu, rfl⟩ := (hL₂ v).1 hv
    exact (hL₁ _).2 ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
  · intro g x y hxy
    obtain ⟨a, ha⟩ := hq (Submodule.Quotient.mk x)
    rw [← ha] at hxy
    obtain ⟨a', ha', b, hb, hy⟩ := (he a y).1 hxy
    obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
    rw [← hqa g a' x (ha'.trans ha)]
    refine (he _ _).2 ⟨actA g a', rfl, μ • ρ g u, (hB _).2 ⟨_, Λ.stable g u hu, rfl⟩, ?_⟩
    show ρ g y = _
    rw [hy, map_add (f := _), hact, LinearMap.map_smul_of_tower]

theorem _root_.UpperTheory.KN.exists_galois_stable_lattice_of_period_data :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {m : ℕ} (F : Fin m → tableLineDegreeTwo.FullRep PD emb lam jT cT) (Λ : Lattice (O := O) (tableLineDegreeTwo.piRep F))
      {A : Type} [AddCommGroup A] [Module O A] [Module.Finite O A] (j : A →ₗ[O] (∀ k, (F k).V)) (actA : G → A → A)
      {E : Type} [AddCommGroup E] [Module O E] (act : G → E → E) (S : Submodule O E) (q : A →ₗ[O] (E ⧸ S)) (c : O),
      Function.Injective j → (∀ g a, j (actA g a) = tableLineDegreeTwo.piRep F g (j a)) → Function.Surjective q →
      (∀ g a x, q a = Submodule.Quotient.mk x → q (actA g a) = Submodule.Quotient.mk (act g x)) →
      c ≠ 0 → (∀ y : E ⧸ S, c • y = 0) → tableLineDegreeTwo.AdmQ PD emb lam jT cT act S := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ O _ _ _ _ _ nn emb lam jT cT
    m F Λ A _ _ _ j actA E _ _ act S q c hj hact hq hqa hc hcy
  exact ⟨m, F, admissible_lattice_inclusion (tableLineDegreeTwo.piRep F) Λ j actA act S q c hj hact hq hqa hc hcy⟩
end
end
