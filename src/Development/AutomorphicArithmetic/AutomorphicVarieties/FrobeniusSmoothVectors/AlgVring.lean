module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SingleMemOfSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVertex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLau
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgModel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLimit

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem alg_vring {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (hi : Function.Injective (algebraMap C K))
    (hn : IsNoetherianRing (lauSub P)) : IsVertexRing C (vertex h) := by
  have hcoeff : ∀ c : C, ((algebraMap C (lauSub P) c : lauSub P) : AddMonoidAlgebra K ℤ).coeff 0 = algebraMap C K c := by
    intro c
    simp
  refine ⟨hn, ?_, alg_sep h hn, ?_, ?_⟩
  · intro c c' hcc
    apply hi
    rw [← hcoeff c, ← hcoeff c', hcc]
  · ext c
    rw [Ideal.mem_comap, mem_vertex, hcoeff]
    constructor
    · rintro ⟨c', hc', he⟩
      rwa [← hi he]
    · intro hc
      exact ⟨c, hc, rfl⟩
  · intro d
    obtain ⟨c, hc⟩ := h.zero _ (d.2 0)
    refine ⟨c, ?_⟩
    rw [mem_vertex]
    refine ⟨0, (maximalIdeal C).zero_mem, ?_⟩
    simp [hc]

private theorem alg_ev (C K : Type) [CommRing C] [CommRing K] [Algebra C K] :
    ∃ e : AddMonoidAlgebra K ℤ →ₐ[C] K, ∀ j x, e (AddMonoidAlgebra.single j x) = x := by
  refine ⟨AddMonoidAlgebra.liftNCAlgHom (AlgHom.id C K) 1 (fun _ _ => Commute.one_right _), fun j x => ?_⟩
  exact (AddMonoidAlgebra.liftNC_single _ _ _ _).trans (by simp)

theorem UpperTheory.V.Fr.alg :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra O K] [Algebra C K] [IsScalarTower O C K], Function.Injective (algebraMap C K) → ∀ ρ : NRep F n K, Cone O C ρ → ∃ (ξ : S.A →ₐ[O] K) (β : S.B →ₐ[O] C), S.u.map (ξ : S.A →+* K) = ρ ∧ ∀ b, ξ (S.inc b) = algebraMap C K (β b) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ K _ _ _ _ hi ρ hcone
  have hv : HasVertex (ρ.part C) := by
    have hC := hcone
    have off : ∀ (L : List (F.G0 × Fin n × Fin n)) (j : ℤ),
        (L.map (fun s => w n s.2.1 - w n s.2.2)).sum = j → j ≠ 0 → ∃ s ∈ L, s.2.1 ≠ s.2.2 := by
      intro L j hL hj
      by_contra h
      push_neg at h
      apply hj
      rw [← hL]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      rw [h s hs, sub_self]
    constructor
    · intro x hx
      have hle : ρ.mon 0 ⊆ (LinearMap.range (Algebra.linearMap C K) : Set K) := by
        rintro _ ⟨L, hL, rfl⟩
        by_cases hd : ∃ s ∈ L, s.2.1 ≠ s.2.2
        · obtain ⟨c, -, hc⟩ := hC.cyc L hL hd
          exact ⟨c, hc⟩
        · push_neg at hd
          have hm : (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod ∈ (algebraMap C K).rangeS := by
            apply list_prod_mem
            intro y hy
            obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
            rw [← hd s hs]
            obtain ⟨c, hc, -⟩ := hC.dg s.1 s.2.1
            exact ⟨c, hc⟩
          obtain ⟨c, hc⟩ := hm
          exact ⟨c, hc⟩
      obtain ⟨c, hc⟩ := Submodule.span_le.2 hle hx
      exact ⟨c, hc⟩
    · intro j hj x hx y hy
      open Pointwise in
      have hle : ρ.mon j * ρ.mon (-j) ⊆
          (Submodule.map (Algebra.linearMap C K) (maximalIdeal C) : Set K) := by
        rintro _ ⟨a, ⟨L1, h1, rfl⟩, b, ⟨L2, h2, rfl⟩, rfl⟩
        obtain ⟨s, hs, hne⟩ := off L1 j h1 hj
        obtain ⟨c, hc, hc'⟩ := hC.cyc (L1 ++ L2)
          (by rw [List.map_append, List.sum_append, h1, h2]; ring) ⟨s, List.mem_append_left _ hs, hne⟩
        refine Submodule.mem_map.2 ⟨c, hc, ?_⟩
        rw [Algebra.linearMap_apply, hc', List.map_append, List.prod_append]
      open Pointwise in
      have hxy : x * y ∈ Submodule.span C (ρ.mon j * ρ.mon (-j)) := by
        rw [← Submodule.span_mul_span]
        exact Submodule.mul_mem_mul hx hy
      obtain ⟨c, hc, hc'⟩ := Submodule.mem_map.1 (Submodule.span_le.2 hle hxy)
      exact ⟨c, hc, hc'⟩
  haveI := alg_ft C ρ hcone.fg
  have hN : IsNoetherianRing (lauSub (NRep.part C ρ)) := Algebra.FiniteType.isNoetherianRing C _
  have hvr := alg_vring hv hi hN
  let lauT : Multiplicative ℤ →* (AddMonoidAlgebra K ℤ)ˣ :=
    (AddMonoidAlgebra.of K ℤ).toHomUnits
  have lauT_zpow (m : ℤ) :
      ((lauT (Multiplicative.ofAdd 1) ^ m : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) =
        AddMonoidAlgebra.single m 1 := by
    rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    rfl
  obtain ⟨ρD, h1, h2⟩ : ∃ ρD : NRep F n (lauSub (ρ.part C)),
      (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) ∧
      (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) := by
    obtain ⟨χ, -, hχ⟩ := hcone.psi
    obtain ⟨ρ', hr, hψ⟩ := alg_twist (lauT (Multiplicative.ofAdd 1))
      (NRep.map (AddMonoidAlgebra.singleZeroRingHom : K →+* AddMonoidAlgebra K ℤ) ρ)
    have hr' : ∀ g i j, ρ'.r g i j = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) := by
      intro g i j
      rw [hr, lauT_zpow, NRep.map_r]
      simp [AddMonoidAlgebra.single_mul_single]
    have hψ' : ∀ v i g, ((ρ'.ψ v i g : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) =
        AddMonoidAlgebra.single 0 (ρ.ψ v i g : K) := by
      intro v i g
      rw [hψ]
      rfl
    have h1 : ∀ g i j, ρ'.r g i j ∈ lauSub (ρ.part C) := by
      intro g i j
      rw [hr']
      exact single_mem_lauSub _ (NRep.r_mem_part C ρ g i j)
    have h2 : ∀ v i g, ((ρ'.ψ v i g : (AddMonoidAlgebra K ℤ)ˣ) : AddMonoidAlgebra K ℤ) ∈
        lauSub (ρ.part C) := by
      intro v i g
      rw [hψ']
      apply single_mem_lauSub
      rw [← hχ, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
    exact ⟨NRep.restrict ρ' (lauSub (ρ.part C)) h1 h2, fun g i j => hr' g i j,
      fun v i g => hψ' v i g⟩
  have hmod := alg_model C ρ hcone hv ρD h1 h2
  letI : Algebra O (lauSub (NRep.part C ρ)) :=
    ((algebraMap C (lauSub (NRep.part C ρ))).comp (algebraMap O C)).toAlgebra
  haveI : IsScalarTower O C (lauSub (NRep.part C ρ)) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ξ, β, hξ, hβ⟩ := alg_limit S C (vertex hv) ρD hvr hmod
  obtain ⟨e, he⟩ := alg_ev C K
  let ev : lauSub (NRep.part C ρ) →ₐ[O] K := (e.comp (lauSub (NRep.part C ρ)).val).restrictScalars O
  refine ⟨ev.comp ξ, β, ?_, fun b => ?_⟩
  · apply NRep.ext
    · ext g i j
      rw [NRep.map_r]
      have hr := NRep.map_r (ξ : S.A →+* lauSub (NRep.part C ρ)) S.u g i j
      rw [hξ] at hr
      show e ((ξ (S.u.r g i j) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
      have hr' : ξ (S.u.r g i j) = ρD.r g i j := hr.symm
      rw [hr', h1, he]
    · funext v i
      ext g
      rw [NRep.map_ψ]
      have hp := NRep.map_ψ (ξ : S.A →+* lauSub (NRep.part C ρ)) S.u v i g
      rw [hξ] at hp
      show e ((ξ ((S.u.ψ v i g : S.Aˣ) : S.A) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
      have hp' : ξ ((S.u.ψ v i g : S.Aˣ) : S.A) = ((ρD.ψ v i g : (lauSub (NRep.part C ρ))ˣ) : lauSub (NRep.part C ρ)) := hp.symm
      rw [hp', h2, he]
  · show e ((ξ (S.inc b) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
    rw [hβ b]
    exact e.commutes (β b)
