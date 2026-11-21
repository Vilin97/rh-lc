module

public import Mathlib

@[expose] public section

namespace GlobalTheory.LocFinSemisimple

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem exists_isAtom_le : ∀ (n : ℕ) (Y : Subrepresentation ρ),
    FiniteDimensional ℂ Y.toSubmodule → Module.finrank ℂ Y.toSubmodule = n → Y ≠ ⊥ →
      ∃ T : Subrepresentation ρ, IsAtom T ∧ T ≤ Y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hY hn hne
    by_cases hA : IsAtom Y
    · exact ⟨Y, hA, le_rfl⟩
    · have : ∃ Z, Z < Y ∧ Z ≠ ⊥ := by
        by_contra hc
        push_neg at hc
        exact hA ⟨hne, hc⟩
      obtain ⟨Z, hZY, hZ⟩ := this
      have hlt : Z.toSubmodule < Y.toSubmodule :=
        lt_of_le_of_ne hZY.le fun h => hZY.ne (Subrepresentation.toSubmodule_injective h)
      have hZf : FiniteDimensional ℂ Z.toSubmodule := Submodule.finiteDimensional_of_le hlt.le
      have hr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT, hTZ⟩ := ih _ (hn ▸ hr) Z hZf rfl hZ
      exact ⟨T, hT, hTZ.trans hZY.le⟩

def ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U) : Subrepresentation ρ :=
  ⟨U, fun k _ hu => hU k _ hu⟩

variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

open MeasureTheory MeasureTheory.Measure in
open scoped InnerProductSpace in
private theorem semisimple_of_continuous_coeff [FiniteDimensional ℂ V]
    (hc : ∀ (ℓ : Module.Dual ℂ V) (v : V), Continuous fun k => ℓ (ρ k v)) :
    ρ.IsSemisimpleRepresentation := by
  borelize K
  let μ := haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
  let b := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    b.equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm
  -- Inverting the group argument makes left Haar invariance apply to the averaged inner product.
  have hcont (v : V) : Continuous fun k : K => e (ρ k⁻¹ v) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (hc (b.coord i) v).comp continuous_inv)
  let c : InnerProductSpace.Core ℂ V :=
    { inner := fun u v => ∫ k, ⟪e (ρ k⁻¹ u), e (ρ k⁻¹ v)⟫_ℂ ∂μ
      conj_inner_symm := fun u v => by simp only [← integral_conj, inner_conj_symm]
      re_inner_nonneg := fun v => by
        simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, integral_ofReal,
          RCLike.ofReal_re]
        exact integral_nonneg fun k => by positivity
      add_left := fun u u' v => by
        have hi (z : V) : Integrable (fun k => ⟪e (ρ k⁻¹ z), e (ρ k⁻¹ v)⟫_ℂ) μ :=
          ((hcont z).inner (hcont v)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        simp only [map_add, inner_add_left]
        exact integral_add (hi u) (hi u')
      smul_left := fun u v r => by
        simp only [map_smul, inner_smul_left, integral_const_mul]
      definite := fun v hv => by
        by_contra h
        simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, integral_ofReal,
          RCLike.ofReal_eq_zero] at hv
        refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := μ) (x := 1)
          (f := fun k => ‖e (ρ k⁻¹ v)‖ ^ 2) ((hcont v).norm.pow 2)
          (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_).ne' hv
        simpa [map_eq_zero_iff e e.injective] using h }
  have hinv (g : K) (u v : V) : c.inner (ρ g u) (ρ g v) = c.inner u v := by
    have h := integral_mul_left_eq_self (μ := μ)
      (fun k => ⟪e (ρ k⁻¹ u), e (ρ k⁻¹ v)⟫_ℂ) g⁻¹
    change (∫ k, ⟪e (ρ k⁻¹ (ρ g u)), e (ρ k⁻¹ (ρ g v))⟫_ℂ ∂μ) =
      ∫ k, ⟪e (ρ k⁻¹ u), e (ρ k⁻¹ v)⟫_ℂ ∂μ
    simpa only [mul_inv_rev, inv_inv, map_mul, mul_apply_eq_comp] using h
  let _ : NormedAddCommGroup V := c.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation ρ := ⟨S.toSubmoduleᗮ, by
    intro g v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    have h := hv _ (S.apply_mem_toSubmodule g⁻¹ hu)
    change c.inner (ρ g⁻¹ u) v = 0 at h
    change c.inner u (ρ g v) = 0
    rw [← hinv g] at h
    simpa using h⟩
  refine ⟨T, ?_⟩
  have h := S.toSubmodule.isCompl_orthogonal
  constructor
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.sup_eq_top

theorem isSemisimple_ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U)
    (hfd : FiniteDimensional ℂ U)
    (hc : ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) :
    (ofInvariant U hU).toRepresentation.IsSemisimpleRepresentation := by
  haveI : FiniteDimensional ℂ (ofInvariant U hU).toSubmodule := hfd
  refine semisimple_of_continuous_coeff fun l v => ?_
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := U) l
  have h : ∀ k, l ((ofInvariant U hU).toRepresentation k v) = g (ρ k v) := fun k => by
    rw [← hg]; rfl
  simp only [h]
  exact hc g v v.2

theorem le_iSup_atoms
    (H : ∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧
      ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u))
    (X : Subrepresentation ρ) :
    X.toSubmodule ≤ ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  set N := ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule with hNdef
  have hNX : N ≤ X.toSubmodule := iSup₂_le fun S hS => hS.2
  have hNinv : ∀ k, ∀ x ∈ N, ρ k x ∈ N := by
    intro k
    have : N ≤ N.comap (ρ k) := iSup₂_le fun S hS x hx =>
      (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun x hx => this hx
  intro x hxX
  obtain ⟨U, hxU, hfd, hU, hc⟩ := H x
  let R := ofInvariant U hU
  haveI : ComplementedLattice (Subrepresentation R.toRepresentation) :=
    isSemisimple_ofInvariant U hU hfd hc
  let W : Subrepresentation R.toRepresentation :=
    ⟨N.comap U.subtype, fun k w hw => hNinv k _ hw⟩
  obtain ⟨W', hW'⟩ := exists_isCompl W
  have hdis : W.toSubmodule ⊓ W'.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
  have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
  let Xc : Submodule ℂ U := X.toSubmodule.comap U.subtype
  let Y : Subrepresentation ρ := ⟨(W'.toSubmodule ⊓ Xc).map U.subtype, by
    rintro k _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨R.toRepresentation k u, ⟨W'.apply_mem_toSubmodule k hu1,
      X.apply_mem_toSubmodule k hu2⟩, rfl⟩⟩
  have hY : Y = ⊥ := by
    by_contra hne
    haveI : FiniteDimensional ℂ Y.toSubmodule := Submodule.finiteDimensional_of_le
      (S₂ := U) (fun y hy => by obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hy; exact u.2)
    obtain ⟨T, hT, hTY⟩ := exists_isAtom_le _ Y this rfl hne
    have hTX : T ≤ X := by
      intro t ht
      obtain ⟨u, ⟨_, hu2⟩, rfl⟩ := hTY ht
      exact hu2
    have hTN : T.toSubmodule ≤ N :=
      le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) T ⟨hT, hTX⟩
    have hT0 : T.toSubmodule ≠ ⊥ := fun h => hT.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    obtain ⟨u, ⟨hu1, _⟩, rfl⟩ := hTY ht
    have hu : u ∈ W.toSubmodule ⊓ W'.toSubmodule := ⟨hTN ht, hu1⟩
    rw [hdis] at hu
    have hu0 : ((u : R.toSubmodule) : V) = 0 :=
      congrArg Subtype.val ((Submodule.mem_bot ℂ (M := R.toSubmodule) (x := u)).1 hu)
    exact ht0 hu0
  have hx' : (⟨x, hxU⟩ : R.toSubmodule) ∈ W.toSubmodule ⊔ W'.toSubmodule := by rw [hsup]; trivial
  obtain ⟨w, hw, w', hw', hww⟩ := Submodule.mem_sup.1 hx'
  have hsum : (w : V) + (w' : V) = x := congrArg Subtype.val hww
  have hw'X : w' ∈ Xc := by
    have h1 : (w : V) ∈ X.toSubmodule := hNX hw
    have h2 : (w' : V) = x - w := by
      rw [← hsum]; abel
    show (w' : V) ∈ X.toSubmodule
    rw [h2]
    exact X.toSubmodule.sub_mem hxX h1
  have hw'0 : (w' : V) ∈ Y.toSubmodule := ⟨w', ⟨hw', hw'X⟩, rfl⟩
  rw [hY] at hw'0
  have : (w' : V) = 0 := (Submodule.mem_bot ℂ).1 hw'0
  have hxw : x = w := by
    rw [← hsum, ‹(w' : V) = 0›, add_zero]
  rw [hxw]
  exact hw

theorem semisimple_of_locallyFinite : ∀ (K V : Type) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧
      (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) →
    ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S →
      FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ,
        X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  intro K V _ _ _ _ _ _ ρ H
  have hle := le_iSup_atoms H
  refine ⟨?_, ?_, fun X => le_antisymm (hle X) (iSup₂_le fun S hS => hS.2)⟩
  · rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
      ← sSup_simples_eq_top_iff_isSemisimpleModule]
    let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
    set s := sSup {m : Submodule (MonoidAlgebra ℂ K) ρ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ K) m} with hs
    have hZ : (e.symm s).toSubmodule = ⊤ := by
      refine eq_top_iff.2 ((hle ⊤).trans (iSup₂_le fun S hS => ?_))
      have : S ≤ e.symm s := e.le_symm_apply.2
        (le_sSup (isSimpleModule_iff_isAtom.2 ((e.isAtom_iff S).2 hS.1)))
      exact this
    have h1 : e.symm s = ⊤ := Subrepresentation.toSubmodule_injective hZ
    rw [← e.apply_symm_apply s, h1, e.map_top]
  · intro S hS
    have hS0 : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    obtain ⟨U, hvU, hfd, hU, -⟩ := H v
    rcases hS.le_iff.1 (inf_le_left : S ⊓ ofInvariant U hU ≤ S) with h | h
    · have hm : v ∈ (S ⊓ ofInvariant U hU).toSubmodule := ⟨hv, hvU⟩
      rw [h] at hm
      exact absurd ((Submodule.mem_bot ℂ).1 hm) hv0
    · have hSU : S.toSubmodule ≤ U := by
        rw [← h]; exact fun x hx => hx.2
      exact Submodule.finiteDimensional_of_le hSU

end GlobalTheory.LocFinSemisimple
