module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsSide
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

open GlobalTheory.PRep GlobalTheory.CuspRep.LocEx

theorem UpperTheory.ConvolutionTheory.R2.H.unrSplit :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ThetaLiftTrivialOrbitTermsVanish W M π → ∀ Q : CuspSub E 2, Q.V ≤ span W M π →
      ∀ (v : P F) (w : P E), SplitAt v w → ∀ B, π.HasSat v B → (CG.mk Q).HasSat w B := by
  intro F E _ _ _ _ _ _ _ D W M π hN Q hQ v w hs B hB
  obtain ⟨hq, i, hc, hx, hv⟩ := hs
  have smooth_loc := π.isSmooth_locRep v
  have cpt_fin (k : TR.Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
      π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
    refine Subtype.ext ?_
    change (TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k)) * TR.rt F 2 (finGL F 2 g)) y.1 =
      (TR.rt F 2 (finGL F 2 g) * TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, TR.infGL_comm]

  have fin_loc {k : GL (Fin 2) (Af F)}
      (hk : GeneralLinearGroup.map (pLoc F v) k = 1) (g : GL (Fin 2) (v.adicCompletion F)) (y : π.V) :
      π.finPart k (π.locRep v g y) = π.locRep v g (π.finPart k y) := by
    simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL v hk]

  -- Local invariant subspaces stable under the commutant are stable under every global action.
  have bot_or_top (W : Submodule ℂ π.V)
      (h1 : ∀ g, ∀ x ∈ W, π.locRep v g x ∈ W)
      (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep v g x) = π.locRep v g (T x)) → ∀ x ∈ W, T x ∈ W) :
      W = ⊥ ∨ W = ⊤ := by
    have hi := Submodule.map_injective_of_injective π.V.injective_subtype
    have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
      cases o with
      | fin k =>
        have h3 := h1 (GeneralLinearGroup.map (pLoc F v) k) _ (h2
          (π.finPart ((locGL F 2 v (GeneralLinearGroup.map (pLoc F v) k))⁻¹ * k))
          (fin_loc (map_pLoc_inv_mul v k)) x hx)
        rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left] at h3
      | cpt k => exact h2 _ (fun g y => cpt_fin k _ y) x hx
      | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F 2 v g)) y.1)) x hx
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨_, hop o x hx, rfl⟩) with h | h
    · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
    · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))
  -- Use a finite-dimensional compact type to obtain an irreducible local component.
  have exists_comp : ∃ σ, π.IsLocComp v σ := by
    let orb {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x

    have orb_comm {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
        (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

    have orb_act {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
        orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
      | single a b => simp [orb]

    let annPart {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V := {
      carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
      add_mem' := fun {x y} hx hy c hc => by
        have : orb κ (x + y) c = orb κ x c + orb κ y c := by
          simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
        rw [this, hx c hc, hy c hc, add_zero]
      zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
      smul_mem' := fun a x hx c hc => by
        have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
        simpa [hx c hc] using this }

    have exists_type {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] (κ : Representation ℂ K V) (φ : V)
        (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
        ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
          (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
      have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
        rintro k _ ⟨c, rfl⟩
        exact ⟨_, orb_act κ φ k c⟩
      have : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
        change FiniteDimensional ℂ ↥(LinearMap.range (Finsupp.linearCombination ℂ (fun k => κ k φ)))
        rw [Finsupp.range_linearCombination]
        exact hφ
      let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
      obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
      refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (GlobalTheory.PRep.sub κ _ hO), fun x hx => ?_⟩
      have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
        rw [← sub_eq_zero, ← map_sub]
        refine hx _ ?_
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
      refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
        ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
      · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
        obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
        have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
            b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
          have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
            Subtype.ext (orb_act κ φ k c)
          rw [h2]
          exact LinearMap.toMatrix_mulVec_repr b b _ _
        rw [h1]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
      · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
        simp [orb]
    let cptPart : Representation ℂ (TR.Kinf F 2) π.V :=
      GlobalTheory.PRep.sub (TR.cptRep F 2) π.V fun k => π.stable (.cpt k)
    obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
    set φ : π.V := ⟨φ₀, hφ⟩
    have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
    set L := GlobalTheory.CuspRep.LocEx.stab π.finPart φ
    have hL : IsOpen (L : Set (GL (Fin 2) (Af F))) := π.isSmooth_finPart _
    obtain ⟨K, ho, hcompact, hK⟩ := LocEx.exists_compact_open v _ hL
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart k φ)) := by
      have := (π.cusp φ₀ hφ).1.kfin
      refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
        (Submodule.span ℂ (Set.range fun k => TR.cptRep F 2 k φ₀)) fun v => ?_)
        fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
      refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    obtain ⟨d, ξ, hξ⟩ := exists_type cptPart φ hfd
    have hcomm : ∀ g k x, π.finPart g (cptPart k x) = cptPart k (π.finPart g x) := fun g k x => (cpt_fin k g x).symm
    let U : Submodule ℂ π.V := annPart cptPart φ ⊓
      fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin 2) (pLoc F v)).ker)
    obtain ⟨σ, hσ, -⟩ := exists_irred smooth_loc ho (fun W hW e => by
        rcases bot_or_top (nullPart (π.locRep v) K) (fun g x hx => nullPart_act _ K g hx)
          (fun T hT x hx => nullPart_comm _ K T hT hx) with h2 | h2
        · exact le_bot_iff.1 (h2 ▸ le_nullPart smooth_loc hcompact W hW e)
        · exact absurd (eq_zero_of_mem_nullPart smooth_loc hcompact (mem_fix.2 hK) (h2 ▸ Submodule.mem_top)) h0')
      U (fun g x hx => ⟨fun c hc => by
          rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
        mem_fix.2 fun k hk => by rw [fin_loc hk.2, mem_fix.1 hx.2 k hk]⟩)
      ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, h0'⟩) (fun K' hK' => by
        obtain ⟨W, hW, hWf⟩ := admissibleReal F 2 π (L ⊓ (K' ⊓ L.comap (locGL F 2 v)).comap (GeneralLinearGroup.map (pLoc F v)))
          (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL v))).preimage
            (continuous_map_pLoc v))) d ξ
        refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
        obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
        refine hWf f hf (fun k hk z => ?_) hx1
        have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul v k⟩
        have h2 := mem_fix.1 hx.2 _ hk.2.1
        have h3 : π.finPart k x = x := by
          rw [← mul_inv_cancel_left (locGL F 2 v (GeneralLinearGroup.map (pLoc F v) k)) k, map_mul,
            mul_apply_eq_comp, h1]
          exact h2
        obtain ⟨c, hc⟩ := hf2 z
        rw [hc, ← orb_comm _ _ (hcomm k), h3])
    exact ⟨σ, hσ⟩
  obtain ⟨σ, hσ⟩ := exists_comp
  have hiso : LocIsotypic π.finPart v σ := by
    refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
    refine (bot_or_top _ (fun g x hx => ?_) (fun T hT x hx => ?_)).resolve_left fun e => ?_
    · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep v g) _) fun f => ?_) hx)
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
    · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
        rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
    · obtain ⟨f, h0, hf⟩ := hσ
      exact h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩))
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL E 2 Q w
  obtain ⟨e, he⟩ := UpperTheory.ConvolutionTheory.R2.split F E D W M π hN Q hQ v w i hc hx σ σ' hσ hσ'
  have h1 : GlobalTheory.LFun.HasSatGL v σ.ρ B := by
    let ρ := π.locRep v
    let I := {f : σ.V →ₗ[ℂ] π.V // ∀ g x, f (σ.ρ g x) = ρ g (f x)}
    have htop : ⨆ f : I, LinearMap.range f.1 = ⊤ := hiso.2
    obtain ⟨f, hf₀, hf⟩ := hσ
    have hker : LinearMap.ker f = ⊥ :=
      ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g x hx => by
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hf, hx, map_zero]) |>.resolve_right fun e => hf₀ (LinearMap.ker_eq_top.1 e)
    have hup : ∀ B', GlobalTheory.LFun.HasSatGL v σ.ρ B' → GlobalTheory.LFun.HasSatGL v ρ B' := by
      intro B' hB'
      constructor
      · obtain ⟨x, hx⟩ := hB'.exists_vec
        have hfx := hx.map f hf ((map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hker)).2 hx.1)
        exact (Submodule.ne_bot_iff _).2 ⟨_, hfx.2.1, hfx.1⟩
      · intro x hx hx₀
        exact GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := ρ) σ.irred hB'
          (fun f : I => f.1) (fun f => f.2) (htop ▸ Submodule.mem_top) hx hx₀
    obtain ⟨x, hx, hx₀⟩ := (Submodule.ne_bot_iff _).1 hB.1
    obtain ⟨y, hy₀, hy⟩ := LocSph.exists_fixed_of_mem_iSup ρ σ.ρ σ.irred
      (fun f : I => f.1) (fun f => f.2) _ x hx₀
      (fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk) (htop ▸ Submodule.mem_top)
    obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
      ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy₀⟩)
    exact (hup B' hB').unique hB ▸ hB'
  have hq' : Formalism.UG.qV E w = Formalism.UG.qV F v := by
    simpa [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV] using hq
  have h2 : GlobalTheory.LFun.HasSatGL w σ'.ρ B :=
    GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hv hq' e (fun g x => (he g x).symm) h1
  rw [CG.hasSat_mk]
  exact GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ' h2
