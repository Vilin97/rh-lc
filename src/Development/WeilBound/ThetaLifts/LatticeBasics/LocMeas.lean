module

public import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {v : Pl F}

theorem herm_full {B : Base F E} {r s : ℕ} (hY : Y.IsHerm σ B r s) : Y.L.IsFullLattice E := by
  have hdet : Y.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have hs := hY.sig w
    obtain ⟨hrs, A, hA⟩ := hs
    let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
    let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
    have h1 : A'ᵀ * (Y.J.map (B.emb w).1) * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
      rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
    have h2 := congrArg Matrix.det h1
    intro h0
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h2
    simpa [Matrix.det_neg] using h2.symm
  have form_eq (y x : Fin n → E) : form σ Y.J y x = ∑ l, (y ᵥ* Y.J) l * σ (x l) := by
    rw [form, Matrix.dotProduct_mulVec]; rfl
  have hspan : Submodule.span E (Y.L : Set (Fin n → E)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let a : Fin n → E := fun i => σ (f (Pi.single i 1))
    let u : Fin n → E := a ᵥ* Y.J⁻¹
    have hu : u ᵥ* Y.J = a := by
      simp [u, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet.isUnit]
    have hform (x : Fin n → E) : form σ Y.J u x = σ (f x) := by
      rw [form_eq, hu, LinearMap.pi_apply_eq_sum_univ f x, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_mul, mul_comm]
      have he : (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := funext fun j => by
        rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
      rw [he]
    have hline (c : E) : c • u ∈ Y.L := by
      apply (hY.dual _).2
      intro x hx
      have hx0 : f x = 0 := hf (Submodule.subset_span hx)
      have he : form σ Y.J (c • u) x = c * form σ Y.J u x := by
        rw [form_eq, form_eq, Matrix.smul_vecMul, Finset.mul_sum]
        simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [he, hform, hx0, map_zero, mul_zero]
      exact isIntegral_zero
    have hu0 : u = 0 := by
      by_contra hn
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
      let coord := (LinearMap.proj i : (Fin n → E) →ₗ[E] E).restrictScalars (𝓞 E)
      have ht : Y.L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / u i) • u, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 E) E := Module.finite_def.mpr (ht ▸ hY.lat.fg.map coord)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    have ha : a = 0 := by simpa [hu0] using hu.symm
    apply hf0
    apply LinearMap.ext
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    apply Finset.sum_eq_zero
    intro i _
    have hi : σ (f (Pi.single i 1)) = 0 := congrFun ha i
    have hi' : f (Pi.single i 1) = 0 := (map_eq_zero σ).mp hi
    have he : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := funext fun j => by
      rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
    simp [he, hi']
  exact { toIsLattice := hY.lat, span_eq_top := hspan }

theorem isOpen_int (hL : Y.L.IsFullLattice E) (v : Pl F) : IsOpen (intGrp σ Y v : Set (UA σ Y.J)) := by
  classical
  obtain ⟨m, x, hs, hx⟩ := lat_gen hL.toIsLattice
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have ce : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  let U : Set (Fin m → AF F) := {a | ∀ i, evFin F v (a i) ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => (Valued.isOpen_valuationSubring _).preimage (ce.comp (continuous_apply i))
  have hV := IsModuleTopology.isOpenMap_of_surjective (gen_surj hL hs) U hU
  set V := (Fintype.linearCombination (AF F) fun i => incV F (x i).1) '' U with eV
  have key : ∀ A : Matrix (Fin n) (Fin n) (AE F E), (∀ i, A *ᵥ incV F (x i).1 ∈ V) → ∀ z ∈ latHat Y, At (evFin F v) z →
      A *ᵥ z ∈ latHat Y := fun A hA z hz h => by
    obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
    rw [← at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
    refine sum_mem fun i _ => ?_
    obtain ⟨b, hb, e⟩ := hA i
    rw [smul_smul, Matrix.mulVec_smul, ← e, Fintype.linearCombination_apply, Finset.smul_sum]
    refine sum_mem fun j _ => ?_
    rw [smul_smul, mul_assoc]
    exact gen_mem (idem_mem (by rw [map_mul]; exact mul_mem ((ha i).2 v) (hb j))) (x j).2
  have x1 : ∀ i, incV F (x i).1 ∈ V := fun i => ⟨Pi.single i 1, fun j => by
    rw [Pi.single_apply, apply_ite (evFin F v), map_one, map_zero]
    split_ifs
    exacts [one_mem _, zero_mem _], by rw [Fintype.linearCombination_apply_single, one_smul]⟩
  have o : IsOpen {g : UA σ Y.J | ∀ i, mat g *ᵥ incV F (x i).1 ∈ V} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => hV.preimage (cont_mat.matrix_mulVec continuous_const)
  have o1 : ∀ i, mat (1 : UA σ Y.J) *ᵥ incV F (x i).1 ∈ V := fun i => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]
    exact x1 i
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (mem_of_superset ((o.inter (o.preimage continuous_inv)).mem_nhds
    ⟨o1, by rw [Set.mem_preimage, inv_one]; exact o1⟩) fun g hg z hz h => ⟨key _ hg.1 z hz h, key _ hg.2 z hz h⟩)

theorem exists_cpt (hL : Y.L.IsFullLattice E) (v : Pl F) : ∃ C : Set (Matrix (Fin n) (Fin n) (AE F E)), IsCompact C ∧
    ∀ g ∈ locGrp σ Y v, IntAt v g → mat g ∈ C := by
  obtain ⟨m, x, hs, -⟩ := lat_gen hL.toIsLattice
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  choose c hc using fun j : Fin n => gen_surj hL hs (Pi.single j 1)
  refine ⟨_, (isCompact_univ_pi fun _ : Fin m => isCompact_latHat hL.toIsLattice).image
    (f := fun y => (1 - idem v) • 1 + Matrix.of fun r j => ∑ i, c j i • y i r)
    (continuous_matrix fun r j => by simp only [Matrix.of_apply, Matrix.add_apply]; fun_prop), fun g hg h => ?_⟩
  refine ⟨fun i => mat g *ᵥ (idem v • incV F (x i).1), fun i _ => (h _ ?_ (at_iff.2 (by rw [smul_smul, idem_sq]))).1, ?_⟩
  · exact gen_mem (mul_one (idem v) ▸ idem_mem (by rw [map_one]; exact one_mem _)) (x i).2
  · refine Eq.trans ?_ (congrArg mat (mem_loc.1 hg))
    show (1 - idem v) • 1 + _ = (1 - idem v) • 1 + idem v • mat g
    refine (add_right_inj _).2 (Matrix.ext fun r j => ?_)
    have e := congrFun (congrArg (fun w => idem v • mat g *ᵥ w) (hc j)) r
    simp only [Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.smul_sum, Finset.sum_apply,
      Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply] at e
    simp only [Matrix.of_apply, Matrix.mulVec_smul, Pi.smul_apply, Matrix.smul_apply, ← e]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem isCompact_int (hL : Y.L.IsFullLattice E) (v : Pl F) : IsCompact {g : locGrp σ Y v | IntAt v g.1} := by
  obtain ⟨C, hC, h⟩ := exists_cpt (σ := σ) hL v
  have := t2Space_cm_host_adeles (F := F) (E := E)
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
  have hc : IsClosed (UG (cA σ) (incM F Y.J) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs)) continuous_const
  have e := (Units.isClosedEmbedding_embedProduct.comp hc.isClosedEmbedding_subtypeVal).comp
    (isClosed_loc (σ := σ) (Y := Y) (v := v)).isClosedEmbedding_subtypeVal
  refine (e.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))).of_isClosed_subset
    ((isClosed_int hL.toIsLattice v).preimage continuous_subtype_val) fun g hg => ⟨h _ g.2 hg, _, h _ (inv_mem g.2) ?_, rfl⟩
  exact (intGrp σ Y v).inv_mem hg

theorem _root_.GlobalTheory.ThK.Dbl.locMeas : LocMeas := by
  intro F E _ _ _ _ _ σ B n Y r s _ hY v
  obtain ⟨b1, b2⟩ := lcsc_loc (σ := σ) (Y := Y) v
  have hfull := herm_full hY
  let K : TopologicalSpace.PositiveCompacts (locGrp σ Y v) := ⟨⟨_, isCompact_int hfull v⟩, 1, mem_interior_iff_mem_nhds.2
    (((isOpen_int hfull v).preimage continuous_subtype_val).mem_nhds (intGrp σ Y v).one_mem)⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

end GlobalTheory.ThK.Dbl.Euler

end
