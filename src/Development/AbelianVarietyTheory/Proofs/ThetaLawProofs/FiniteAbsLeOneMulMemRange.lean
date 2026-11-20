import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OfRealVecHalfVec
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem eq_of_finite_modular_family {F : Set (ℍ → ℂ)} (hF : F.Finite)
    (hol : ∀ f ∈ F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (bdd : ∀ f ∈ F, UpperHalfPlane.IsBoundedAtImInfty f)
    (hS : ∀ f ∈ F, (fun z => f (ModularGroup.S • z)) ∈ F)
    (hT : ∀ f ∈ F, (fun z => f (ModularGroup.T • z)) ∈ F)
    {f : ℍ → ℂ} (hf : f ∈ F) (z w : ℍ) : f z = f w := by
  have key : ∀ X : ℂ, ∃ c, (∏ f ∈ hF.toFinset, (fun z => X - f z) : ℍ → ℂ) =
      Function.const _ c := by
    intro X
    set P : ℍ → ℂ := ∏ f ∈ hF.toFinset, (fun z => X - f z) with hP
    have hγ : ∀ γ : SL(2, ℤ), (∀ f ∈ F, (fun z => f (γ • z)) ∈ F) → P ∣[(0 : ℤ)] γ = P := by
      intro γ hγ
      have hinj : Function.Injective fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z) := by
        intro f f' h
        funext z
        simpa using congrFun h (γ⁻¹ • z)
      have hb : Set.BijOn (fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z)) F F :=
        (hF.injOn_iff_bijOn_of_mapsTo hγ).1 hinj.injOn
      ext z
      rw [ModularForm.SL_slash_apply]
      simp only [neg_zero, zpow_zero, mul_one, hP, Finset.prod_apply]
      exact Finset.prod_nbij (fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z))
        (fun f hf => by simpa using hγ f (by simpa using hf)) hinj.injOn
        (by simpa using hb.surjOn) (fun f _ => rfl)
    have hs := SlashInvariantForm.slash_action_generators_SL2Z (hγ _ hS) (hγ _ hT)
    have hb : UpperHalfPlane.IsBoundedAtImInfty P := by
      refine Filter.BoundedAtFilter.prod _ fun f hf => ?_
      exact Asymptotics.IsBigO.sub (Filter.const_boundedAtFilter _ X) (bdd f (by simpa using hf))
    let M : ModularForm 𝒮ℒ 0 :=
      { toFun := P
        slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
        holo' := by
          refine Finset.prod_induction _ (fun f : ℍ → ℂ => MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
            (fun a b ha hb => ha.mul hb) mdifferentiable_const fun f hf => ?_
          exact mdifferentiable_const.sub (hol f (by simpa using hf))
        bdd_at_cusps' := fun {c} hc ↦ by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
          rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
          intro γ _
          rw [hs γ]
          exact hb }
    exact ModularFormClass.levelOne_weight_zero_const M
  have hfin : ((fun f : ℍ → ℂ => f UpperHalfPlane.I) '' F).Finite := hF.image _
  refine isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete
    (hol f hf).continuous.continuousOn (fun t _ => ?_) (Set.mem_univ z) (Set.mem_univ w)
  obtain ⟨c, hc⟩ := key (f t)
  have h1 := congrFun hc t
  have h2 := congrFun hc UpperHalfPlane.I
  simp only [Finset.prod_apply, Function.const_apply] at h1 h2
  rw [Finset.prod_eq_zero (f := fun c : ℍ → ℂ => f t - c t) (hF.mem_toFinset.2 hf) (sub_self _)]
    at h1
  obtain ⟨f', hf', h⟩ := Finset.prod_eq_zero_iff.1 (h2.trans h1.symm)
  exact ⟨f', hF.mem_toFinset.1 hf', (sub_eq_zero.1 h).symm⟩

variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}

theorem spInvariant_transl (hH : IsSpInvariant g H) {B : Matrix (Fin g) (Fin g) ℤ} (hB : B.IsSymm)
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    H (τ + B.map (Int.cast : ℤ → ℂ)) = H τ := by
  rw [← spAct_spTransl]
  exact hH _ (spTransl_mem_sp hB) τ hτ

theorem spAct_spDiag_eq (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    spAct (spDiag U) τ = (U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ) * τ *
      ((U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ))ᵀ := by
  rw [spAct_eq, jAut_spDiag_inv, nAut_eq, cMat_spDiag]
  simp

theorem spInvariant_conj (hH : IsSpInvariant g H) (U : (Matrix (Fin g) (Fin g) ℤ)ˣ)
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    H ((U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ) * τ *
      ((U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ))ᵀ) = H τ := by
  rw [← spAct_spDiag_eq]
  exact hH _ (spDiag_mem_sp U) τ hτ

theorem spInvariant_partialInv (hH : IsSpInvariant g H) (e : Fin g)
    {τ σ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    (h : ∀ i k, σ i k - σ i e * (τ e k + if e = k then 1 else 0) =
      τ i k + if i = e then (if e = k then 1 else 0) - τ e k else 0) : H σ = H τ := by sorry























def rankOneCurve (Z : Matrix (Fin g) (Fin g) ℂ) (R : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℝ)
    (s : ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  of fun i j => Z i j + R i j + s * u i * u j

theorem rankOneCurve_map_im (Z : Matrix (Fin g) (Fin g) ℂ) (R : Matrix (Fin g) (Fin g) ℝ)
    (u : Fin g → ℝ) (s : ℂ) :
    (rankOneCurve Z R u s).map Complex.im = Z.map Complex.im + s.im • vecMulVec u u := by
  ext i j
  simp [rankOneCurve, vecMulVec_apply, mul_assoc]

section Curve

variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)

include hZs hZ in
theorem rankOneCurve_mem {R : Matrix (Fin g) (Fin g) ℝ} (hR : R.IsSymm) {u : Fin g → ℝ}
    (hu : u e = 1) {s : ℂ} (hs : 0 < s.im) : rankOneCurve Z R u s ∈ SiegelH (Fin g) := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [rankOneCurve, transpose_apply, of_apply, hZs.apply i j, hR.apply i j]
    ring
  · rw [rankOneCurve_map_im]
    exact hZ u hu _ hs

theorem finite_abs_le_one_mul_mem_range {c : ℝ} (hc : c ≠ 0) :
    {x : ℝ | |x| ≤ 1 ∧ c * x ∈ (Int.castRingHom ℝ).range}.Finite := by
  refine ((Set.finite_Icc (-⌈|c|⌉) ⌈|c|⌉).image fun k : ℤ => (k : ℝ) / c).subset ?_
  rintro x ⟨hx, k, hk⟩
  have hk' : (k : ℝ) = c * x := hk
  refine ⟨k, ?_, by simp only [hk']; field_simp⟩
  have h1 : |(k : ℝ)| ≤ (⌈|c|⌉ : ℤ) := by
    rw [hk', abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg c) hx).trans (Int.le_ceil _)
  exact abs_le.1 (by exact_mod_cast h1)

include hZs hZe hZ in

theorem eq_on_rankOneCurve_of_integral (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {N : ℕ} (hN : N ≠ 0) {R : Matrix (Fin g) (Fin g) ℝ} {u : Fin g → ℝ} (hu : u e = 1)
    (hR : R.IsSymm) (hRe : R e e = 0) (huN : ∀ i, N * u i ∈ (Int.castRingHom ℝ).range)
    (hRN : ∀ i, N * R i e ∈ (Int.castRingHom ℝ).range)
    (hRN2 : ∀ i j, N * N * R i j ∈ (Int.castRingHom ℝ).range) (z w : ℍ) :
    H (rankOneCurve Z R u z) = H (rankOneCurve Z R u w) := by sorry










































































































































theorem tendsto_floor_nat_mul_div (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (⌊(n + 1 : ℝ) * x⌋ : ℝ) / (n + 1)) Filter.atTop (𝓝 x) := by
  have h := (tendsto_const_nhds (x := x)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds (fun n => ?_) fun n => ?_
  · have hn : (0 : ℝ) < n + 1 := by positivity
    simp only
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn]
    linarith [Int.lt_floor_add_one ((n + 1 : ℝ) * x)]
  · have hn : (0 : ℝ) < n + 1 := by positivity
    simp only
    rw [div_le_iff₀ hn]
    linarith [Int.floor_le ((n + 1 : ℝ) * x)]

include hZs hZe hZ in

theorem eq_on_rankOneCurve (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {u v : Fin g → ℝ} (hu : u e = 1) (hv : v e = 0) (z w : ℍ) :
    H (rankOneCurve Z (vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)) u z) =
      H (rankOneCurve Z (vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)) u w) := by
  let R : (Fin g → ℝ) → Matrix (Fin g) (Fin g) ℝ := fun v =>
    vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)
  have hR : ∀ v, (R v).IsSymm := fun v => by
    ext i j
    simp only [R, transpose_apply, Matrix.add_apply, vecMulVec_apply]
    ring
  let a : (Fin g → ℝ) → ℕ → Fin g → ℝ := fun x n i => (⌊(n + 1 : ℝ) * x i⌋ : ℝ) / (n + 1)
  have hau : ∀ n, a u n e = 1 := fun n => by
    have : ⌊(n + 1 : ℝ)⌋ = n + 1 := by exact_mod_cast Int.floor_intCast (R := ℝ) (n + 1)
    simp only [a, hu, mul_one, this]
    push_cast
    exact div_self (by positivity)
  have hav : ∀ n, a v n e = 0 := fun n => by simp [a, hv]
  have ha : ∀ x (n : ℕ) i, ((n + 1 : ℕ) : ℝ) * a x n i ∈ (Int.castRingHom ℝ).range := by
    intro x n i
    refine ⟨⌊(n + 1 : ℝ) * x i⌋, ?_⟩
    simp only [a, eq_intCast]
    push_cast
    field_simp
  have hε : ∀ i, (Pi.single e 1 : Fin g → ℝ) i ∈ (Int.castRingHom ℝ).range := fun i => by
    by_cases h : i = e <;> simp [h]
  have hlim : ∀ z : ℍ, Filter.Tendsto (fun n => H (rankOneCurve Z (R (a v n)) (a u n) z))
      Filter.atTop (𝓝 (H (rankOneCurve Z (R v) u z))) := by
    intro z
    have hm := rankOneCurve_mem hZs hZ (hR v) hu z.im_pos
    have hc : Continuous fun p : (Fin g → ℝ) × (Fin g → ℝ) =>
        (of.symm (rankOneCurve Z (R p.1) p.2 z) : Fin g → Fin g → ℂ) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [rankOneCurve, of_symm_apply, of_apply, R, Matrix.add_apply, vecMulVec_apply]
      fun_prop
    have h1 : Filter.Tendsto (fun n => (a v n, a u n)) Filter.atTop (𝓝 (v, u)) :=
      (tendsto_pi_nhds.2 fun i => tendsto_floor_nat_mul_div _).prodMk_nhds
        (tendsto_pi_nhds.2 fun i => tendsto_floor_nat_mul_div _)
    have h2 := (hol.continuousOn.continuousAt
      ((isOpen_phDom g).mem_nhds (of_symm_mem_phDom hm))).tendsto.comp
      ((hc.tendsto (v, u)).comp h1)
    simp only [Equiv.apply_symm_apply, phSym_eq_self_of_isSymm hm.1] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, Equiv.apply_symm_apply,
      phSym_eq_self_of_isSymm (rankOneCurve_mem hZs hZ (hR _) (hau n) z.im_pos).1]
  refine tendsto_nhds_unique (hlim z) ((hlim w).congr fun n => ?_)
  refine eq_on_rankOneCurve_of_integral hZs hZe hZ hol hH hb (Nat.succ_ne_zero n) (hau n) (hR _)
    (by simp [R, vecMulVec_apply, hav]) (ha u n) (fun i => ?_) (fun i j => ?_) w z
  · simpa [R, vecMulVec_apply, hav] using ha v n i
  · convert mul_mem (natCast_mem _ (n + 1))
      (add_mem (mul_mem (hε i) (ha v n j)) (mul_mem (ha v n i) (hε j))) using 1
    simp only [R, Matrix.add_apply, vecMulVec_apply]
    ring

end Curve

theorem posDef_sub_vecMulVec_add {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) (e : Fin g)
    {u : Fin g → ℝ} (hu : u e = 1) {y : ℝ} (hy : 0 < y) :
    (Y - (Y e e)⁻¹ • vecMulVec (fun i => Y i e) (fun i => Y i e) + y • vecMulVec u u).PosDef := by
  have hs : ∀ i j, Y j i = Y i j := fun i j => by simpa using hY.1.apply i j
  have he : 0 < Y e e := hY.diag_pos
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [vecMulVec_apply, hs i j, mul_comm]
  · set a : ℝ := x ⬝ᵥ fun i => Y i e with ha
    have h1 : Y *ᵥ Pi.single e 1 = fun i => Y i e := by
      ext i
      simp
    have h2 : Pi.single e 1 ⬝ᵥ Y *ᵥ x = a := by
      rw [single_dotProduct]
      simp [ha, mulVec, dotProduct, hs e, mul_comm]
    set x' := x - (a / Y e e) • (Pi.single e 1 : Fin g → ℝ) with hx'
    have h3 : star x ⬝ᵥ (Y - (Y e e)⁻¹ • vecMulVec (fun i => Y i e) (fun i => Y i e) +
        y • vecMulVec u u) *ᵥ x = x' ⬝ᵥ Y *ᵥ x' + y * (x ⬝ᵥ u) ^ 2 := by
      simp only [star_trivial, add_mulVec, sub_mulVec, smul_mulVec, vecMulVec_mulVec, hx',
        mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, h1, h2, single_dotProduct, op_smul_eq_smul, smul_eq_mul,
        dotProduct_comm _ x, ← ha]
      field_simp
      ring
    rw [h3]
    by_cases h0 : x' = 0
    · have h4 : x = (a / Y e e) • (Pi.single e 1 : Fin g → ℝ) := sub_eq_zero.1 h0
      have h5 : a / Y e e ≠ 0 := fun h => hx (by rw [h4, h, zero_smul])
      have h6 : x ⬝ᵥ u = a / Y e e := by
        rw [h4]
        simp [hu]
      rw [h0, h6, zero_dotProduct, zero_add]
      positivity
    · have := hY.dotProduct_mulVec_pos h0
      rw [star_trivial] at this
      positivity

theorem eventually_eq_column (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    (e : Fin g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    ∀ᶠ s in 𝓝 (0 : ℂ), H (τ + s • vecMulVec (fun i => ((τ i e).im : ℂ))
      (fun i => ((τ i e).im : ℂ))) = H τ := by
  have he : 0 < (τ e e).im := hτ.2.diag_pos (i := e)
  let u : Fin g → ℝ := fun i => (τ i e).im / (τ e e).im
  let v : Fin g → ℝ := fun i => (τ i e).re - (τ e e).re * u i
  have hu : u e = 1 := div_self he.ne'
  have hv : v e = 0 := by simp [v, hu]
  let R : Matrix (Fin g) (Fin g) ℝ := vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)
  let Z : Matrix (Fin g) (Fin g) ℂ := of fun i j => τ i j - R i j - τ e e * u i * u j
  have hZs : Z.IsSymm := by
    ext i j
    simp only [Z, R, transpose_apply, of_apply, Matrix.add_apply, vecMulVec_apply, hτ.1.apply i j]
    push_cast
    ring
  have hZe : ∀ i, Z i e = 0 := fun i => by
    apply Complex.ext
    · simp [Z, R, vecMulVec_apply, hu, v]
    · simp [Z, hu]
      simp only [u]
      field_simp
      ring
  have hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
      (Z.map Complex.im + y • vecMulVec u u).PosDef := fun u' hu' y hy => by
    convert posDef_sub_vecMulVec_add hτ.2 e hu' hy using 2
    ext i j
    simp [Z, vecMulVec_apply]
    simp only [u]
    field_simp
  have hc : Continuous fun s : ℂ => (τ e e + s * (τ e e).im ^ 2).im := by fun_prop
  filter_upwards [continuousAt_const.eventually_lt hc.continuousAt
    (show (0 : ℝ) < _ by simpa using he)] with s hs
  convert eq_on_rankOneCurve hZs hZe hZ hol hH hb hu hv ⟨_, hs⟩ ⟨_, he⟩ using 2
  · ext i j
    have : ((τ e e).im : ℂ) ≠ 0 := by exact_mod_cast he.ne'
    simp [rankOneCurve, Z, R, vecMulVec_apply]
    simp only [u]
    push_cast
    field_simp
    ring
  · ext i j
    simp [rankOneCurve, Z, R]
    ring

theorem fderiv_vecMulVec_eq_zero (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (e : Fin g) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) :
    fderiv ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (of x))) (of.symm τ)
      (of.symm (vecMulVec (imC τ *ᵥ fun l => (U.val e l : ℂ))
        (imC τ *ᵥ fun l => (U.val e l : ℂ)))) = 0 := by sorry


























theorem siegel_eq_of_bounded (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {τ σ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) (hσ : σ ∈ SiegelH (Fin g)) :
    H τ = H σ := by sorry

















































































theorem phHolo_of_phKoecher : PhKoecherStatement → PhHoloStatement := by
  intro hK g hg H hol hH
  have hb := hK g hg 1 le_rfl H hol
    (fun B hB τ hτ => by simpa using spInvariant_transl hH hB hτ)
    (fun U hU _ τ hτ => by
      obtain ⟨U, rfl⟩ := (isUnit_iff_isUnit_det U).2 (hU ▸ isUnit_one)
      exact spInvariant_conj hH U hτ)
  by_cases h : (SiegelH (Fin g)).Nonempty
  · obtain ⟨σ, hσ⟩ := h
    exact ⟨H σ, fun τ hτ => siegel_eq_of_bounded hol hH hb hτ hσ⟩
  · exact ⟨0, fun τ hτ => absurd ⟨τ, hτ⟩ h⟩

end GlobalTheory
