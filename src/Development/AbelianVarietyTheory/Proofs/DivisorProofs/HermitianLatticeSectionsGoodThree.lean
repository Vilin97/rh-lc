module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteTypeStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsOpenComplexPointsAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
public import Development.AutomorphicArithmetic.DivisorFrames.CuspFormWeightReduction
public import Development.AutomorphicArithmetic.DivisorFrames.HolomorphicReductionSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfArcVanishingSmoothChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReading
public import Development.AutomorphicArithmetic.DivisorFrames.EvenWeightDictionaryFrame

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)


set_option synthInstance.maxHeartbeats 200000 in
attribute [-instance] GlobalTheory.CompHS.cuspAddCommGroup in
private theorem chart_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
    {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r} {Z : Comp Xo c} {G : WTZ E} (hev : Even G.2)
    (σ : c.F →+* ℂ) (hU : IsUnf (U (goodOf c σ)))
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    {τ : ℕ} {t : ℝ} {f : cuspOn U Z (τ • G)} (hfm : f ∈ smallL U x V dict Z G τ t) :
    ∃ (R : Subalgebra c.F (Om Z)) (_ : Algebra.FiniteType c.F R) (d : Om Z) (_ : d ≠ 0)
      (hc : ∀ v, d * genPoint Z (cuspOn U Z G) v ∈ R) (hF : d ^ τ * genVal Z (f : Rul Xo c) ∈ R),
      ∀ (N n : ℕ) (b : Module.Basis (Fin N) c.F (cuspOn U Z G)) (g : Matrix (Fin N) (Fin n) c.F)
        (A : (c.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
        GlobalTheory.CompHt.IsFrame (normOn U x V dict Z G) (latOn U Z G) b g A → ∀ φ : R →+* ℂ,
        φ.comp (algebraMap c.F R) = σ →
        ‖φ ⟨_, hF⟩‖ ^ 2 ≤ Real.exp (2 * τ * t) * (∑ a, ‖∑ m, A σ m a * φ ⟨_, hc (b m)⟩‖ ^ 2) ^ τ := by
  have cs_frame {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (s v : Fin N → ℂ) :
      ‖∑ m, s m * v m‖ ^ 2 ≤ (∑ a, ‖∑ m, A m a * v m‖ ^ 2) * GlobalTheory.ChowHt.frameNorm A s ^ 2 := by
    set y := A⁻¹.mulVec s with hy
    have hs : A.mulVec y = s := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.one_mulVec]
    have e : ∑ m, s m * v m = ∑ a, (∑ m, A m a * v m) * y a := by
      rw [← hs]
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by ring
    rw [e, GlobalTheory.ChowHt.frameNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← hy]
    refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2
    exact Finset.sum_congr rfl fun a _ => norm_mul _ _


  have hlemma :
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ (σ : c.F →+* ℂ), (∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom) → (∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G), ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))), ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2) → ∀ (N n : ℕ) (b : Module.Basis (Fin N) c.F (cuspOn U Z G)) (g : Matrix (Fin N) (Fin n) c.F) (A : (c.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.CompHt.IsFrame (normOn U x V dict Z G) (latOn U Z G) b g A → ∀ (κ : ℂ →+* ℂ), (∀ a, ‖κ a‖ = ‖a‖) → κ.comp (goodOf c σ) = σ → ∀ (τ : ℕ) (t : ℝ), ∀ f ∈ smallL U x V dict Z G τ t, ∀ z ∈ framesOn (U (goodOf c σ)) Z, ‖rdU (U (goodOf c σ)) (f : Rul Xo c) z.1 z.2‖ ^ 2 ≤ Real.exp (2 * τ * t) * (∑ a, ‖∑ m, A σ m a * κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2)‖ ^ 2) ^ τ := by
    intro E _ _ _ H Dw l Xo c r U x D V dict Z G hG σ hd hspan N n b g A hF κ hκ hκσ τ t f hf z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hz : z ∈ framesOn (U (goodOf c σ)) Z := ⟨hz1, hz2⟩
    have hN : ∀ (G' : WTZ E) (f' : Rul Xo c), homN (U (goodOf c σ)) x G' f' z =
        GlobalTheory.DegTop.normFac (U (goodOf c σ)) x G' z * ‖rdU (U (goodOf c σ)) f' z.1 z.2‖ := fun G' f' =>
      GlobalTheory.DegTop.homN_eq x _ G' f' z
    have hpos := GlobalTheory.DegTop.normFac_pos x (U (goodOf c σ)) G hz1
    set F := GlobalTheory.DegTop.normFac (U (goodOf c σ)) x G z with hFdef
    set S := ∑ a, ‖∑ m, A σ m a * κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2)‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hB0 : 0 ≤ F ^ 2 * S := by positivity
    have h1 := hf.2 _ (goodEmb_goodOf c σ) ⟨z.1, z.2, hz1⟩ hz
    have h2 := GlobalTheory.CompHS.bergOn_le_bergCusp (x := x) hd hspan ⟨z.1, z.2, hz1⟩ hz
    have h3 : GlobalTheory.CompHS.bergCusp U x V dict Z G σ z ≤ ENNReal.ofReal (F ^ 2 * S) := by
      rw [GlobalTheory.CompHS.bergCusp_le_iff hB0]
      intro f' hf'
      have e1 := hF.norm σ ⟨f', hf'⟩
      have e2 : f' = ∑ m, b.repr ⟨f', hf'⟩ m • (b m : Rul Xo c) := by
        have := congrArg Subtype.val (b.sum_repr ⟨f', hf'⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      have e3 : κ (rdU (U (goodOf c σ)) f' z.1 z.2) =
          ∑ m, σ (b.repr ⟨f', hf'⟩ m) * κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2) := by
        conv_lhs => rw [e2]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_apply, Finset.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
        congr 1
        exact congrArg (fun φ : c.F →+* ℂ => φ (b.repr ⟨f', hf'⟩ m)) hκσ
      have e4 := cs_frame (A σ) (hF.herm σ) (fun m => σ (b.repr ⟨f', hf'⟩ m))
        (fun m => κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2))
      rw [← e3, hκ, e1] at e4
      rw [hN, mul_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left e4 (sq_nonneg _)
    have h4 := h1.trans (mul_le_mul_right (pow_le_pow_left' (h2.trans h3) τ) _)
    have h5 : homN (U (goodOf c σ)) x (τ • G) f z = F ^ τ * ‖rdU (U (goodOf c σ)) (f : Rul Xo c) z.1 z.2‖ := by
      rw [hN, GlobalTheory.DegTop.normFac_nsmul x _ hG hz1]
    have h6 : ENNReal.ofReal (homN (U (goodOf c σ)) x (τ • G) f z ^ 2) ≤
        ENNReal.ofReal (Real.exp (2 * τ * t) * (F ^ 2 * S) ^ τ) := by
      rw [ENNReal.ofReal_pow (homN_nonneg _ _ _ _ _), ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow hB0]
      exact h4
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity), h5] at h6
    refine le_of_mul_le_mul_left (a := (F ^ τ) ^ 2) ?_ (by positivity)
    calc _ = (F ^ τ * ‖rdU (U (goodOf c σ)) (f : Rul Xo c) z.1 z.2‖) ^ 2 := by ring
      _ ≤ _ := h6
      _ = _ := by ring
  obtain ⟨κ, hκn, hκκ, hκσ⟩ : ∃ κ : ℂ →+* ℂ, (∀ a, ‖κ a‖ = ‖a‖) ∧ (∀ a, κ (κ a) = a) ∧
      κ.comp (goodOf c σ) = σ := by
    by_cases h : GoodEmb c σ
    · exact ⟨RingHom.id ℂ, fun _ => rfl, fun _ => rfl, by rw [goodOf, if_pos h]; rfl⟩
    · exact ⟨starRingEnd ℂ, Complex.norm_conj, Complex.conj_conj, by
        rw [goodOf, if_neg h]; exact RingHom.ext fun a => Complex.conj_conj _⟩
  obtain ⟨R, hR, tt, hmem, hread⟩ := GlobalTheory.DegCmp.exists_chart_read_at_frames _ _ _ _ _ _ _ (goodOf c σ)
    (U (goodOf c σ)) hU Z
  have hex : exZ Dw (τ • G) = fun ix => exZ Dw G ix * τ := by
    funext ix
    cases ix <;> simp [exZ, mul_comm]
  have hfs : (f : Rul Xo c) ∈ secZ Xo c (fun ix => exZ Dw G ix * (τ : ℤ)) := by
    rw [← hex]; exact cuspW_le_secZ _ f.2.1
  have hpow : ∀ {M : Type} [Field M] (a : Formalism.L2.Pj.Ix Dw → Mˣ),
      ((∏ ix, a ix ^ (exZ Dw G ix * (τ : ℤ)) : Mˣ) : M) = ((∏ ix, a ix ^ exZ Dw G ix : Mˣ) : M) ^ τ := fun a => by
    rw [← Units.val_pow_eq_pow_val, ← Finset.prod_pow]
    simp only [zpow_mul, zpow_natCast]
  have hF := hmem _ _ hfs
  rw [hpow] at hF
  have hs : ∀ v : cuspOn U Z G, (v : Rul Xo c) ∈ secZ Xo c (exZ Dw G) := fun v => cuspW_le_secZ _ v.2.1
  have hc : ∀ v, ((∏ ix, tt ix ^ exZ Dw G ix : (Om Z)ˣ) : Om Z) * genPoint Z (cuspOn U Z G) v ∈ R :=
    fun v => hmem _ _ (hs v)
  refine ⟨R, hR, _, Units.ne_zero _, hc, hF, fun N n b g A hfr φ hφ => ?_⟩
  obtain ⟨z, hz, a, ha⟩ := hread (κ.comp φ) (by
    rw [RingHom.comp_assoc, hφ]
    refine RingHom.ext fun x => ?_
    conv_lhs => rw [← hκσ]
    exact hκκ _)
  have hb := hlemma _ _ _ _ _ _ _ U x D V dict Z G hev σ hd hspan N n b g A hfr κ hκn hκσ τ t f hfm z hz
  have e1 := ha _ _ hfs ⟨_, hF⟩ (by rw [hpow])
  rw [hpow] at e1
  have e2 := fun m => congrArg κ (ha _ _ (hs (b m)) ⟨_, hc (b m)⟩ rfl)
  simp only [RingHom.comp_apply, hκκ, map_mul] at e1 e2
  generalize ((∏ ix, a ix ^ exZ Dw G ix : ℂˣ) : ℂ) = S at e1 e2
  have e3 : ∑ a, ‖∑ m, A σ m a * φ ⟨_, hc (b m)⟩‖ ^ 2 =
      (∑ a, ‖∑ m, A σ m a * κ (rdU (U (goodOf c σ)) (b m : Rul Xo c) z.1 z.2)‖ ^ 2) * ‖S‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hκn S, ← mul_pow, ← norm_mul, Finset.sum_mul]
    exact congrArg (fun q : ℂ => ‖q‖ ^ 2) (Finset.sum_congr rfl fun m _ => by rw [e2]; ring)
  rw [e3, ← hκn, e1, norm_mul, mul_pow, mul_pow, norm_pow, ← pow_mul, ← pow_mul, mul_comm τ 2, ← mul_assoc, mul_comm]
  exact mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg _) _)

