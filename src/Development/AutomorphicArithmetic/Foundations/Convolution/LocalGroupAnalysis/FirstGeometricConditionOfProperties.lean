module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import GroundTheory.AutomorphicForms.ReductionHeight
public import GroundTheory.AutomorphicForms.ReductionIwasawa
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
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.ReductionBlock
public import Development.AutomorphicArithmetic.AdelicQuotients.FinAtMapGLGalAdMemIwahori
public import Development.AutomorphicArithmetic.AdelicQuotients.HeightOffMapGLGalAd
public import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AutomorphicArithmetic.AdelicQuotients.NormCoeffZeroDvdCharpolyLeAdicCompletion
public import Development.AutomorphicArithmetic.AdelicQuotients.NormCoeffZeroDvdCharpolyLeInfinitePlace
public import Development.AutomorphicArithmetic.AdelicQuotients.NormCoeffZeroFactorCharpolyIwahoriDiagPowLe
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AdelicQuotients.OneLeMulHeightConstHeightOffPowOfSmallAtPlace
public import Development.AutomorphicArithmetic.AdelicQuotients.TwNormConjDiagonalEqConjNormGL

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.CharpolyLocalAdelicConjDiagonalEq

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.charpoly_local_adelic_conj_diagonal_eq :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (γ : GL (Fin n) E) (x : AdelicGLn.AdelicGL E n),
        (∀ w : HeightOneSpectrum (𝓞 E), ((finAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x) : GL (Fin n) (w.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = (γ : Matrix (Fin n) (Fin n) E).charpoly.map (algebraMap E (w.adicCompletion E))) ∧
        ∀ w : InfinitePlace E, ((infAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x) : GL (Fin n) w.Completion) :
          Matrix (Fin n) (Fin n) w.Completion).charpoly = (γ : Matrix (Fin n) (Fin n) E).charpoly.map (algebraMap E w.Completion) := by
  intro E _ _ n γ x
  refine ⟨fun w => ?_, fun w => ?_⟩
  · have h : ((finAt w (AdelicGLn.diagonal E n γ) : GL (Fin n) (w.adicCompletion E)) :
        Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
        (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) := by
      ext a b
      rfl
    rw [finAt_mul, finAt_mul, finAt_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj', h, Matrix.charpoly_map]
  · have h : ((infAt w (AdelicGLn.diagonal E n γ) : GL (Fin n) w.Completion) :
        Matrix (Fin n) (Fin n) w.Completion) =
        (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E w.Completion) := by
      ext a b
      rfl
    rw [infAt_mul, infAt_mul, infAt_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj', h, Matrix.charpoly_map]
end
end

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.EqOneOfSmulPlaceEqOfCompletionMapSurjective

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.eq_one_of_smul_place_eq_of_completionMap_surjective :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E q), Function.Surjective (completionMap q w.1) →
        ∀ σ : E ≃ₐ[F] E, σ • w = w → σ = 1 := by
  intro F E _ _ _ _ _ q w hs σ hσ
  have h : w.1 = σ • w.1 := (congrArg Subtype.val hσ).symm
  haveI : w.1.asIdeal.LiesOver q.asIdeal := w.2
  have hid : ∀ y, galHom σ w.1 w.1 h y = y := by
    intro y
    obtain ⟨a, rfl⟩ := hs y
    exact galHom_completionMap q σ w.1 w.1 h a
  refine AlgEquiv.ext fun x ↦ ?_
  have h2 := galHom_algebraMap σ w.1 w.1 h x
  rw [hid] at h2
  exact (algebraMap E (w.1.adicCompletion E)).injective h2.symm
end
end

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.NormAlgebraMapBaseLeOneOfPlacesOver

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.norm_algebraMap_base_le_one_of_placesOver :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : HeightOneSpectrum (𝓞 F)) (w w' : PlacesOver E q) (a : F),
        ‖algebraMap E (w.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 → ‖algebraMap E (w'.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 := by
  intro F E _ _ _ _ _ q w w' a
  have key : ∀ u : PlacesOver E q,
      ‖algebraMap E (u.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 ↔
        Valued.v (algebraMap F (q.adicCompletion F) a) ≤ 1 := by
    intro u
    rw [Valued.toNormedField.norm_le_one_iff,
      ← IsScalarTower.algebraMap_apply F E (u.1.adicCompletion E),
      ← completionMap_algebraMap q u.1, valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) u.1.asIdeal).ne'
  exact fun h => (key w').2 ((key w).1 h)
end
end

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.OneLeHeightOffAndSubmultiplicative

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.one_le_heightOff_and_submultiplicative :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (q : HeightOneSpectrum (𝓞 F)),
        (∀ g : AdelicGLn.AdelicGL E n, 1 ≤ heightOff q g) ∧ heightOff q (1 : AdelicGLn.AdelicGL E n) = 1 ∧
        ∀ g h : AdelicGLn.AdelicGL E n, heightOff q (g * h) ≤ AutomorphicForm.heightConst E n * heightOff q g * heightOff q h := by
  classical
  intro F E _ _ _ _ _ n q
  let f : AdelicGLn.AdelicGL E n → HeightOneSpectrum (𝓞 E) → ℝ := fun x w =>
    if below F w ≠ q then AutomorphicForm.locHeight (finAt w x) else 1
  have hoff : ∀ x : AdelicGLn.AdelicGL E n, heightOff q x =
      (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w x) ^ w.mult) * ∏ᶠ w, f x w := by
    intro x
    unfold heightOff
    congr 1
    exact finprod_congr fun w => finprod_eq_if
  have hone : ∀ x w, 1 ≤ f x w := by
    intro x w
    simp only [f]
    split_ifs
    · exact AutomorphicForm.one_le_locHeight _
    · exact le_rfl
  have hsupp : ∀ x, (Function.mulSupport (f x)).Finite := by
    intro x
    refine (AutomorphicForm.finite_mulSupport_locHeight_finAt x).subset ?_
    intro w hw
    simp only [Function.mem_mulSupport, f] at hw ⊢
    intro h
    apply hw
    rw [h]
    simp
  have hfi1 : ∀ x, 1 ≤ ∏ᶠ w, f x w := fun x =>
    finprod_induction (fun y : ℝ => 1 ≤ y) le_rfl
      (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) (hone x)
  refine ⟨fun g => ?_, ?_, fun g h => ?_⟩
  · rw [hoff]
    exact one_le_mul_of_one_le_of_one_le (AutomorphicForm.one_le_prod_locHeight g) (hfi1 g)
  · have h1 : ∀ w, f 1 w = 1 := by
      intro w
      simp [f, AutomorphicForm.locHeight_one]
    rw [hoff, finprod_eq_one_of_forall_eq_one h1]
    simp [AutomorphicForm.locHeight_one]
  · set s := ((hsupp g).union (hsupp h)).union (hsupp (g * h))
    have hfin : ∀ x : AdelicGLn.AdelicGL E n, x = g ∨ x = h ∨ x = g * h →
        ∏ᶠ w, f x w = ∏ w ∈ s.toFinset, f x w := by
      intro x hx
      refine finprod_eq_prod_of_mulSupport_subset _ ?_
      intro v hv
      simp only [Set.Finite.coe_toFinset, Set.mem_union]
      rcases hx with rfl | rfl | rfl
      · exact Or.inl (Or.inl hv)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
    have hf : ∏ᶠ w, f (g * h) w ≤ (∏ᶠ w, f g w) * ∏ᶠ w, f h w := by
      rw [hfin _ (Or.inr (Or.inr rfl)), hfin _ (Or.inl rfl), hfin _ (Or.inr (Or.inl rfl)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun v _ => le_trans zero_le_one (hone _ v)) fun v _ => ?_
      simp only [f]
      split_ifs
      · rw [finAt_mul]
        exact AutomorphicForm.locHeight_mul_le_of_ultrametric _ _
      · simp
    have hi : (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (g * h)) ^ w.mult) ≤
        AutomorphicForm.heightConst E n *
          (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult) *
          ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w h) ^ w.mult := by
      rw [AutomorphicForm.heightConst, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀
        (fun w _ => by have := AutomorphicForm.locHeight_pos (infAt w (g * h)); positivity)
        fun w _ => ?_
      rw [← mul_pow, ← mul_pow, infAt_mul]
      exact pow_le_pow_left₀ (AutomorphicForm.locHeight_pos _).le
        (AutomorphicForm.locHeight_mul_le _ _) _
    rw [hoff, hoff, hoff]
    calc (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (g * h)) ^ w.mult) *
          ∏ᶠ w, f (g * h) w
        ≤ (AutomorphicForm.heightConst E n *
            (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult) *
            ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w h) ^ w.mult) *
          ((∏ᶠ w, f g w) * ∏ᶠ w, f h w) :=
          mul_le_mul hi hf (le_trans zero_le_one (hfi1 _))
            (mul_nonneg (mul_nonneg (le_trans zero_le_one AutomorphicForm.one_le_heightConst)
              (le_trans zero_le_one (AutomorphicForm.one_le_prod_locHeight g)))
              (le_trans zero_le_one (AutomorphicForm.one_le_prod_locHeight h)))
      _ = _ := by ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.FirstGeometricConditionOfProperties

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private noncomputable abbrev th (σ : E ≃ₐ[F] E) (n : ℕ) : Monoid.End (AdelicGLn.AdelicGL E n) := mapGL n (galAd σ)

private theorem ht_pow (σ : E ≃ₐ[F] E) (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (y : AdelicGLn.AdelicGL E n) (m : ℕ) :
    heightOff q ((th σ n ^ m) y) = heightOff q y := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ_apply']; exact (UpperTheory.heightOff_mapGL_galAd F E σ n q _).trans ih

private theorem ht_norm (σ : E ≃ₐ[F] E) (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (y : AdelicGLn.AdelicGL E n) {Y : ℝ}
    (hy : heightOff q y ≤ Y) (m : ℕ) :
    heightOff q (twNorm (th σ n) m y) ≤ (AutomorphicForm.heightConst E n * Y) ^ m := by
  obtain ⟨h1, h2, h3⟩ := UpperTheory.one_le_heightOff_and_submultiplicative F E n q
  have hK := AutomorphicForm.one_le_heightConst (K := E) (n := n)
  induction m with
  | zero => rw [twNorm_zero, h2, pow_zero]
  | succ m ih =>
    rw [twNorm_succ]
    refine (h3 _ _).trans ?_
    rw [ht_pow, pow_succ]
    have a1 := h1 y
    have a2 := h1 (twNorm (th σ n) m y)
    calc _ = heightOff q (twNorm (th σ n) m y) * (AutomorphicForm.heightConst E n * heightOff q y) := by ring
      _ ≤ _ := mul_le_mul ih (mul_le_mul_of_nonneg_left hy (by linarith)) (by positivity) (by linarith)

private theorem iw_pow (σ : E ≃ₐ[F] E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (y : AdelicGLn.AdelicGL E n)
    (hy : finAt w y ∈ GLnLocal.iwahori (w.adicCompletion E) n) (m : ℕ) :
    ∀ w' : HeightOneSpectrum (𝓞 E), w' = (σ ^ m) • w →
      finAt w' ((th σ n ^ m) y) ∈ GLnLocal.iwahori (w'.adicCompletion E) n := by
  induction m with
  | zero => intro w' h; rw [pow_zero, one_smul] at h; subst h; exact hy
  | succ m ih =>
    intro w' h
    rw [pow_succ', mul_smul] at h
    subst h
    rw [pow_succ_apply']
    exact UpperTheory.finAt_mapGL_galAd_mem_iwahori F E σ n _ _ (ih _ rfl)

private theorem norm_at [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (n : ℕ)
    (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q) (hs : Function.Surjective (completionMap q w₀.1))
    (y : AdelicGLn.AdelicGL E n)
    (hy : ∀ w : PlacesOver E q, w ≠ w₀ → finAt w.1 y ∈ GLnLocal.iwahori (w.1.adicCompletion E) n) (m : ℕ)
    (hm : m + 1 ≤ Module.finrank F E) :
    ∃ i ∈ GLnLocal.iwahori (w₀.1.adicCompletion E) n, finAt w₀.1 (twNorm (th σ n) (m + 1) y) = finAt w₀.1 y * i := by
  have hord : orderOf σ = Module.finrank F E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  induction m with
  | zero => exact ⟨1, one_mem _, by rw [twNorm_succ, twNorm_zero, one_mul, mul_one]; rfl⟩
  | succ m ih =>
    obtain ⟨i, hi, e⟩ := ih (by omega)
    have hne : (σ ^ (m + 1))⁻¹ • w₀ ≠ w₀ := fun h => by
      have h1 := UpperTheory.eq_one_of_smul_place_eq_of_completionMap_surjective F E q w₀ hs _ h
      rw [inv_eq_one] at h1
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega) h1
    have h2 := iw_pow σ n _ y (hy _ hne) (m + 1) w₀.1 (by rw [coe_smul_placesOver, smul_inv_smul])
    exact ⟨i * _, mul_mem hi h2, by rw [twNorm_succ, finAt_mul, e, mul_assoc]⟩

private theorem small_false (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q) (γ : GL (Fin n) E)
    (x : AdelicGLn.AdelicGL E n) (p : F[X]) (hp : p.Monic)
    (hd : p.map (algebraMap F E) ∣ (γ : Matrix (Fin n) (Fin n) E).charpoly) (j : ℕ)
    (hs : ‖((p.map (algebraMap F E)).map (algebraMap E (w₀.1.adicCompletion E))).coeff 0‖ * 2 ^ j ≤ 1) :
    (2 : ℝ) ^ j ≤ (AutomorphicForm.heightConst E n * heightOff q (x⁻¹ * AdelicGLn.diagonal E n γ * x)) ^ n := by
  obtain ⟨c1, c2⟩ := UpperTheory.charpoly_local_adelic_conj_diagonal_eq E n γ x
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have h21 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  rw [coeff_map, coeff_map] at hs
  have hne : algebraMap F E (p.coeff 0) ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := hd
    have h1 := congrArg (fun s : E[X] => s.coeff 0) hr
    simp only [mul_coeff_zero, coeff_map, h0, zero_mul] at h1
    have h3 := Matrix.det_eq_sign_charpoly_coeff (γ : Matrix (Fin n) (Fin n) E)
    rw [h1, mul_zero] at h3
    exact (Matrix.isUnits_det_units γ).ne_zero h3
  have hs' : ‖algebraMap E (w₀.1.adicCompletion E) (algebraMap F E (p.coeff 0))‖ ≤ (2 ^ j : ℝ)⁻¹ := by
    rw [← one_div, le_div_iff₀ h2]; exact hs
  have key := UpperTheory.one_le_mul_heightConst_heightOff_pow_of_small_at_place F E n q w₀ (x⁻¹ * AdelicGLn.diagonal E n γ * x) _ _ hne
    (fun w => by
      have := UpperTheory.norm_coeff_zero_dvd_charpoly_le_infinitePlace E w n _ _ (AutomorphicForm.one_le_locHeight _)
        (AutomorphicForm.norm_apply_le_locHeight (infAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x)))
        ((p.map (algebraMap F E)).map (algebraMap E w.Completion)) ((hp.map _).map _)
        (by rw [c2]; exact Polynomial.map_dvd _ hd)
      rwa [coeff_map, coeff_map] at this)
    (fun w => by
      have := UpperTheory.norm_coeff_zero_dvd_charpoly_le_adicCompletion E w n _ _ (AutomorphicForm.one_le_locHeight _)
        (AutomorphicForm.norm_apply_le_locHeight (finAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x)))
        ((p.map (algebraMap F E)).map (algebraMap E (w.adicCompletion E))) ((hp.map _).map _)
        (by rw [c1]; exact Polynomial.map_dvd _ hd)
      rwa [coeff_map, coeff_map] at this)
    (fun w => UpperTheory.norm_algebraMap_base_le_one_of_placesOver F E q w₀ w _ (hs'.trans (inv_le_one_of_one_le₀ h21))) hs'
  rwa [← div_eq_inv_mul, one_le_div h2] at key

private theorem core [IsGalois F E] (hA : A1) (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (n : ℕ) (hn : 0 < n)
    (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q) (hs : ∀ w : PlacesOver E q, Function.Surjective (completionMap q w.1))
    (ν : Fin n → ℤ) (hν : Function.Injective ν) (hsum : ∑ i, ν i = 0)
    (hJ : ∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, ν i ≠ 0)
    (j : ℕ) (hj0 : 0 < j) (Y : ℝ) (hY : 1 ≤ Y)
    (hj : (AutomorphicForm.heightConst E n * AutomorphicForm.heightConst E n ^ Module.finrank F E) ^ n *
      Y ^ (Module.finrank F E * n) < 2 ^ j)
    (δ : GL (Fin n) E) (x y : AdelicGLn.AdelicGL E n)
    (hy : y = x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x)
    (hht : heightOff q y ≤ Y)
    (a b : GL (Fin n) (w₀.1.adicCompletion E)) (ha : a ∈ GLnLocal.iwahori (w₀.1.adicCompletion E) n)
    (hb : b ∈ GLnLocal.iwahori (w₀.1.adicCompletion E) n)
    (hab : finAt w₀.1 y = a * Cartan.diagPow (w₀.1.adicCompletion E) n (fun i => (j : ℤ) * ν i) * b)
    (hoth : ∀ w : PlacesOver E q, w ≠ w₀ → finAt w.1 y ∈ GLnLocal.iwahori (w.1.adicCompletion E) n) :
    EllElt σ δ := by
  have hK := AutomorphicForm.one_le_heightConst (K := E) (n := n)
  obtain ⟨P, hP⟩ := charpoly_normGL_lifts σ hσ δ
  have hPm : P.Monic := by
    refine Polynomial.monic_of_injective (algebraMap F E).injective ?_
    rw [hP]; exact Matrix.charpoly_monic _
  have hPd : P.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (algebraMap F E).injective P, hP, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  refine ⟨P, ?_, hP⟩
  have hN : twNorm (th σ n) (Module.finrank F E) y = x⁻¹ * AdelicGLn.diagonal E n (normGL σ δ) * x := by
    rw [hy]; exact UpperTheory.twNorm_conj_diagonal_eq_conj_normGL F E σ n δ x
  have hH := ht_norm σ n q y hht (Module.finrank F E)
  rw [hN] at hH
  have hbad : ∀ p : F[X], p.Monic → p ∣ P →
      ¬ ‖((p.map (algebraMap F E)).map (algebraMap E (w₀.1.adicCompletion E))).coeff 0‖ * 2 ^ j ≤ 1 := by
    intro p hp hd h
    have h1 := small_false n q w₀ (normGL σ δ) x p hp (by rw [← hP]; exact Polynomial.map_dvd _ hd) j h
    have h0 := (UpperTheory.one_le_heightOff_and_submultiplicative F E n q).1 (x⁻¹ * AdelicGLn.diagonal E n (normGL σ δ) * x)
    have h2 := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hH (by linarith : 0 ≤ AutomorphicForm.heightConst E n)) n
    have h3 : (AutomorphicForm.heightConst E n * (AutomorphicForm.heightConst E n * Y) ^ Module.finrank F E) ^ n =
        (AutomorphicForm.heightConst E n * AutomorphicForm.heightConst E n ^ Module.finrank F E) ^ n * Y ^ (Module.finrank F E * n) := by
      rw [pow_mul, ← mul_pow, mul_pow _ Y, mul_assoc]
    linarith
  have hl0 : 0 < Module.finrank F E := Module.finrank_pos
  obtain ⟨i, hi, hNi⟩ := norm_at σ hσ n q w₀ (hs w₀) y hoth (Module.finrank F E - 1) (by omega)
  rw [show Module.finrank F E - 1 + 1 = Module.finrank F E by omega, hN, hab, mul_assoc _ b i] at hNi
  have hc := (UpperTheory.charpoly_local_adelic_conj_diagonal_eq E n (normGL σ δ) x).1 w₀.1
  rw [hNi, ← hP] at hc
  rw [hPm.irreducible_iff_natDegree]
  refine ⟨fun h => by rw [h, natDegree_one] at hPd; omega, fun p₁ p₂ h₁ h₂ h12 => ?_⟩
  by_contra hcon
  have hd12 : p₁.natDegree + p₂.natDegree = n := by rw [← h12, h₁.natDegree_mul h₂] at hPd; exact hPd
  have hinj : ∀ p : F[X], ((p.map (algebraMap F E)).map (algebraMap E (w₀.1.adicCompletion E))).natDegree =
      p.natDegree := fun p => by
    rw [natDegree_map_eq_of_injective (RingHom.injective _), natDegree_map_eq_of_injective (RingHom.injective _)]
  have hp1 : 0 < p₁.natDegree := by
    exact Nat.pos_of_ne_zero fun h => hcon (Or.inl h)
  have hp2 : 0 < p₂.natDegree := by
    exact Nat.pos_of_ne_zero fun h => hcon (Or.inr h)
  rcases UpperTheory.norm_coeff_zero_factor_charpoly_iwahori_diagPow_le hA E w₀.1 n ν hν hsum hJ j hj0 a ha (b * i) (mul_mem hb hi)
    ((p₁.map (algebraMap F E)).map (algebraMap E _)) ((p₂.map (algebraMap F E)).map (algebraMap E _))
    ((h₁.map _).map _) ((h₂.map _).map _) (by rw [hinj]; exact hp1) (by rw [hinj]; exact hp2)
    (by rw [← Polynomial.map_mul, ← Polynomial.map_mul, h12, ← hc, ← mul_assoc]) with h | h
  · exact hbad p₁ h₁ ⟨p₂, h12.symm⟩ h
  · exact hbad p₂ h₂ ⟨p₁, by rw [mul_comm, h12]⟩ h

end

theorem UpperTheory.ConvolutionTheory.G.firstGeometricCondition_of_properties :
    A1 → N5 → EllipticityFromProductFormula := by
  intro hA _ F E _ _ _ _ _ _ σ hσ n hn
  have hK := AutomorphicForm.one_le_heightConst (K := E) (n := n)
  refine ⟨(AutomorphicForm.heightConst E n * AutomorphicForm.heightConst E n ^ Module.finrank F E) ^ n,
    Module.finrank F E * n, ?_⟩
  intro q w₀ hs ν hν hsum hJ j Y hY hj f hf δ x y hy hfy
  obtain ⟨hht, ⟨a, ha, b, hb, hab⟩, hoth⟩ := hf y hfy
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exfalso
      have h1 : 1 ≤ (AutomorphicForm.heightConst E n * AutomorphicForm.heightConst E n ^ Module.finrank F E) ^ n *
          Y ^ (Module.finrank F E * n) :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hK)))
          (one_le_pow₀ hY)
      rw [pow_zero] at hj
      linarith
    · exact h
  exact core hA σ hσ n hn q w₀ hs ν hν hsum hJ j hj0 Y hY hj δ _ _ hy hht a b ha hb hab hoth
end
end
