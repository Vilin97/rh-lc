module

public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsKeyPow
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaLawZeroOfEven
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LatticeBlocks
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawSymplecticNormalForm
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminantStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_ellipticKeyData_value_eq_discriminant : ThetaUnifAV → ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic], ∃ x : KeyIn R, x.P.g = 1 ∧ ∀ (s : R →+* ℂ) (x' : KeyIn ℂ) (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), KeyPB x' x s → charHalf x'.P.g a b → c ≠ 0 → NormalAt x' τ M a b c → M.det ^ 4 / c ^ 8 = s W.Δ := by
  first | exact @GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant | exact GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant | (intros; apply GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyRuleCharHalfOfCharZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

theorem IsKeyPow.dim_eq {R : Type} [CommRing R] {y x : KeyIn R} {j : ℕ} (h : IsKeyPow y x j) :
    y.P.g = j * x.P.g := by
  obtain ⟨_, hg, -⟩ := h
  exact hg.symm

theorem exists_int_half {g : ℕ} {a : Fin g → ℂ} (h : ∀ i, a i = 0 ∨ a i = 1 / 2) :
    ∃ n : Fin g → ℤ, a = fun i => (((n i : ℝ) / 2 : ℝ) : ℂ) := by
  have : ∀ i, ∃ m : ℤ, a i = (((m : ℝ) / 2 : ℝ) : ℂ) := fun i => by
    rcases h i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using this
  exact ⟨n, funext hn⟩

theorem even_dot_double {g g' : ℕ} (e : Fin 2 × Fin g ≃ Fin g') (n n' : Fin g → ℤ) :
    Even ((fun p => n (e.symm p).2) ⬝ᵥ (fun p => n' (e.symm p).2)) := by
  refine ⟨n ⬝ᵥ n', ?_⟩
  unfold dotProduct
  rw [← e.sum_comp]
  simp [Fintype.sum_prod_type, two_mul]

end GlobalTheory.KeyPow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonzeroLocusConstMul

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowChange

open GlobalTheory.PowLie

variable {R : Type} [CommRing R]

theorem sc_zero_comp {G : Over (Sp R)} [GrpObj G] {v : epsR R ⟶ G} (hv : IsTangent v) :
    sc 0 ≫ v = 1 := by
  have h : sc (0 : R) = toUnit _ ≫ zeroPt R := by
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, Category.assoc, (isTangent_iff v).1 hv, Hom.one_def]

theorem exists_block_basis {G' G : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {j g n : ℕ} (p : Out.IsPowGrp G' G j) (hg : j * g = n) {v v' : Fin g → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (hv' : IsLieBasis v') (M : Matrix (Fin g) (Fin g) R)
    (hM : ∀ i, IsLieComb (M i) v (v' i)) (u : Fin n → (epsR R ⟶ G'))
    (hu : ∀ (i i' : Fin j) (k : Fin g),
      u ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v k else 1) :
    ∃ (w : Fin n → (epsR R ⟶ G')) (M' : Matrix (Fin n) (Fin n) R), IsLieBasis w ∧
      (∀ (i i' : Fin j) (k : Fin g),
        w ((finProdFinEquiv (i, k)).cast hg) ≫ p.pr i' = if i = i' then v' k else 1) ∧
      (∀ i, IsLieComb (M' i) u (w i)) ∧ M'.det = M.det ^ j := by
  subst hg
  obtain ⟨w, hw, hw'⟩ := isLieBasis_pow R G' G j g p v' hv'
  let e : Fin g × Fin j ≃ Fin (j * g) := (Equiv.prodComm _ _).trans finProdFinEquiv
  refine ⟨w, Matrix.reindex e e (Matrix.blockDiagonal fun _ => M), hw, hw', fun m => ?_, ?_⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [isLieComb_iff_prod]
    refine p.lim.hom_ext fun ⟨i'⟩ => ?_
    have := p.hom i'
    change _ ≫ p.pr i' = _ ≫ p.pr i'
    refine Eq.trans ?_ (map_prod (IsMonHom.monoidHom (p.pr i') (epsR R)) _ _).symm
    have hu' : ∀ (i : Fin j) (k : Fin g), u (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 :=
      fun i k => hu i i' k
    rw [hw', ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type, Finset.prod_eq_single i']
    · have h₁ : ∀ k', (IsMonHom.monoidHom (p.pr i') (epsR R))
          (sc (Matrix.reindex e e (Matrix.blockDiagonal fun _ => M) (finProdFinEquiv (i, k))
            (finProdFinEquiv (i', k'))) ≫ u (finProdFinEquiv (i', k'))) =
          sc (if i = i' then M k k' else 0) ≫ v k' := fun k' => by
        change (sc _ ≫ u _) ≫ p.pr i' = _
        rw [Category.assoc, hu', if_pos rfl]
        congr 2
        simp [e, Matrix.blockDiagonal_apply]
      rw [Finset.prod_congr rfl fun k' _ => h₁ k']
      split_ifs with h
      · exact (isLieComb_iff_prod _ _ _).1 (hM k)
      · exact (Finset.prod_eq_one fun k' _ => sc_zero_comp (hv.1 k')).symm
    · intro i'' _ hi
      refine Finset.prod_eq_one fun k' _ => ?_
      change (sc _ ≫ u _) ≫ p.pr i' = _
      rw [Category.assoc, hu', if_neg hi, comp_one]
    · simp
  · rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    simp

theorem appLE_constFn {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

theorem res_constFn {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem constFn_pow {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) (a : R) (n : ℕ) :
    constFn q U (a ^ n) = constFn q U a ^ n := by
  simp only [constFn, map_pow]

def constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_constFn, res_constFn, s.compat, mul_left_comm]

theorem nonzeroLocus_constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R} (ha : IsUnit a) (s : L.Sec) :
    Out.nonzeroLocus (constMul q a s) = Out.nonzeroLocus s := by
  refine iSup_congr fun i => ?_
  have h : IsUnit (constFn q (L.U i) a) := (ha.map _).map _
  change X.basicOpen (constFn q _ a * s.f i) = _
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ h]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem isKeyPow_change : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (j : ℕ) (y : KeyIn K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → GlobalTheory.KeyPow.IsKeyPow y ⟨P, hg, rig, hr, th, hth, v, hv⟩ j → ∃ (t : y.P.L.Sec) (ht : _) (w : _) (hw : _) (M' : Matrix (Fin y.P.g) (Fin y.P.g) K), GlobalTheory.KeyPow.IsKeyPow ⟨y.P, y.g_pos, y.rig, y.rig_gen, t, ht, w, hw⟩ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ j ∧ (∀ i, t.f i = constFn y.P.A.hom _ (a ^ j) * y.th.f i) ∧ (∀ i, IsLieComb (M' i) y.v (w i)) ∧ M'.det = M.det ^ j := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M j y ha hM ⟨p, hj, h₁, h₂, h₃⟩
  have h0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨x, -, hx⟩ := hth' (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  haveI := y.P.isAb.comm
  haveI := P.isAb.comm
  obtain ⟨w, M', hw, hw', hM', hdet⟩ := exists_block_basis p.toIsPowGrp hj hv hv' M hM y.v h₃
  refine ⟨constMul y.P.A.hom (a ^ j) y.th, fun s => ?_, w, hw, M', ⟨p, hj, h₁, fun jj b h => ?_, hw'⟩,
    fun _ => rfl, hM', hdet⟩
  · rw [nonzeroLocus_constMul _ (pow_ne_zero j h0).isUnit]
    exact y.th_ne s
  · have h₄ := h₂ jj b h
    have h₅ : ∀ i, ((p.pr i).left.appLE _ _ (h i)).hom (th'.f (jj i)) =
        constFn y.P.A.hom _ a * ((p.pr i).left.appLE _ _ (h i)).hom (th.f (jj i)) := fun i => by
      rw [ha, map_mul, appLE_constFn _ _ _ (Over.w (p.pr i))]
    refine (Finset.prod_congr rfl fun i _ => h₅ i).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg (_ * ·) h₄).trans ?_
    have h₆ : resG _ (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)
        ((constMul y.P.A.hom (a ^ j) y.th).f b) =
        constFn y.P.A.hom _ a ^ j * resG _ inf_le_right (y.th.f b) := by
      rw [← constFn_pow, ← res_constFn y.P.A.hom (inf_le_right : (Out.boxLB P.L p.pr).U jj ⊓ y.P.L.U b ≤ _)]
      exact map_mul _ _ _
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₆.symm)

end GlobalTheory.PowChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedKeyInvariantRuleCharZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyNormRule

def HasValue (g n : ℕ) (ka : KeyIn ℂ → ℂˣ) (a₀ : ℂ) : Prop :=
  ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g →
    charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ →
    (ka x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ n

theorem dim_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : x'.P.g = x.P.g := by
  obtain ⟨_, _, _, hg, -⟩ := h
  exact hg

theorem HasValue.holo {g n : ℕ} {ka : KeyIn ℂ → ℂˣ} {a₀ : ℂ} (h : HasValue g n ka a₀) (a b : Fin g → ℂ)
    (hab : charHalf g a b) : ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) :=
  ⟨fun _ => a₀, differentiableOn_const _, fun x hx τ hn => by
    simpa using h x τ 1 _ _ 1 hx ⟨fun i => hab.1 _, fun i => hab.2 _⟩ one_ne_zero (by simp) hn⟩

theorem exists_rule_sq (hinv : Key.Chi.InversionStatement) {g c M : ℕ}
    {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK (2 * g) c M ka) {a₀ : ℂ}
    (ha : ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ), x.P.g = 2 * g → c₀ ≠ 0 → Mx.det ≠ 0 →
      NormalAt x τ Mx 0 0 c₀ → (ka ℂ x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ c) :
    ∃ kb, KaRuleK g (2 * c) M kb ∧ HasValue g (2 * c) (kb ℂ) a₀ := by
  obtain ⟨hH, hF, hU, -⟩ := hka
  have hex : ∀ (R : Type) [CommRing R] (x : KeyIn R), ∃ y, IsKeyPow y x 2 :=
    fun R _ x => exists_isKeyPow R x 2 (by norm_num)
  choose sq hsq using hex
  have hdim : ∀ {R : Type} [CommRing R] {x y : KeyIn R}, x.P.g = g → IsKeyPow y x 2 → y.P.g = 2 * g :=
    fun hx hy => hx ▸ hy.dim_eq
  have indep : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K), x.P.g = g → IsKeyPow y x 2 →
      (ka K (sq K x) : K) = ka K y := fun K _ _ x y hx hy =>
    hF K K (RingHom.id K) y (sq K x) (hdim hx hy)
      (keyPB_of_isKeyPow K K (RingHom.id K) x y x (sq K x) 2 (GlobalTheory.keyPB_id K x) hy (hsq K x))
  have hval : HasValue g (2 * c) (fun x => ka ℂ (sq ℂ x)) a₀ := by
    intro x τ Mx a b c₀ hx hab hc hM hn₀
    obtain ⟨n, rfl⟩ := exists_int_half hab.1
    obtain ⟨n', rfl⟩ := exists_int_half hab.2
    have hy := hsq ℂ x
    obtain ⟨e, τ', M', hd, hn⟩ :=
      normalAt_pow x _ 2 τ Mx (fun i => (n i : ℝ) / 2) (fun i => (n' i : ℝ) / 2) c₀ hy hn₀
    obtain ⟨sp, hsp, hlaw⟩ := exists_thetaLaw_zero_of_even hinv _ _ _ (even_dot_double e n n')
    obtain ⟨M'', c', hc', hq, hn'⟩ := GlobalTheory.SpMove.normalAt_spAct (sq ℂ x) τ' M' (c₀ ^ 2) sp _ _ 0 0 hsp hlaw
      (pow_ne_zero _ hc) (by simpa using hn)
    have hq' : M''.det ^ 4 / c' ^ 8 = (Mx.det ^ 4 / c₀ ^ 8) ^ 2 := by rw [hq, hd]; ring
    have hM'' : M''.det ≠ 0 := fun h => by
      rw [h] at hq'
      exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 4 hM) (pow_ne_zero 8 hc)) (by rw [← hq']; simp)
    have := ha (sq ℂ x) _ M'' c' (hdim hx hy) hc' hM'' (by simpa [Pi.zero_def] using hn')
    rw [hq', ← pow_mul] at this
    exact this
  refine ⟨fun K _ _ x => ka K (sq K x), ⟨?_, ?_, ?_, hval.holo⟩, hval⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx hP h₁ h₂
    have hy := hsq K ⟨P, hg, rig, hr, th, hth, v, hv⟩
    obtain ⟨t, ht, w, hw, M', hp, ht', hw', hd⟩ :=
      GlobalTheory.PowChange.isKeyPow_change K P hg rig hr th hth v hv th' hth' v' hv' a Mx 2 _ h₁ h₂ hy
    have key := hH K _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).g_pos _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).rig_gen _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).th_ne _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).basis t ht w hw (a ^ 2) M' (hdim hP hy) ht' hw'
    dsimp only
    rw [indep K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ _ hP hp]
    rw [hd, ← pow_mul, ← pow_mul] at key
    rw [show 8 * (2 * c) = 2 * (8 * c) by ring, show 4 * (2 * c) = 2 * (4 * c) by ring]
    exact key
  · intro K K' _ _ _ _ f x x' hx h
    exact hF K K' f _ _ (hdim hx (hsq K x)) (keyPB_of_isKeyPow K K' f x _ x' _ 2 h (hsq K x) (hsq K' x'))
  · intro R K _ _ _ _ _ _ _ x xK hx hM h
    obtain ⟨u, hu, hu'⟩ := hU R K (sq R x) (sq K xK) (hdim hx (hsq R x)) hM
      (keyPB_of_isKeyPow R K _ x _ xK _ 2 h (hsq R x) (hsq K xK))
    exact ⟨u, hu, fun k _ _ r xk hr hk =>
      hu' k r (sq k xk) hr (keyPB_of_isKeyPow R k r x _ xk _ 2 hk (hsq R x) (hsq k xk))⟩

theorem exists_test (hT : ThetaUnifAV) {g n : ℕ} (hg : 1 ≤ g) {ka : KeyIn ℂ → ℂˣ} {a₀ : ℂ} (h : HasValue g n ka a₀)
    {S : Type} [CommRing S] (W : WeierstrassCurve S) [W.IsElliptic] (s : S →+* ℂ) :
    ∃ (y : KeyIn S) (z : KeyIn ℂ), y.P.g = g ∧ KeyPB z y s ∧ (ka z : ℂ) = a₀ * s W.Δ ^ (g * n) := by
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.T.exists_ellipticKeyData_value_eq_discriminant hT S W
  obtain ⟨y, hy⟩ := exists_isKeyPow S x g hg
  obtain ⟨x', hx'⟩ := exists_keyPB_ring x s
  obtain ⟨z, hz⟩ := exists_isKeyPow ℂ x' g hg
  obtain ⟨⟨τ, Mx, a, b, c, hab, hc, hM, hn₀⟩, -⟩ := GlobalTheory.KeyNormalExists.exists_normalAt hT x'
  have hΔ := hxv s x' τ Mx a b c hx' hab hc hn₀
  obtain ⟨m, rfl⟩ := exists_int_half hab.1
  obtain ⟨m', rfl⟩ := exists_int_half hab.2
  obtain ⟨e, τ', M', hd, hn⟩ :=
    normalAt_pow x' z g τ Mx (fun i => (m i : ℝ) / 2) (fun i => (m' i : ℝ) / 2) c hz hn₀
  refine ⟨y, z, by rw [hy.dim_eq, hx, Nat.mul_one], keyPB_of_isKeyPow S ℂ s x y x' z g hx' hy hz, ?_⟩
  rw [h z τ' M' _ _ _ (by rw [hz.dim_eq, dim_of_keyPB hx', hx, Nat.mul_one]) ⟨fun i => hab.1 _, fun i => hab.2 _⟩
    (pow_ne_zero _ hc) (by rw [hd]; exact pow_ne_zero _ hM) hn, ← hΔ, hd, pow_mul]
  congr 2
  ring

theorem const_rat_unit (hT : ThetaUnifAV) {g n M : ℕ} (hg : 1 ≤ g)
    {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK g n M ka) {a₀ : ℂ}
    (h : HasValue g n (ka ℂ) a₀) (W : WeierstrassCurve ℤ) (hW : W.Δ ≠ 0) :
    ∃ r : ℚ, r ≠ 0 ∧ (r : ℂ) = a₀ ∧ ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
      [CharZero K] [Algebra R K] [IsFractionRing R K], IsUnit (M : R) → IsUnit (W.Δ : R) →
      ∃ w : Rˣ, algebraMap R K w = (r : K) := by
  obtain ⟨-, hF, hU, -⟩ := hka
  let S := Localization.Away W.Δ
  have hext : ∀ {T : Type} [CommRing T] (f f' : S →+* T), f = f' := fun f f' =>
    IsLocalization.ringHom_ext (Submonoid.powers W.Δ) (RingHom.ext_int _ _)
  have hlift : ∀ {T : Type} [CommRing T], IsUnit (W.Δ : T) → Nonempty (S →+* T) := fun {T} _ hu =>
    ⟨IsLocalization.Away.lift (g := Int.castRingHom T) W.Δ hu⟩
  haveI : (W.map (algebraMap ℤ S)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact IsLocalization.Away.algebraMap_isUnit W.Δ⟩
  have hQ : (W.Δ : ℚ) ≠ 0 := Int.cast_ne_zero.2 hW
  obtain ⟨i⟩ := hlift (T := ℚ) hQ.isUnit
  obtain ⟨y, z, hy, hz, hv⟩ := exists_test hT hg h (W.map (algebraMap ℤ S)) ((Rat.castHom ℂ).comp i)
  obtain ⟨yQ, hyQ⟩ := exists_keyPB_ring y i
  have hyQg : yQ.P.g = g := (dim_of_keyPB hyQ).trans hy
  rw [hF ℚ ℂ (Rat.castHom ℂ) yQ z hyQg (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yQ z _ _ hyQ hz),
    WeierstrassCurve.map_Δ, eq_intCast (algebraMap ℤ S), map_intCast, eq_ratCast] at hv
  have hC : (W.Δ : ℂ) ≠ 0 := Int.cast_ne_zero.2 hW
  refine ⟨(ka ℚ yQ : ℚ) / (W.Δ : ℚ) ^ (g * n), div_ne_zero (Units.ne_zero _) (pow_ne_zero _ hQ), ?_, ?_⟩
  · push_cast
    rw [hv, mul_div_cancel_right₀ _ (pow_ne_zero _ hC)]
  · intro R K _ _ _ _ _ _ _ hM hΔ
    obtain ⟨j⟩ := hlift hΔ
    obtain ⟨yR, hyR⟩ := exists_keyPB_ring y j
    obtain ⟨yK, hyK⟩ := exists_keyPB_ring yQ (Rat.castHom K)
    have hyK' := GlobalTheory.keyPB_trans _ _ _ y yQ yK _ _ hyQ hyK
    rw [hext ((Rat.castHom K).comp i) ((algebraMap R K).comp j)] at hyK'
    obtain ⟨u, hu, -⟩ := hU R K yR yK ((dim_of_keyPB hyR).trans hy) hM
      (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yR yK _ _ hyR hyK')
    rw [hF ℚ K _ yQ yK hyQg hyK, eq_ratCast] at hu
    have hK : (W.Δ : K) ≠ 0 := Int.cast_ne_zero.2 hW
    refine ⟨u * hΔ.unit⁻¹ ^ (g * n), ?_⟩
    have e : algebraMap R K (hΔ.unit⁻¹ : Rˣ) = (W.Δ : K)⁻¹ := by
      rw [map_units_inv, IsUnit.unit_spec, map_intCast]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, e, ← hu, Rat.cast_div, Rat.cast_pow,
      Rat.cast_intCast, inv_pow, div_eq_mul_inv]

theorem rule_div {g n M : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK g n M ka)
    {r : ℚ} (hr : r ≠ 0) (h : HasValue g n (ka ℂ) r)
    (hu : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
      [CharZero K] [Algebra R K] [IsFractionRing R K], IsUnit (M : R) → ∃ w : Rˣ, algebraMap R K w = (r : K)) :
    ∃ κ, KaRuleK g n M κ ∧ HasValue g n (κ ℂ) 1 := by
  obtain ⟨hH, hF, hU, -⟩ := hka
  let κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ :=
    fun K _ _ x => ka K x * (Units.mk0 (r : K) (Rat.cast_ne_zero.2 hr))⁻¹
  have hκ : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), (κ K x : K) = ka K x * (r : K)⁻¹ :=
    fun K _ _ x => by simp [κ]
  have hval : HasValue g n (κ ℂ) 1 := fun x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅ => by
    have : (r : ℂ) ≠ 0 := Rat.cast_ne_zero.2 hr
    rw [hκ, h x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅]
    field_simp
  refine ⟨κ, ⟨?_, ?_, ?_, hval.holo⟩, hval⟩
  · intro K _ _ P hg rig hrig th hth v hv th' hth' v' hv' a Mx hP h₁ h₂
    rw [hκ, hκ, ← _root_.mul_assoc, ← _root_.mul_assoc,
      hH K P hg rig hrig th hth v hv th' hth' v' hv' a Mx hP h₁ h₂]
  · intro K K' _ _ _ _ f x x' hx hp
    rw [hκ, hκ, hF K K' f x x' hx hp, map_mul, map_inv₀, map_ratCast]
  · intro R K _ _ _ _ _ _ _ x xK hx hM hp
    obtain ⟨u, hu₁, hu₂⟩ := hU R K x xK hx hM hp
    obtain ⟨w, hw⟩ := hu R K hM
    have hw' : (w : R) * (r.den : R) = (r.num : R) := IsFractionRing.injective R K (by
      rw [map_mul, hw, map_natCast, map_intCast]
      exact_mod_cast Rat.mul_den_eq_num r)
    refine ⟨u * w⁻¹, ?_, fun k _ _ ρ xk hρ hk => ?_⟩
    · rw [hκ, hu₁, Units.val_mul, map_mul, map_units_inv, hw]
    · have e : ρ w = (r : k) := by
        have := congrArg ρ hw'
        rw [map_mul, map_natCast, map_intCast] at this
        rw [Rat.cast_def, eq_div_iff (Nat.cast_ne_zero.2 r.den_ne_zero), this]
      rw [hκ, hu₂ k ρ xk hρ hk, Units.val_mul, map_mul, map_units_inv, e]

theorem exists_normalised_rule : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → ∀ (g c M : ℕ), 1 ≤ g → KaRule (2 * g) c M → ∃ κ, KaRuleK g (2 * c) M κ ∧ ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g → charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ → (κ ℂ x : ℂ) = (Mx.det ^ 4 / c₀ ^ 8) ^ (2 * c) := by
  intro hL hT hinv hP hA g c M hg hR
  obtain ⟨ka, hka⟩ := GlobalTheory.KeyGalDesc.exists_kaRuleK hL.polBaseChange _ _ _ hR
  obtain ⟨a₀, ha⟩ := GlobalTheory.KeyConst.exists_const hT hinv hP hA _ c M ka (by omega) hka
  obtain ⟨kb, hkb, hv⟩ := exists_rule_sq hinv hka ha
  obtain ⟨r, hr, rfl, h₃⟩ := const_rat_unit hT hg hkb hv (WeierstrassCurve.ofJ0 ℤ)
    (by rw [WeierstrassCurve.ofJ0_Δ]; norm_num)
  obtain ⟨r', -, e, h₂⟩ := const_rat_unit hT hg hkb hv (WeierstrassCurve.ofJ1728 ℤ)
    (by rw [WeierstrassCurve.ofJ1728_Δ]; norm_num)
  obtain rfl : r' = r := Rat.cast_injective e
  obtain ⟨κ, hκ, hκv⟩ := rule_div hkb hr hv fun R K _ _ _ _ _ _ _ hM => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : R) with h | h
    · refine h₃ R K hM ?_
      rw [WeierstrassCurve.ofJ0_Δ]
      convert (h.pow 3).neg using 1
      norm_num
    · refine h₂ R K hM ?_
      rw [WeierstrassCurve.ofJ1728_Δ]
      convert (h.pow 6).neg using 1
      norm_num
  exact ⟨κ, hκ, fun x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅ => by
    rw [hκv x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅, _root_.one_mul]⟩

end GlobalTheory.KeyNormRule
end
end
end
